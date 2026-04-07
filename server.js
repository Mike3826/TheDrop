'use strict';

const express = require('express');
const http    = require('http');
const { Server } = require('socket.io');

const app    = express();
const server = http.createServer(app);
const io     = new Server(server);

app.use(express.static('public'));

// ─── Constants ────────────────────────────────────────────────────────────────

const BUY_IN      = 10000;
const SMALL_BLIND = 50;
const BIG_BLIND   = 100;

const SUITS = ['s', 'h', 'd', 'c'];
const RANKS = ['2','3','4','5','6','7','8','9','T','J','Q','K','A'];
const RANK_VAL = Object.fromEntries(RANKS.map((r, i) => [r, i + 2]));

const HAND_NAMES = [
  'High Card', 'One Pair', 'Two Pair', 'Three of a Kind',
  'Straight',  'Flush',    'Full House', 'Four of a Kind',
  'Straight Flush', 'Royal Flush',
];

// ─── Card / Hand Utilities ────────────────────────────────────────────────────

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function combinations(arr, k) {
  if (k === 0) return [[]];
  if (arr.length < k) return [];
  const [head, ...tail] = arr;
  return [
    ...combinations(tail, k - 1).map(c => [head, ...c]),
    ...combinations(tail, k),
  ];
}

function evaluate5(cards) {
  const values = cards.map(c => RANK_VAL[c.r]).sort((a, b) => b - a);
  const suits  = cards.map(c => c.s);
  const isFlush = new Set(suits).size === 1;

  let isStraight = false, straightHigh = 0;
  if (new Set(values).size === 5 && values[0] - values[4] === 4) {
    isStraight   = true;
    straightHigh = values[0];
  } else if (values.join(',') === '14,5,4,3,2') {
    isStraight   = true;
    straightHigh = 5;
  }

  const freq = {};
  values.forEach(v => freq[v] = (freq[v] || 0) + 1);
  const groups = Object.entries(freq)
    .map(([v, c]) => ({ v: +v, c }))
    .sort((a, b) => b.c - a.c || b.v - a.v);

  if (isFlush && isStraight) return { rank: straightHigh === 14 ? 9 : 8, tb: [straightHigh] };
  if (groups[0].c === 4)     return { rank: 7, tb: [groups[0].v, groups[1].v] };
  if (groups[0].c === 3 && groups[1].c === 2) return { rank: 6, tb: [groups[0].v, groups[1].v] };
  if (isFlush)               return { rank: 5, tb: values };
  if (isStraight)            return { rank: 4, tb: [straightHigh] };
  if (groups[0].c === 3)     return { rank: 3, tb: groups.map(g => g.v) };
  if (groups[0].c === 2 && groups[1].c === 2) {
    const hi = Math.max(groups[0].v, groups[1].v);
    const lo = Math.min(groups[0].v, groups[1].v);
    return { rank: 2, tb: [hi, lo, groups[2].v] };
  }
  if (groups[0].c === 2)     return { rank: 1, tb: groups.map(g => g.v) };
  return { rank: 0, tb: values };
}

function bestHand(cards) {
  let best = null;
  for (const combo of combinations(cards, 5)) {
    const h = evaluate5(combo);
    if (!best || compareHands(h, best) > 0) best = { ...h, cards: combo };
  }
  return best;
}

function compareHands(a, b) {
  if (a.rank !== b.rank) return a.rank - b.rank;
  for (let i = 0; i < Math.max(a.tb.length, b.tb.length); i++) {
    const d = (a.tb[i] || 0) - (b.tb[i] || 0);
    if (d) return d;
  }
  return 0;
}

// ─── Game Class ───────────────────────────────────────────────────────────────

class PokerGame {
  constructor() {
    this.players            = [];
    this.phase              = 'waiting';
    this.deck               = [];
    this.community          = [];
    this.discardSectionLength = 0;
    this.pot                = 0;
    this.currentBet         = 0;
    this.lastRaise          = BIG_BLIND;
    this.dealerSeat         = -1;
    this.currentSeat        = -1;
    this.lastResult         = null;
  }

  addPlayer(id, name) {
    if (this.players.length >= 8) return false;
    this.players.push({
      id, name,
      chips: BUY_IN, hand: [],
      bet: 0, totalBet: 0,
      folded: false, allIn: false, hasActed: false,
      seat: this.players.length,
      isDealer: false, isSB: false, isBB: false,
      disconnected: false,
      mustDiscard: false,
      discardChoice: null,
    });
    return true;
  }

  removePlayer(id) {
    const idx = this.players.findIndex(p => p.id === id);
    if (idx === -1) return;
    this.players.splice(idx, 1);
    this.players.forEach((p, i) => p.seat = i);
    if (this.dealerSeat >= this.players.length)
      this.dealerSeat = Math.max(0, this.players.length - 1);
    if (this.currentSeat >= this.players.length)
      this.currentSeat = 0;
  }

  getPlayer(id) { return this.players.find(p => p.id === id); }
  inHand()      { return this.players.filter(p => !p.folded); }
  canAct()      { return this.players.filter(p => !p.folded && !p.allIn); }

  startHand() {
    if (this.players.length < 2) return false;

    this.deck       = shuffle(SUITS.flatMap(s => RANKS.map(r => ({ r, s }))));
    this.community  = [];
    this.pot        = 0;
    this.currentBet = 0;
    this.lastRaise  = BIG_BLIND;
    this.lastResult = null;

    if (this.dealerSeat < 0) this.dealerSeat = 0;
    else this.dealerSeat = (this.dealerSeat + 1) % this.players.length;

    for (const p of this.players) {
      Object.assign(p, {
        hand: [], bet: 0, totalBet: 0,
        folded: false, allIn: false, hasActed: false,
        isDealer: false, isSB: false, isBB: false,
        mustDiscard: false, discardChoice: null,
      });
    }

    const n  = this.players.length;
    const d  = this.dealerSeat;

    const sbSeat   = n === 2 ? d         : (d + 1) % n;
    const bbSeat   = n === 2 ? (d + 1) % n : (d + 2) % n;
    const firstAct = n === 2 ? d         : (d + 3) % n;  // HU: dealer/SB first; else UTG

    this.players[d].isDealer     = true;
    this.players[sbSeat].isSB    = true;
    this.players[bbSeat].isBB    = true;

    this._postBlind(sbSeat, SMALL_BLIND);
    this._postBlind(bbSeat, BIG_BLIND);
    this.currentBet = BIG_BLIND;

    for (let round = 0; round < 3; round++)
      for (let j = 0; j < n; j++)
        this.players[(d + 1 + j) % n].hand.push(this.deck.pop());

    this.discardSectionLength = 0;
    this.phase       = 'preflop';
    this.currentSeat = firstAct;
    this._skipIfNeeded();
    return true;
  }

  _postBlind(seat, amount) {
    const p      = this.players[seat];
    const actual = Math.min(amount, p.chips);
    p.chips    -= actual;
    p.bet       = actual;
    p.totalBet  = actual;
    p.hasActed  = false;
    this.pot   += actual;
    if (!p.chips) p.allIn = true;
  }

  _skipIfNeeded() {
    const p = this.players[this.currentSeat];
    if (p && (p.folded || p.allIn)) this._advance();
  }

  // ── Actions ─────────────────────────────────────────────────────────────────

  fold(id) {
    const p = this.getPlayer(id);
    if (!p || p.seat !== this.currentSeat) return false;
    p.folded = true; p.hasActed = true;
    this._afterAction(); return true;
  }

  check(id) {
    const p = this.getPlayer(id);
    if (!p || p.seat !== this.currentSeat) return false;
    if (p.bet < this.currentBet) return false;
    p.hasActed = true;
    this._afterAction(); return true;
  }

  call(id) {
    const p     = this.getPlayer(id);
    if (!p || p.seat !== this.currentSeat) return false;
    const toAdd = Math.min(this.currentBet - p.bet, p.chips);
    p.chips    -= toAdd; p.bet += toAdd; p.totalBet += toAdd;
    p.hasActed  = true;  this.pot += toAdd;
    if (!p.chips) p.allIn = true;
    this._afterAction(); return true;
  }

  discardHole(id, index) {
    if (this.phase !== 'flop_discard') return false;
    const p = this.getPlayer(id);
    if (!p || p.folded || !p.mustDiscard) return false;
    const i = parseInt(index, 10);
    if (i !== 0 && i !== 1 && i !== 2) return false;
    if (!p.hand[i]) return false;
    p.discardChoice = i;
    this._tryAdvanceAfterDiscards();
    return true;
  }

  _tryAdvanceAfterDiscards() {
    const pending = this.players.filter(
      pl => pl.mustDiscard && pl.discardChoice === null,
    );
    if (pending.length) return;
    this._finishDiscardPhase();
  }

  _finishDiscardPhase() {
    const n = this.players.length;
    const order = [];
    for (let k = 0; k < n; k++) {
      const seat = (this.dealerSeat + 1 + k) % n;
      const pl = this.players[seat];
      if (pl.mustDiscard) order.push(pl);
    }

    for (const pl of order) {
      let idx = pl.discardChoice;
      if (idx == null || idx < 0 || idx > 2 || !pl.hand[idx]) idx = 0;
      const [card] = pl.hand.splice(idx, 1);
      this.community.push(card);
    }

    this.discardSectionLength = order.length;
    for (const pl of this.players) {
      pl.mustDiscard    = false;
      pl.discardChoice  = null;
    }

    this.deck.pop();
    this.community.push(this.deck.pop());
    this.phase = 'turn';

    const inHand = this.inHand();
    if (inHand.length === 1) {
      this._awardPot(inHand[0]);
      return;
    }
    if (!this.canAct().length) {
      this._nextPhase();
      return;
    }

    let first = (this.dealerSeat + 1) % n;
    for (let k = 0; k < n; k++) {
      const pl = this.players[first];
      if (!pl.folded && !pl.allIn) {
        this.currentSeat = first;
        return;
      }
      first = (first + 1) % n;
    }
    this._nextPhase();
  }

  raise(id, totalAmount) {
    const p = this.getPlayer(id);
    if (!p || p.seat !== this.currentSeat) return false;

    const minTotal = this.currentBet + this.lastRaise;
    const maxTotal = p.chips + p.bet;
    if (totalAmount < minTotal && totalAmount < maxTotal) return false;

    const actual  = Math.min(totalAmount, maxTotal);
    const toAdd   = actual - p.bet;
    const raiseBy = actual - this.currentBet;

    p.chips    -= toAdd; p.bet = actual; p.totalBet += toAdd;
    this.pot   += toAdd;
    if (raiseBy > this.lastRaise) this.lastRaise = raiseBy;
    this.currentBet = actual;
    if (!p.chips) p.allIn = true;
    p.hasActed = true;

    for (const o of this.players)
      if (o.id !== id && !o.folded && !o.allIn) o.hasActed = false;

    this._afterAction(); return true;
  }

  // ── Internal flow ────────────────────────────────────────────────────────────

  _afterAction() {
    const inHand = this.inHand();
    if (inHand.length === 1) { this._awardPot(inHand[0]); return; }
    if (this._roundOver()) this._nextPhase();
    else this._advance();
  }

  _roundOver() {
    const active = this.canAct();
    if (!active.length) return true;
    return active.every(p => p.hasActed && p.bet === this.currentBet);
  }

  _advance() {
    const n = this.players.length;
    let next = (this.currentSeat + 1) % n;
    for (let i = 0; i < n; i++) {
      const p = this.players[next];
      if (!p.folded && !p.allIn) { this.currentSeat = next; return; }
      next = (next + 1) % n;
    }
    this._nextPhase();
  }

  _nextPhase() {
    for (const p of this.players) { p.bet = 0; p.hasActed = false; }
    this.currentBet = 0;
    this.lastRaise  = BIG_BLIND;

    if (this.phase === 'preflop') {
      this.deck.pop();
      this.community.push(this.deck.pop(), this.deck.pop(), this.deck.pop());
      this.phase = 'flop';
    } else if (this.phase === 'flop') {
      const alive = this.inHand();
      if (alive.length <= 1) {
        if (alive.length === 1) this._awardPot(alive[0]);
        return;
      }
      this.phase = 'flop_discard';
      for (const pl of this.players) {
        pl.mustDiscard   = !pl.folded && pl.hand.length === 3;
        pl.discardChoice = null;
      }
      this.currentSeat = -1;
      return;
    } else if (this.phase === 'flop_discard') {
      return;
    } else if (this.phase === 'turn') {
      this.deck.pop();
      this.community.push(this.deck.pop());
      this.phase = 'river';
    } else if (this.phase === 'river') {
      this._showdown();
      return;
    }

    const inHand = this.inHand();
    if (inHand.length === 1) { this._awardPot(inHand[0]); return; }
    if (!this.canAct().length) { this._nextPhase(); return; }  // run out the board

    const n = this.players.length;
    let first = (this.dealerSeat + 1) % n;
    for (let i = 0; i < n; i++) {
      const p = this.players[first];
      if (!p.folded && !p.allIn) { this.currentSeat = first; return; }
      first = (first + 1) % n;
    }
    this._nextPhase();
  }

  _showdown() {
    this.phase = 'showdown';
    const inHand = this.inHand();
    if (inHand.length === 1) { this._awardPot(inHand[0]); return; }
    const results = inHand.map(p => ({
      player: p,
      best: bestHand([...p.hand, ...this.community]),
    }));
    this._awardSidePots(results);
  }

  _awardPot(winner) {
    winner.chips  += this.pot;
    this.phase     = 'showdown';
    this.lastResult = {
      winners: [{ id: winner.id, name: winner.name, hand: winner.hand, won: this.pot }],
      pot: this.pot, foldWin: true, winnerNames: winner.name, handName: '',
    };
  }

  _awardSidePots(results) {
    const contributors = this.players.filter(p => p.totalBet > 0);
    const levels = [...new Set(contributors.map(p => p.totalBet))].sort((a, b) => a - b);
    const pots = [];
    let prev = 0;

    for (const lvl of levels) {
      let amt = 0;
      for (const p of contributors) amt += Math.min(p.totalBet, lvl) - prev;
      const eligible = contributors.filter(p => !p.folded && p.totalBet >= lvl);
      if (amt > 0 && eligible.length) pots.push({ amount: amt, eligible });
      prev = lvl;
    }

    const winMap = new Map();
    for (const pot of pots) {
      const contenders = pot.eligible
        .map(ep => results.find(r => r.player.id === ep.id))
        .filter(Boolean);
      if (!contenders.length) continue;

      let bestH = null, winners = [];
      for (const c of contenders) {
        if (!bestH || compareHands(c.best, bestH) > 0) { bestH = c.best; winners = [c]; }
        else if (compareHands(c.best, bestH) === 0) winners.push(c);
      }

      const share = Math.floor(pot.amount / winners.length);
      const rem   = pot.amount - share * winners.length;

      winners.forEach((w, i) => {
        const won = share + (i === 0 ? rem : 0);
        w.player.chips += won;
        const ex = winMap.get(w.player.id);
        if (ex) ex.won += won;
        else winMap.set(w.player.id, {
          id: w.player.id, name: w.player.name,
          hand: w.player.hand, best: w.best,
          handName: HAND_NAMES[w.best.rank], won,
        });
      });
    }

    const winList = [...winMap.values()];
    this.lastResult = {
      winners: winList, pot: this.pot, foldWin: false,
      winnerNames: winList.map(w => w.name).join(', '),
      handName: winList[0]?.handName || '',
    };
  }

  // ── State snapshot ───────────────────────────────────────────────────────────

  stateFor(viewerId) {
    const viewer = this.getPlayer(viewerId);
    const inHandNow = this.inHand().length;
    const expectedDiscards =
      this.phase === 'flop_discard' ? inHandNow : this.discardSectionLength;
    return {
      phase: this.phase,
      pot: this.pot,
      community: this.community,
      boardLayout: {
        flopLen: 3,
        discardLen: this.discardSectionLength,
        expectedDiscards,
      },
      currentBet: this.currentBet,
      currentSeat: this.currentSeat,
      dealerSeat: this.dealerSeat,
      lastResult: this.lastResult,
      players: this.players.map(p => ({
        id: p.id,
        name: p.name,
        chips: p.chips,
        bet: p.bet,
        folded: p.folded,
        allIn: p.allIn,
        seat: p.seat,
        isDealer: p.isDealer,
        isSB: p.isSB,
        isBB: p.isBB,
        isCurrentPlayer: p.seat === this.currentSeat,
        mustDiscard: !!p.mustDiscard,
        discardSubmitted: p.discardChoice !== null,
        hand:
          (viewer && p.id === viewer.id) ||
          (this.phase === 'showdown' && !p.folded)
            ? p.hand
            : p.hand.map(() => null),
      })),
      myId: viewerId,
      mySeat: viewer?.seat ?? -1,
      needsDiscard: !!(
        viewer &&
        viewer.mustDiscard &&
        viewer.discardChoice === null
      ),
      canAct: !!(
        viewer &&
        viewer.seat === this.currentSeat &&
        !['waiting', 'showdown', 'flop_discard'].includes(this.phase) &&
        !viewer.folded &&
        !viewer.allIn
      ),
      callAmount: viewer
        ? Math.min(
            Math.max(this.currentBet - (viewer.bet || 0), 0),
            viewer.chips,
          )
        : 0,
      minRaise: this.currentBet + this.lastRaise,
    };
  }
}

// ─── Server ───────────────────────────────────────────────────────────────────

const game = new PokerGame();

function broadcast() {
  for (const p of game.players) {
    const s = io.sockets.sockets.get(p.id);
    if (s) s.emit('gameState', game.stateFor(p.id));
  }
}

io.on('connection', socket => {

  socket.on('join', ({ name } = {}) => {
    if (game.phase !== 'waiting') { socket.emit('err', 'Game in progress. Please wait for the next hand.'); return; }
    if (game.players.length >= 8) { socket.emit('err', 'Room is full (8 players max).'); return; }
    const n = (name || '').trim().slice(0, 20);
    if (!n) { socket.emit('err', 'Please enter a valid name.'); return; }
    game.addPlayer(socket.id, n);
    socket.emit('joined');
    io.emit('msg', `${n} joined the table.`);
    broadcast();
  });

  socket.on('start', () => {
    if (game.phase !== 'waiting') return;
    if (!game.getPlayer(socket.id)) return;
    if (game.players.length < 2) { socket.emit('err', 'Need at least 2 players to start.'); return; }
    game.startHand();
    io.emit('msg', 'Hand started! Good luck everyone!');
    broadcast();
  });

  socket.on('fold', () => {
    const p = game.getPlayer(socket.id);
    if (game.fold(socket.id)) { io.emit('msg', `${p?.name} folds.`); broadcast(); }
  });

  socket.on('check', () => {
    const p = game.getPlayer(socket.id);
    if (game.check(socket.id)) { io.emit('msg', `${p?.name} checks.`); broadcast(); }
  });

  socket.on('call', () => {
    const p = game.getPlayer(socket.id);
    if (game.call(socket.id)) { io.emit('msg', `${p?.name} calls.`); broadcast(); }
  });

  socket.on('raise', ({ amount } = {}) => {
    const p   = game.getPlayer(socket.id);
    const amt = parseInt(amount, 10);
    if (!isNaN(amt) && game.raise(socket.id, amt)) {
      io.emit('msg', `${p?.name} raises to ${amt.toLocaleString()}.`);
      broadcast();
    }
  });

  socket.on('discard', ({ index } = {}) => {
    const wasDiscard = game.phase === 'flop_discard';
    if (game.discardHole(socket.id, index)) {
      if (wasDiscard && game.phase !== 'flop_discard') {
        io.emit(
          'msg',
          'Discarded hole cards are revealed — turn is on the board.',
        );
      }
      broadcast();
    }
  });

  socket.on('nextHand', () => {
    if (game.phase !== 'showdown') return;
    if (!game.getPlayer(socket.id)) return;

    // Remove disconnected players; auto-rebuy broke players
    game.players = game.players.filter(p => !p.disconnected);
    for (const p of game.players) {
      if (p.chips <= 0) { p.chips = BUY_IN; io.emit('msg', `${p.name} rebuys for ${BUY_IN.toLocaleString()} chips.`); }
    }
    game.players.forEach((p, i) => p.seat = i);

    if (game.players.length < 2) {
      game.phase      = 'waiting';
      game.dealerSeat = -1;
      io.emit('msg', 'Not enough players. Waiting for more to join...');
    } else {
      game.startHand();
      io.emit('msg', 'Next hand!');
    }
    broadcast();
  });

  socket.on('disconnect', () => {
    const p = game.getPlayer(socket.id);
    if (!p) return;
    const name = p.name;

    if (game.phase === 'waiting' || game.phase === 'showdown') {
      game.removePlayer(socket.id);
    } else if (game.phase === 'flop_discard' && p.mustDiscard && p.discardChoice === null) {
      p.disconnected = true;
      p.discardChoice = Math.floor(Math.random() * Math.max(1, p.hand.length));
      const wasD = game.phase === 'flop_discard';
      game._tryAdvanceAfterDiscards();
      if (wasD && game.phase !== 'flop_discard') {
        io.emit(
          'msg',
          'Discarded hole cards are revealed — turn is on the board.',
        );
      }
    } else {
      p.disconnected = true;
      if (!p.folded && !p.allIn) {
        if (game.players[game.currentSeat]?.id === socket.id) {
          p.folded = true;
          p.hasActed = true;
          game._afterAction();
        } else {
          p.folded = true;
          const ih = game.inHand();
          if (ih.length === 1) game._awardPot(ih[0]);
        }
      }
    }

    io.emit('msg', `${name} left the table.`);
    broadcast();
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Poker server running → http://localhost:${PORT}`);
});
