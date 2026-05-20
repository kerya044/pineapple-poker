'use strict';
const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const httpServer = http.createServer(app);
const io = new Server(httpServer);

app.use(express.static('public'));

// ─── Constants ────────────────────────────────────────────────────────────────
const SUITS  = ['♠','♥','♦','♣'];
const VALUES = ['2','3','4','5','6','7','8','9','10','J','Q','K','A'];
const RANK   = Object.fromEntries(VALUES.map((v,i) => [v, i+2])); // '2'→2 … 'A'→14
const HAND_NAMES = [
  'Carte haute','Paire','Double paire','Brelan',
  'Suite','Couleur','Full','Carré',
  'Quinte flush','Quinte flush royale'
];

// ─── Deck ─────────────────────────────────────────────────────────────────────
function newDeck() {
  const d = [];
  for (const s of SUITS) for (const v of VALUES) d.push({ s, v });
  for (let i = d.length-1; i > 0; i--) {
    const j = Math.random()*i|0;
    [d[i],d[j]] = [d[j],d[i]];
  }
  return d;
}

// ─── Hand evaluator ───────────────────────────────────────────────────────────
function scoreHand(hand) {
  const rs = hand.map(c => RANK[c.v]).sort((a,b) => b-a);
  const flush = new Set(hand.map(c => c.s)).size === 1;
  const cnt = {};
  for (const r of rs) cnt[r] = (cnt[r]||0)+1;
  const freqs = Object.entries(cnt).map(([r,f]) => [+r,f])
    .sort((a,b) => b[1]-a[1] || b[0]-a[0]);
  const [f0,f1] = [freqs[0]?.[1]??0, freqs[1]?.[1]??0];
  const byF = freqs.map(x => x[0]);

  let str = false, strHigh = rs[0];
  if (new Set(rs).size===5 && rs[0]-rs[4]===4) str = true;
  if (rs[0]===14&&rs[1]===5&&rs[2]===4&&rs[3]===3&&rs[4]===2) { str=true; strHigh=5; }

  if (flush && str) return strHigh===14 ? {r:9,t:[14]} : {r:8,t:[strHigh]};
  if (f0===4)       return {r:7,t:byF};
  if (f0===3&&f1===2) return {r:6,t:byF};
  if (flush)        return {r:5,t:rs};
  if (str)          return {r:4,t:[strHigh]};
  if (f0===3)       return {r:3,t:byF};
  if (f0===2&&f1===2) return {r:2,t:byF};
  if (f0===2)       return {r:1,t:byF};
  return {r:0,t:rs};
}

function cmpScore(a,b) {
  if (a.r!==b.r) return a.r-b.r;
  for (let i=0; i<Math.min(a.t.length,b.t.length); i++)
    if (a.t[i]!==b.t[i]) return a.t[i]-b.t[i];
  return 0;
}

function bestScore(hole, community) {
  const all = [...hole, ...community];
  const n = all.length;
  let best = null;
  // All C(n,5) combos
  for (let a=0;a<n-4;a++) for (let b=a+1;b<n-3;b++) for (let c=b+1;c<n-2;c++)
    for (let d=c+1;d<n-1;d++) for (let e=d+1;e<n;e++) {
      const s = scoreHand([all[a],all[b],all[c],all[d],all[e]]);
      if (!best || cmpScore(s,best)>0) best=s;
    }
  return best;
}

// ─── Room helpers ─────────────────────────────────────────────────────────────
const rooms = new Map();

function mkRoom(id) {
  return {
    id, players:[], host:null,
    phase:'waiting',       // waiting|preflop|flop|discard|turn|river|showdown
    deck:[], community:[], pot:0, curBet:0,
    dealerIdx:-1, curIdx:-1,
    toAct: new Set(),
    rBets:{},              // bets this betting round  {playerId: amount}
    sb:10, bb:20,
    winners:null,
    log:[]
  };
}

function mkPlayer(id, name) {
  return {
    id, name, chips:1000,
    hand:[], folded:false, allIn:false,
    discarded:false, disconnected:false, totalBet:0
  };
}

// ─── State serialiser (strips private data) ───────────────────────────────────
function pub(room, forId) {
  return {
    roomId:    room.id,
    phase:     room.phase,
    community: room.community,
    pot:       room.pot,
    curBet:    room.curBet,
    curIdx:    room.curIdx,
    dealerIdx: room.dealerIdx,
    sb: room.sb, bb: room.bb,
    winners:   room.winners,
    log:       room.log.slice(-5),
    players: room.players.map(p => ({
      id:    p.id,
      name:  p.name,
      chips: p.chips,
      bet:   room.rBets[p.id] || 0,
      folded: p.folded,
      allIn:  p.allIn,
      disconnected: p.disconnected,
      isHost: p.id === room.host,
      needsDiscard: room.phase==='discard' && !p.folded && !p.discarded && !p.disconnected,
      handSize: p.hand ? p.hand.length : 0,
      // Reveal hand only at showdown (non-folded) or to the player themselves
      hand: (room.phase==='showdown' && !p.folded) || p.id===forId ? p.hand : null,
      handName: room.phase==='showdown' && !p.folded && p.hand?.length>0
        ? HAND_NAMES[bestScore(p.hand, room.community)?.r ?? 0] : null
    }))
  };
}

function bcast(room) {
  for (const p of room.players) {
    if (!p.disconnected) {
      const s = io.sockets.sockets.get(p.id);
      if (s) s.emit('state', pub(room, p.id));
    }
  }
}

function addLog(room, msg) {
  room.log.push(msg);
  if (room.log.length > 20) room.log.shift();
}

// ─── Game logic ───────────────────────────────────────────────────────────────
function alive(room)  { return room.players.filter(p => !p.folded && !p.disconnected); }

function addBet(room, player, amount) {
  const actual = Math.min(amount, player.chips);
  player.chips  -= actual;
  player.totalBet += actual;
  room.rBets[player.id] = (room.rBets[player.id]||0) + actual;
  room.pot += actual;
  if (player.chips===0) player.allIn = true;
  return actual;
}

function initBetting(room, fromIdx) {
  room.rBets  = {};
  room.curBet = 0;
  room.toAct  = new Set(
    room.players.filter(p => !p.folded && !p.allIn && !p.disconnected).map(p => p.id)
  );
  setNext(room, fromIdx);
}

function setNext(room, fromIdx) {
  const n = room.players.length;
  for (let i=0; i<n; i++) {
    const idx = (fromIdx+i) % n;
    const p   = room.players[idx];
    if (!p.folded && !p.allIn && !p.disconnected && room.toAct.has(p.id)) {
      room.curIdx = idx;
      return;
    }
  }
  // Nobody left to act → advance phase
  room.curIdx = -1;
  advance(room);
}

function advance(room) {
  const al = alive(room);
  if (al.length <= 1) { showdown(room); return; }

  room.rBets  = {};
  room.curBet = 0;
  const postIdx = (room.dealerIdx+1) % room.players.length;

  switch (room.phase) {
    case 'preflop':
      room.community = [room.deck.pop(), room.deck.pop(), room.deck.pop()];
      room.phase = 'flop';
      addLog(room, `Flop : ${room.community.map(c=>c.v+c.s).join(' ')}`);
      initBetting(room, postIdx);
      break;

    case 'flop':
      // Crazy Pineapple : défausse APRÈS le flop betting
      room.phase = 'discard';
      for (const p of room.players) p.discarded = false;
      addLog(room, 'Phase de défausse — choisissez une carte à écarter');
      // Si tous les joueurs actifs ont déjà 2 cartes (cas rare), on passe directement
      if (!al.some(p => p.hand.length === 3)) { continuAfterDiscard(room); }
      break;

    case 'discard':
      continuAfterDiscard(room);
      break;

    case 'turn':
      room.community.push(room.deck.pop());
      room.phase = 'river';
      addLog(room, `River : ${room.community[4].v+room.community[4].s}`);
      initBetting(room, postIdx);
      break;

    case 'river':
      showdown(room);
      break;
  }
}

function continuAfterDiscard(room) {
  room.community.push(room.deck.pop());
  room.phase = 'turn';
  addLog(room, `Turn : ${room.community[3].v+room.community[3].s}`);
  initBetting(room, (room.dealerIdx+1) % room.players.length);
}

function showdown(room) {
  room.phase = 'showdown';
  const al = alive(room);
  if (al.length === 1) {
    al[0].chips += room.pot;
    room.winners = [{ id:al[0].id, name:al[0].name, amount:room.pot, handName:'' }];
    addLog(room, `🏆 ${al[0].name} remporte ${room.pot} jetons (seul en jeu)`);
    room.pot = 0;
    return;
  }
  for (const p of al) p._sc = bestScore(p.hand, room.community);
  al.sort((a,b) => cmpScore(b._sc, a._sc));
  const best = al[0]._sc;
  const winners = al.filter(p => cmpScore(p._sc, best)===0);
  const share = Math.floor(room.pot / winners.length);
  const extra = room.pot % winners.length;
  room.winners = winners.map((p,i) => {
    const amt = share + (i===0 ? extra : 0);
    p.chips += amt;
    return { id:p.id, name:p.name, amount:amt, handName: HAND_NAMES[p._sc.r] };
  });
  for (const w of room.winners)
    addLog(room, `🏆 ${w.name} gagne ${w.amount} jetons — ${w.handName}`);
  room.pot = 0;
}

function startRound(room) {
  room.deck      = newDeck();
  room.community = [];
  room.pot = 0; room.curBet = 0; room.winners = null;
  for (const p of room.players) {
    p.hand = [room.deck.pop(), room.deck.pop(), room.deck.pop()];
    p.folded=false; p.allIn=false; p.discarded=false; p.totalBet=0;
  }
  room.phase = 'preflop';
  room.rBets = {};

  const n    = room.players.length;
  const sbI  = (room.dealerIdx+1) % n;
  const bbI  = (room.dealerIdx+2) % n;
  addBet(room, room.players[sbI], room.sb);
  addBet(room, room.players[bbI], room.bb);
  room.curBet = room.bb;
  addLog(room, `--- Nouveau tour (dealer: ${room.players[room.dealerIdx].name}) ---`);

  // Première action au joueur après la BB
  initBetting(room, (bbI+1) % n);
  // La BB est dans toAct (elle peut relancer si personne ne l'a fait)
  room.toAct.add(room.players[bbI].id);
  // Recalculate curIdx since we modified toAct
  setNext(room, (bbI+1) % n);
}

function handleAction(room, pid, action, amount) {
  const pi = room.players.findIndex(p => p.id===pid);
  if (pi !== room.curIdx) return false;
  const p = room.players[pi];
  if (p.folded || p.allIn) return false;

  switch (action) {
    case 'fold':
      p.folded = true;
      room.toAct.delete(pid);
      addLog(room, `${p.name} se couche`);
      break;

    case 'check':
      if ((room.rBets[pid]||0) < room.curBet) return false;
      room.toAct.delete(pid);
      addLog(room, `${p.name} checke`);
      break;

    case 'call': {
      room.toAct.delete(pid);
      const need = room.curBet - (room.rBets[pid]||0);
      const actual = addBet(room, p, need);
      addLog(room, `${p.name} suit (+${actual})`);
      break;
    }

    case 'raise': {
      const minR   = room.curBet + room.bb;
      const target = Math.max(amount||minR, minR);
      const already = room.rBets[pid]||0;
      const toPut  = Math.min(target - already, p.chips);
      p.chips     -= toPut;
      p.totalBet  += toPut;
      room.rBets[pid] = already + toPut;
      room.pot    += toPut;
      if (p.chips===0) p.allIn = true;
      room.curBet = room.rBets[pid];
      // Reset toAct : tout le monde sauf le relanceur doit reagir
      room.toAct = new Set(
        room.players
          .filter(q => !q.folded && !q.allIn && !q.disconnected && q.id!==pid)
          .map(q => q.id)
      );
      addLog(room, `${p.name} relance à ${room.curBet}`);
      break;
    }

    default: return false;
  }

  if (room.toAct.size===0 || alive(room).length<=1) {
    advance(room);
  } else {
    setNext(room, (pi+1) % room.players.length);
  }
  return true;
}

// ─── Socket.IO events ─────────────────────────────────────────────────────────
io.on('connection', sock => {
  const roomOf = () => sock.data.rid ? rooms.get(sock.data.rid) : null;

  sock.on('create', ({ name }) => {
    const id = Math.random().toString(36).slice(2,8).toUpperCase();
    const room = mkRoom(id);
    rooms.set(id, room);
    room.players.push(mkPlayer(sock.id, name||'Joueur'));
    room.host = sock.id;
    sock.join(id);
    sock.data.rid = id;
    sock.emit('created', { roomId: id });
    bcast(room);
  });

  sock.on('join', ({ roomId, name }) => {
    const id = (roomId||'').toUpperCase().trim();
    const room = rooms.get(id);
    if (!room)                     { sock.emit('err','Salle introuvable'); return; }
    if (room.phase !== 'waiting')  { sock.emit('err','Partie déjà en cours'); return; }
    if (room.players.length >= 8)  { sock.emit('err','Salle pleine (max 8)'); return; }
    room.players.push(mkPlayer(sock.id, name||'Joueur'));
    sock.join(id);
    sock.data.rid = id;
    sock.emit('joined', { roomId: id });
    bcast(room);
  });

  sock.on('start', () => {
    const room = roomOf();
    if (!room || room.host!==sock.id) return;
    if (room.players.length < 2) { sock.emit('err','Il faut au moins 2 joueurs'); return; }
    room.dealerIdx = 0;
    startRound(room);
    bcast(room);
  });

  sock.on('action', ({ action, amount }) => {
    const room = roomOf();
    if (!room) return;
    if (['waiting','discard','showdown'].includes(room.phase)) return;
    handleAction(room, sock.id, action, amount);
    bcast(room);
  });

  sock.on('discard', ({ cardIndex }) => {
    const room = roomOf();
    if (!room || room.phase!=='discard') return;
    const p = room.players.find(p => p.id===sock.id);
    if (!p || p.folded || p.discarded || p.disconnected) return;
    if (cardIndex < 0 || cardIndex >= p.hand.length) return;
    const card = p.hand[cardIndex];
    p.hand.splice(cardIndex, 1);
    p.discarded = true;
    addLog(room, `${p.name} défausse ${card.v+card.s}`);
    bcast(room);
    // Tous les joueurs actifs ont défaussé ?
    const al = alive(room);
    if (al.every(q => q.discarded || q.hand.length < 3)) {
      continuAfterDiscard(room);
      bcast(room);
    }
  });

  sock.on('nextRound', () => {
    const room = roomOf();
    if (!room || room.host!==sock.id || room.phase!=='showdown') return;
    room.players = room.players.filter(p => p.chips>0 && !p.disconnected);
    if (room.players.length < 2) {
      room.phase = 'waiting';
      if (room.players.length>0) room.host = room.players[0].id;
      bcast(room); return;
    }
    room.dealerIdx = (room.dealerIdx+1) % room.players.length;
    startRound(room);
    bcast(room);
  });

  sock.on('disconnect', () => {
    const room = roomOf();
    if (!room) return;
    const p = room.players.find(p => p.id===sock.id);
    if (!p) return;
    if (room.phase === 'waiting') {
      room.players = room.players.filter(p => p.id!==sock.id);
      if (room.host===sock.id && room.players.length>0) room.host = room.players[0].id;
    } else {
      p.disconnected = true;
      p.folded = true;
      room.toAct.delete(sock.id);
      addLog(room, `${p.name} s'est déconnecté`);
      if (room.curIdx>=0 && room.players[room.curIdx]?.id===sock.id) {
        const al = alive(room);
        if (room.toAct.size===0 || al.length<=1) advance(room);
        else setNext(room, (room.curIdx+1) % room.players.length);
      }
    }
    bcast(room);
  });
});
const PORT = process.env.PORT || 3000;

app.use(express.json());
app.use(express.static('docs'));

app.get("/", (req, res) => {
  res.sendFile(__dirname + "/docs/index.html");
});
app.post("/create-game", (req, res) => {
  console.log("create-game called");

  const gameId = Math.random().toString(36).substring(2, 8);

  res.json({
    gameId: gameId,
    message: "Game created"
  });
});
httpServer.listen(PORT, () =>
  console.log(`🍍 Crazy Pineapple Poker → http://localhost:${PORT}`)
);
