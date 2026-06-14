const express = require('express');
const http = require('http');
const socketIO = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = socketIO(server);

app.use(express.static('public'));

// ========== CONSTANTES ==========
const MAP_MAX = 5000;
const MAP_MIN = 2000;
const TICK_RATE = 20;
const TICK_INTERVAL = 100 / TICK_RATE;
const MIN_SEGMENTS = 3;
const BOT_COUNT = 0;          // Sem bots normais (apenas players)
const MIN_SPAWN_DISTANCE = 250;
const PICKUP_RADIUS = 22;

const colors = [
  '#ff4d4d','#4dff4d','#4da3ff','#ffd84d','#ff4dff',
  '#4dffff','#ff9d4d','#ffffff','#b84dff','#ff4da6'
];

const FOOD_LIMITS = {
  green: 500, yellow: 180, pink: 120, red: 220,
  white: 80, rgb: 30, turbo: 30, magnet: 30, corpse: 9999
};

// ========== ESTADO GLOBAL ==========
let players = new Map();        // id -> player object
let foods = [];
let worldSize = MAP_MAX;
let currentEvent = null;
let eventCount = 0;
let nextEventAt = Date.now() + 300000;

// Eventos visuais (enviados ao cliente)
let floodWaterLevel = 0;
let stormFlashAlpha = 0;
let spaceFlashAlpha = 0;
let spaceStars = [];
let stormParticles = [];

let spawnTimers = {
  green: 0, yellow: 0, pink: 0, red: 0,
  white: 0, rgb: 0, turbo: 0, magnet: 0
};

// ========== FUNÇÕES AUXILIARES ==========
function uid() {
  return Math.random().toString(36).substr(2, 9);
}

function rand(min, max) {
  return min + Math.random() * (max - min);
}

function clamp(v, min, max) {
  return Math.max(min, Math.min(max, v));
}

function lerp(a, b, t) {
  return a + (b - a) * t;
}

function randomColor() {
  return colors[Math.floor(Math.random() * colors.length)];
}

function getWorldRect() {
  const size = clamp(worldSize, MAP_MIN, MAP_MAX);
  const pad = (MAP_MAX - size) / 2;
  return { minX: pad, minY: pad, maxX: pad + size, maxY: pad + size, size };
}

function randomSpawnPosition() {
  const w = getWorldRect();
  const margin = 120;
  return {
    x: rand(w.minX + margin, w.maxX - margin),
    y: rand(w.minY + margin, w.maxY - margin)
  };
}

function isPositionSafe(x, y, ignoreId = null) {
  for (let [id, p] of players) {
    if (ignoreId === id) continue;
    if (!p.alive) continue;
    for (let seg of p.segments) {
      if (Math.hypot(seg.x - x, seg.y - y) < MIN_SPAWN_DISTANCE) return false;
    }
  }
  return true;
}

function findSafeSpawn(ignoreId = null) {
  for (let i = 0; i < 220; i++) {
    const pos = randomSpawnPosition();
    if (isPositionSafe(pos.x, pos.y, ignoreId)) return pos;
  }
  return randomSpawnPosition();
}

// ========== CRIAÇÃO DE PLAYER ==========
function createPlayer(id, nick) {
  const pos = findSafeSpawn();
  const segments = [];
  for (let i = 0; i < MIN_SEGMENTS; i++) {
    segments.push({ x: pos.x - i * 18, y: pos.y });
  }
  return {
    id: id,
    nick: nick,
    x: pos.x,
    y: pos.y,
    angle: Math.random() * Math.PI * 2,
    color: randomColor(),
    score: 0,
    alive: true,
    segments: segments,
    nitroHeld: false,
    turboUntil: 0,
    magnetUntil: 0,
    lastInput: { x: 0, y: 0 },
    lastUpdate: Date.now()
  };
  }// ========== MOVIMENTAÇÃO E FÍSICA ==========
function moveSnake(snake, nx, ny, dt, speed) {
  snake.x += nx * speed * dt;
  snake.y += ny * speed * dt;
  const w = getWorldRect();
  snake.x = clamp(snake.x, w.minX, w.maxX);
  snake.y = clamp(snake.y, w.minY, w.maxY);
  
  if (snake.segments.length) {
    snake.segments[0].x = snake.x;
    snake.segments[0].y = snake.y;
  }
  for (let i = 1; i < snake.segments.length; i++) {
    const prev = snake.segments[i-1];
    const seg = snake.segments[i];
    const follow = 0.26;
    seg.x += (prev.x - seg.x) * follow;
    seg.y += (prev.y - seg.y) * follow;
  }
}

function getTargetSegments(score) {
  return Math.max(MIN_SEGMENTS, MIN_SEGMENTS + Math.floor(score / 10));
}

function syncSegmentsToScore(snake) {
  const target = getTargetSegments(snake.score);
  while (snake.segments.length < target) {
    const tail = snake.segments[snake.segments.length - 1];
    snake.segments.push({ x: tail.x, y: tail.y });
  }
  while (snake.segments.length > target) snake.segments.pop();
}

function changeScore(snake, delta) {
  const oldScore = snake.score;
  const nextScore = Math.max(0, oldScore + delta);
  const actualDelta = nextScore - oldScore;
  snake.score = nextScore;
  syncSegmentsToScore(snake);
  return actualDelta;
}

// ========== COLISÕES E MORTE ==========
function killSnake(snake, dropCorpse = true) {
  if (!snake.alive) return;
  snake.alive = false;
  if (dropCorpse) {
    for (let seg of snake.segments) {
      foods.push({
        id: uid(),
        kind: 'corpse',
        x: seg.x + rand(-4, 4),
        y: seg.y + rand(-4, 4),
        color: snake.color
      });
    }
  }
  // Notifica o cliente
  const socket = io.sockets.sockets.get(snake.id);
  if (socket) {
    socket.emit('dead', { score: snake.score });
  }
}

function respawnPlayer(id) {
  const snake = players.get(id);
  if (!snake) return;
  const pos = findSafeSpawn(id);
  snake.x = pos.x;
  snake.y = pos.y;
  snake.angle = Math.random() * Math.PI * 2;
  snake.color = randomColor();
  snake.score = 0;
  snake.alive = true;
  snake.nitroHeld = false;
  snake.turboUntil = 0;
  snake.magnetUntil = 0;
  snake.lastInput = { x: 0, y: 0 };
  const count = MIN_SEGMENTS;
  snake.segments = [];
  for (let i = 0; i < count; i++) {
    snake.segments.push({ x: pos.x - i * 18, y: pos.y });
  }
}

function checkCollisions() {
  const headRadius = 14;
  const toKill = new Set();
  const playersList = Array.from(players.values());
  for (let a of playersList) {
    if (!a.alive || toKill.has(a.id)) continue;
    const head = a.segments[0];
    for (let b of playersList) {
      if (a.id === b.id) continue;
      if (!b.alive) continue;
      for (let i = 1; i < b.segments.length; i++) {
        const seg = b.segments[i];
        if (Math.hypot(head.x - seg.x, head.y - seg.y) < headRadius * 2 - 2) {
          toKill.add(a.id);
          break;
        }
      }
    }
  }
  for (let id of toKill) {
    killSnake(players.get(id), true);
  }
}

// ========== COMIDAS ==========
function spawnFood(kind, count = 1, x = null, y = null, color = null) {
  for (let i = 0; i < count; i++) {
    const pos = (x === null || y === null) ? randomSpawnPosition() : { x, y };
    foods.push({
      id: uid(),
      kind,
      x: pos.x,
      y: pos.y,
      color: color || null
    });
  }
}

function spawnInitialFoods() {
  foods = [];
  spawnFood('green', 25);
  spawnFood('yellow', 12);
  spawnFood('pink', 6);
  spawnFood('red', 10);
  spawnFood('white', 4);
  spawnFood('rgb', 1);
  spawnFood('turbo', 1);
  spawnFood('magnet', 1);
}

function countFoods(kind) {
  return foods.filter(f => f.kind === kind).length;
}

function spawnFromTimer(kind, amount) {
  if (countFoods(kind) >= FOOD_LIMITS[kind]) return;
  const freeSlots = FOOD_LIMITS[kind] - countFoods(kind);
  spawnFood(kind, Math.max(0, Math.min(amount, freeSlots)));
}

function updateFoodSpawns(dt) {
  const rain = (currentEvent && currentEvent.type === 'foodRain') ? 2 : 1;
  // green
  spawnTimers.green += dt;
  if (spawnTimers.green >= 1 / rain) {
    const batches = Math.floor(spawnTimers.green / (1 / rain));
    spawnTimers.green -= batches * (1 / rain);
    spawnFromTimer('green', batches * 5 * rain);
  }
  // yellow
  spawnTimers.yellow += dt;
  if (spawnTimers.yellow >= 1 / rain) {
    const batches = Math.floor(spawnTimers.yellow / (1 / rain));
    spawnTimers.yellow -= batches * (1 / rain);
    spawnFromTimer('yellow', batches * 1 * rain);
  }
  // pink
  spawnTimers.pink += dt;
  if (spawnTimers.pink >= 5 / rain) {
    const batches = Math.floor(spawnTimers.pink / (5 / rain));
    spawnTimers.pink -= batches * (5 / rain);
    spawnFromTimer('pink', batches * 1 * rain);
  }
  // red
  spawnTimers.red += dt;
  if (spawnTimers.red >= 1 / rain) {
    const batches = Math.floor(spawnTimers.red / (1 / rain));
    spawnTimers.red -= batches * (1 / rain);
    spawnFromTimer('red', batches * 1 * rain);
  }
  // white
  spawnTimers.white += dt;
  if (spawnTimers.white >= 30 / rain) {
    const batches = Math.floor(spawnTimers.white / (30 / rain));
    spawnTimers.white -= batches * (30 / rain);
    spawnFromTimer('white', batches * 3 * rain);
  }
  // rgb
  spawnTimers.rgb += dt;
  if (spawnTimers.rgb >= 30 / rain) {
    const batches = Math.floor(spawnTimers.rgb / (30 / rain));
    spawnTimers.rgb -= batches * (30 / rain);
    spawnFromTimer('rgb', batches * 1 * rain);
  }
  // turbo
  spawnTimers.turbo += dt;
  if (spawnTimers.turbo >= 60 / rain) {
    const batches = Math.floor(spawnTimers.turbo / (60 / rain));
    spawnTimers.turbo -= batches * (60 / rain);
    spawnFromTimer('turbo', batches * 1 * rain);
  }
  // magnet
  spawnTimers.magnet += dt;
  if (spawnTimers.magnet >= 40 / rain) {
    const batches = Math.floor(spawnTimers.magnet / (40 / rain));
    spawnTimers.magnet -= batches * (40 / rain);
    spawnFromTimer('magnet', batches * 1 * rain);
  }
}

function applyFoodEffect(snake, food) {
  switch (food.kind) {
    case 'green': changeScore(snake, 1); break;
    case 'corpse': changeScore(snake, 5); break;
    case 'yellow': changeScore(snake, 3); break;
    case 'pink': changeScore(snake, 5); break;
    case 'red': changeScore(snake, -10); break;
    case 'white': changeScore(snake, Math.floor(rand(-10, 11))); break;
    case 'rgb': changeScore(snake, 20); break;
    case 'turbo': snake.turboUntil = Date.now() + 30000; break;
    case 'magnet': snake.magnetUntil = Date.now() + 40000; break;
  }
                  }function getClosestMagnetSnake(food) {
  let best = null;
  let bestDist = Infinity;
  for (let [id, snake] of players) {
    if (!snake.alive) continue;
    if (Date.now() > snake.magnetUntil) continue;
    const head = snake.segments[0];
    const d = Math.hypot(head.x - food.x, head.y - food.y);
    if (d <= 250 && d < bestDist) {
      best = snake;
      bestDist = d;
    }
  }
  return best;
}

function updateFoodInteractions(dt) {
  for (let i = foods.length-1; i >= 0; i--) {
    const food = foods[i];
    let eaten = false;
    // buraco negro (space)
    if (currentEvent && currentEvent.type === 'space' && currentEvent.holeRadius) {
      const cx = currentEvent.centerX;
      const cy = currentEvent.centerY;
      const d = Math.hypot(food.x - cx, food.y - cy);
      if (d <= currentEvent.holeRadius) {
        foods.splice(i,1);
        currentEvent.holeRadius = Math.min(900, currentEvent.holeRadius + 1);
        continue;
      }
    }
    // colisão com cobras
    for (let [id, snake] of players) {
      if (!snake.alive) continue;
      const head = snake.segments[0];
      let radius = 6;
      switch (food.kind) {
        case 'green': radius=6; break;
        case 'yellow': radius=8; break;
        case 'pink': radius=10; break;
        case 'red': radius=10; break;
        case 'white': radius=10; break;
        case 'rgb': radius=16; break;
        case 'turbo': radius=13; break;
        case 'magnet': radius=13; break;
        case 'corpse': radius=10; break;
      }
      if (Math.hypot(head.x - food.x, head.y - food.y) < PICKUP_RADIUS + radius) {
        applyFoodEffect(snake, food);
        foods.splice(i,1);
        eaten = true;
        break;
      }
    }
    if (eaten) continue;
    // atração por magnet
    const magnet = getClosestMagnetSnake(food);
    if (magnet) {
      const head = magnet.segments[0];
      const dx = head.x - food.x;
      const dy = head.y - food.y;
      const dist = Math.hypot(dx, dy);
      if (dist > 0.001) {
        const pull = Math.max(2.2, (250 - dist) / 30);
        food.x += (dx / dist) * pull;
        food.y += (dy / dist) * pull;
        food.x = clamp(food.x, 0, MAP_MAX);
        food.y = clamp(food.y, 0, MAP_MAX);
      }
    }
  }
  // vento de tempestade
  if (currentEvent && (currentEvent.type === 'storm' || currentEvent.type === 'superStorm')) {
    const wind = currentEvent.wind || { x:0, y:0 };
    const push = currentEvent.type === 'superStorm' ? 100 : 50;
    for (let food of foods) {
      food.x += wind.x * push * dt;
      food.y += wind.y * push * dt;
      food.x = clamp(food.x, 0, MAP_MAX);
      food.y = clamp(food.y, 0, MAP_MAX);
    }
  }
}

// ========== EVENTOS DO JOGO ==========
function randomCardinalWind() {
  const winds = [{x:0,y:-1},{x:0,y:1},{x:-1,y:0},{x:1,y:0}];
  return winds[Math.floor(Math.random() * winds.length)];
}

function spawnStars() {
  spaceStars = [];
  for (let i = 0; i < 240; i++) {
    spaceStars.push({
      x: Math.random() * MAP_MAX,
      y: Math.random() * MAP_MAX,
      r: rand(0.8, 2.2),
      a: rand(0.45, 1)
    });
  }
}

function startRandomEvent(now) {
  eventCount++;
  const isSuperSlot = (eventCount % 3 === 0);
  const normalEvents = ['border', 'apocalypse', 'storm', 'flood', 'foodRain'];
  const superEvents = ['superStorm', 'space'];
  let eventType;
  if (isSuperSlot) {
    eventType = Math.random() < 0.5 ? normalEvents[Math.floor(Math.random() * normalEvents.length)] : superEvents[Math.floor(Math.random() * superEvents.length)];
  } else {
    eventType = normalEvents[Math.floor(Math.random() * normalEvents.length)];
  }

  if (eventType === 'border') {
    currentEvent = { type:'border', start:now, shrinkEnd:now+60000, end:now+70000 };
    worldSize = MAP_MAX;
  } else if (eventType === 'apocalypse') {
    currentEvent = { type:'apocalypse', start:now, end:now+60000 };
    // remove wild existentes e cria 3 novos (bots selvagens)
    for (let [id, p] of players) {
      if (p.isWild) killSnake(p, true);
    }
    // criar bots selvagens (simulados como players com isWild)
    for (let i = 0; i < 3; i++) {
      const pos = findSafeSpawn();
      const wildId = 'wild_' + uid();
      const wildSnake = {
        id: wildId,
        nick: '☠️',
        isWild: true,
        x: pos.x, y: pos.y,
        angle: Math.random() * Math.PI * 2,
        color: '#1b5e20',
        score: 90,
        alive: true,
        segments: Array.from({ length: 10 }, (_,i) => ({ x: pos.x - i*18, y: pos.y })),
        nitroHeld: false,
        turboUntil: 0,
        magnetUntil: 0,
        wildExpiresAt: now + 60000,
        aiDashUntil: 0,
        aiDashCooldown: rand(0.8,2.2),
        aiStrafeDir: Math.random()<0.5?-1:1,
        wanderPhase: Math.random()*Math.PI*2,
        lastInput: { x:0, y:0 }
      };
      players.set(wildId, wildSnake);
    }
  } else if (eventType === 'storm') {
    currentEvent = { type:'storm', start:now, end:now+60000, wind:randomCardinalWind() };
    stormParticles = [];
  } else if (eventType === 'superStorm') {
    currentEvent = { type:'superStorm', start:now, end:now+60000, wind:randomCardinalWind(), flashNext:now+10000 };
    stormParticles = [];
    stormFlashAlpha = 0;
  } else if (eventType === 'flood') {
    currentEvent = { type:'flood', start:now, riseEnd:now+30000, holdEnd:now+60000, end:now+70000 };
    floodWaterLevel = 0;
  } else if (eventType === 'foodRain') {
    currentEvent = { type:'foodRain', start:now, end:now+60000 };
  } else if (eventType === 'space') {
    currentEvent = {
      type:'space',
      start:now,
      blackHoleStart:now+20000,
      blackHoleGrowEnd:now+40000,
      blackHoleHoldEnd:now+60000,
      holeRadius:50,
      centerX: MAP_MAX/2,
      centerY: MAP_MAX/2
    };
    spawnStars();
    spaceFlashAlpha = 0;
  }
}

function updateEventState(now, dt) {
  if (!currentEvent) {
    if (now >= nextEventAt) {
      startRandomEvent(now);
      nextEventAt = now + 300000;
    }
    worldSize = MAP_MAX;
    return;
  }

  const e = currentEvent;
  if (e.type === 'border') {
    if (now < e.shrinkEnd) {
      const t = clamp((now - e.start) / 60000, 0, 1);
      worldSize = lerp(MAP_MAX, MAP_MIN, t);
    } else if (now < e.end) {
      const t = clamp((now - e.shrinkEnd) / 10000, 0, 1);
      worldSize = lerp(MAP_MIN, MAP_MAX, t);
    } else {
      currentEvent = null;
      worldSize = MAP_MAX;
    }
  } else if (e.type === 'apocalypse') {
    if (now >= e.end) {
      // remove bots selvagens
      for (let [id, p] of players) {
        if (p.isWild && p.alive) killSnake(p, true);
      }
      currentEvent = null;
    }
  } else if (e.type === 'storm' || e.type === 'superStorm') {
    if (e.type === 'superStorm' && now >= e.flashNext) {
      stormFlashAlpha = 1;
      e.flashNext += 10000;
    }
    stormFlashAlpha = Math.max(0, stormFlashAlpha - dt * 1.6);
    if (now >= e.end) {
      currentEvent = null;
      stormFlashAlpha = 0;
      stormParticles = [];
    }
  } else if (e.type === 'flood') {
    if (now < e.riseEnd) {
      const t = clamp((now - e.start) / 30000, 0, 1);
      floodWaterLevel = t;
    } else if (now < e.holdEnd) {
      floodWaterLevel = 1;
    } else if (now < e.end) {
      const t = clamp((now - e.holdEnd) / 10000, 0, 1);
      floodWaterLevel = 1 - t;
    } else {
      currentEvent = null;
      floodWaterLevel = 0;
    }
  } else if (e.type === 'foodRain') {
    if (now >= e.end) currentEvent = null;
  } else if (e.type === 'space') {
    if (now >= e.blackHoleStart && now < e.blackHoleGrowEnd) {
      const t = clamp((now - e.blackHoleStart) / 20000, 0, 1);
      e.holeRadius = lerp(50, 900, t);
    } else if (now >= e.blackHoleGrowEnd && now < e.blackHoleHoldEnd) {
      e.holeRadius = 900;
    }
    if (now >= e.blackHoleHoldEnd) {
      // spawn recompensa
      const cx = MAP_MAX/2, cy = MAP_MAX/2;
      for (let i=0;i<10;i++) {
        foods.push({ id:uid(), kind:'rgb', x:cx+rand(-26,26), y:cy+rand(-26,26), color:null });
      }
      spaceFlashAlpha = 1;
      currentEvent = null;
    }
    if (spaceFlashAlpha > 0) spaceFlashAlpha = Math.max(0, spaceFlashAlpha - dt * 0.65);
  }
}

function updateStormParticles(dt) {
  if (!currentEvent || (currentEvent.type !== 'storm' && currentEvent.type !== 'superStorm')) return;
  const wind = currentEvent.wind || {x:0,y:0};
  const speed = 760;
  if (stormParticles.length === 0) {
    for (let i=0;i<140;i++) {
      stormParticles.push({
        x: Math.random() * MAP_MAX,
        y: Math.random() * MAP_MAX,
        len: rand(10,34)
      });
    }
  }
  for (let p of stormParticles) {
    p.x += wind.x * speed * dt;
    p.y += wind.y * speed * dt;
    if (wind.x !== 0) {
      if (wind.x > 0 && p.x > MAP_MAX + 40) p.x = -40;
      if (wind.x < 0 && p.x < -40) p.x = MAP_MAX + 40;
    } else {
      if (wind.y > 0 && p.y > MAP_MAX + 40) p.y = -40;
      if (wind.y < 0 && p.y < -40) p.y = MAP_MAX + 40;
    }
    p.x = clamp(p.x, -40, MAP_MAX+40);
    p.y = clamp(p.y, -40, MAP_MAX+40);
  }
}

function updateBlackHole(dt) {
  if (!currentEvent || currentEvent.type !== 'space') return;
  const e = currentEvent;
  const cx = e.centerX, cy = e.centerY;
  const radius = e.holeRadius;
  const influence = radius * 2;
  const pullSpeed = 140;
  // puxar comidas
  for (let i=foods.length-1; i>=0; i--) {
    const f = foods[i];
    const d = Math.hypot(f.x - cx, f.y - cy);
    if (d <= radius) {
      foods.splice(i,1);
      e.holeRadius = Math.min(900, e.holeRadius + 1);
      continue;
    }
    if (d <= influence && d > 0.001) {
      const nx = (cx - f.x) / d;
      const ny = (cy - f.y) / d;
      f.x += nx * pullSpeed * dt;
      f.y += ny * pullSpeed * dt;
    }
  }
  // puxar cobras
  for (let [id, snake] of players) {
    if (!snake.alive) continue;
    const head = snake.segments[0];
    const d = Math.hypot(head.x - cx, head.y - cy);
    if (d <= radius) {
      e.holeRadius = Math.min(900, e.holeRadius + snake.segments.length * 5);
      killSnake(snake, false);
      continue;
    }
    if (d <= influence && d > 0.001) {
      const nx = (cx - head.x) / d;
      const ny = (cy - head.y) / d;
      const dx = nx * pullSpeed * dt;
      const dy = ny * pullSpeed * dt;
      snake.x += dx; snake.y += dy;
      for (let seg of snake.segments) {
        seg.x += dx; seg.y += dy;
      }
    }
  }
}

// ========== LÓGICA DE IA PARA BOTS SELVAGENS ==========
function updateWildBots(dt, now) {
  for (let [id, bot] of players) {
    if (!bot.isWild) continue;
    if (!bot.alive) continue;
    if (now >= bot.wildExpiresAt) {
      killSnake(bot, true);
      continue;
    }
    // encontra alvo (player mais próximo que não seja wild)
    let target = null;
    let bestDist = Infinity;
    for (let [oid, p] of players) {
      if (p.isWild) continue;
      if (!p.alive) continue;
      const d = Math.hypot(bot.x - p.x, bot.y - p.y);
      if (d < bestDist) { bestDist = d; target = p; }
    }
    if (target) {
      const dx = target.x - bot.x;
      const dy = target.y - bot.y;
      const dist = Math.hypot(dx, dy) || 1;
      const baseAngle = Math.atan2(dy, dx);
      const orbit = Math.sin(now * 0.002 + bot.wanderPhase) * 0.6 * bot.aiStrafeDir;
      let desired = baseAngle + orbit;
      if (dist < 180) desired += (bot.aiStrafeDir * Math.PI / 3);
      bot.angle = approachAngle(bot.angle, desired, 0.09);
      if (bot.aiDashCooldown > 0) bot.aiDashCooldown -= dt;
      if (bot.aiDashCooldown <= 0 && dist < 360) {
        bot.aiDashUntil = now + 500;
        bot.aiDashCooldown = rand(1.7, 3.2);
        bot.aiStrafeDir *= -1;
      }
      const dash = now < bot.aiDashUntil;
      let speed = (dash ? 320 : 230);
      const nx = Math.cos(bot.angle);
      const ny = Math.sin(bot.angle);
      moveSnake(bot, nx, ny, dt, speed);
    } else {
      const nx = Math.cos(bot.angle);
      const ny = Math.sin(bot.angle);
      moveSnake(bot, nx, ny, dt, 180);
    }
  }
}

function approachAngle(current, target, step) {
  let diff = target - current;
  while (diff > Math.PI) diff -= Math.PI*2;
  while (diff < -Math.PI) diff += Math.PI*2;
  if (Math.abs(diff) <= step) return target;
  return current + Math.sign(diff) * step;
    }// ========== ATUALIZAÇÃO DO JOGO (TICK) ==========
let lastTick = Date.now();

function gameTick() {
  const now = Date.now();
  let dt = Math.min(0.033, (now - lastTick) / 1000);
  lastTick = now;

  // Atualiza eventos
  updateEventState(now, dt);
  updateStormParticles(dt);
  updateBlackHole(dt);

  // Atualiza jogadores (movimento baseado no input)
  for (let [id, player] of players) {
    if (!player.alive) continue;
    const input = player.lastInput;
    const len = Math.hypot(input.x, input.y);
    let nx = 0, ny = 0;
    if (len > 0.001) {
      nx = input.x / len;
      ny = input.y / len;
      player.angle = Math.atan2(ny, nx);
    }
    let speed = 190;
    if (player.turboUntil > now) speed *= 3;
    if (player.nitroHeld && player.score > 0) speed *= 2;
    // efeitos de evento
    if (currentEvent && (currentEvent.type === 'storm' || currentEvent.type === 'superStorm')) {
      const wind = currentEvent.wind || {x:0,y:0};
      const push = currentEvent.type === 'superStorm' ? 120 : 60;
      const dirX = Math.cos(player.angle);
      const dirY = Math.sin(player.angle);
      const dot = dirX * wind.x + dirY * wind.y;
      if (dot > 0.2) speed *= 2;
      else if (dot < -0.2) speed *= 0.5;
      player.x += wind.x * push * dt;
      player.y += wind.y * push * dt;
    }
    if (currentEvent && currentEvent.type === 'flood') {
      const waterLine = MAP_MAX * (1 - floodWaterLevel);
      if (player.segments[0].y >= waterLine) speed *= 0.5;
    }
    moveSnake(player, nx, ny, dt, speed);
    // perda de pontos com nitro
    if (player.nitroHeld && player.score > 0) {
      if (player.score > 0) changeScore(player, -1);
      if (player.score <= 0) player.nitroHeld = false;
    }
  }

  // Atualiza bots selvagens (IA)
  updateWildBots(dt, now);

  // Colisões
  checkCollisions();

  // Comidas
  updateFoodSpawns(dt);
  updateFoodInteractions(dt);

  // Prepara estado para envio
  const state = {
    players: Object.fromEntries(players),
    foods: foods,
    worldSize: worldSize,
    currentEvent: currentEvent,
    floodWaterLevel: floodWaterLevel,
    stormFlashAlpha: stormFlashAlpha,
    spaceFlashAlpha: spaceFlashAlpha,
    spaceStars: spaceStars,
    stormParticles: stormParticles
  };
  io.emit('state', state);
}

// ========== SOCKET.IO ==========
io.on('connection', (socket) => {
  console.log('Jogador conectado:', socket.id);

  socket.on('join', (data) => {
    const nick = data.nick || 'Jogador';
    if (players.has(socket.id)) {
      // já existe? reseta
      respawnPlayer(socket.id);
      players.get(socket.id).nick = nick;
    } else {
      const newPlayer = createPlayer(socket.id, nick);
      players.set(socket.id, newPlayer);
    }
    socket.emit('joined', { id: socket.id, nick: nick });
    console.log(`${nick} entrou no jogo`);
  });

  socket.on('input', (data) => {
    const player = players.get(socket.id);
    if (player && player.alive) {
      player.lastInput = { x: data.x || 0, y: data.y || 0 };
      player.nitroHeld = data.nitro || false;
    }
  });

  socket.on('restart', () => {
    const player = players.get(socket.id);
    if (player && !player.alive) {
      respawnPlayer(socket.id);
    }
  });

  socket.on('disconnect', () => {
    console.log('Jogador desconectado:', socket.id);
    players.delete(socket.id);
  });
});

// Inicialização
spawnInitialFoods();

// Loop do jogo
setInterval(gameTick, TICK_INTERVAL);

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Servidor rodando em http://localhost:${PORT}`);
});
