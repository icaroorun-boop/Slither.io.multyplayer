const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');
const { randomUUID } = require('crypto');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

const PORT = process.env.PORT || 3000;

app.use(express.static(path.join(__dirname, 'public')));
app.get('/health', (_, res) => res.status(200).send('ok'));

const MAP_MAX = 5000;
const MAP_MIN = 2000;
const MIN_SEGMENTS = 3;
const MIN_SPAWN_DISTANCE = 250;
const PICKUP_RADIUS = 22;
const BOT_COUNT = 0;
const TICK_MS = 50;

const colors = [
  '#ff4d4d', '#4dff4d', '#4da3ff', '#ffd84d', '#ff4dff',
  '#4dffff', '#ff9d4d', '#ffffff', '#b84dff', '#ff4da6'
];

const FOOD_LIMITS = {
  green: 500, yellow: 180, pink: 120, red: 220,
  white: 80, rgb: 30, turbo: 30, magnet: 30, corpse: 9999
};

const state = {
  worldSize: MAP_MAX,
  currentEvent: null,
  nextEventAt: Date.now() + 300000,
  eventCount: 0,
  foods: [],
  players: new Map(),
  wildBots: [],
  foodTimers: {
    green: 0, yellow: 0, pink: 0, red: 0,
    white: 0, rgb: 0, turbo: 0, magnet: 0
  },
  stormFlashAlpha: 0,
  spaceFlashAlpha: 0,
  floodWaterLevel: 0,
  spaceStars: []
};

function uid() {
  return randomUUID();
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

function normalizeAngle(a) {
  while (a > Math.PI) a -= Math.PI * 2;
  while (a < -Math.PI) a += Math.PI * 2;
  return a;
}

function approachAngle(current, target, step) {
  const diff = normalizeAngle(target - current);
  if (Math.abs(diff) <= step) return target;
  return current + Math.sign(diff) * step;
}

function getWorldRect() {
  const size = clamp(state.worldSize, MAP_MIN, MAP_MAX);
  const pad = (MAP_MAX - size) / 2;
  return { minX: pad, minY: pad, maxX: pad + size, maxY: pad + size, size };
}

function randomSpawnPosition() {
  const size = clamp(state.worldSize, MAP_MIN, MAP_MAX);
  const pad = (MAP_MAX - size) / 2;
  const margin = 120;
  return {
    x: rand(pad + margin, pad + size - margin),
    y: rand(pad + margin, pad + size - margin)
  };
}

function countAliveSegmentsAround(pos, snakeList) {
  for (const s of snakeList) {
    if (!s.alive) continue;
    for (const seg of s.segments) {
      if (Math.hypot(seg.x - pos.x, seg.y - pos.y) < MIN_SPAWN_DISTANCE) return false;
    }
  }
  return true;
}

function findSafeSpawn(list) {
  for (let i = 0; i < 220; i++) {
    const pos = randomSpawnPosition();
    if (countAliveSegmentsAround(pos, list)) return pos;
  }
  return randomSpawnPosition();
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

function createSnakeBase({
  x, y, color, nick, isPlayer = false, isWild = false,
  score = 0, segmentsCount = 3, socketId = null
}) {
  const segs = [];
  for (let i = 0; i < segmentsCount; i++) segs.push({ x: x - i * 18, y });
  return {
    id: uid(),
    socketId,
    nick,
    isPlayer,
    isWild,
    x, y,
    angle: Math.random() * Math.PI * 2,
    color,
    score,
    alive: true,
    respawnAt: 0,
    turboUntil: 0,
    magnetUntil: 0,
    nitroHeld: false,
    nitroDrainAccum: 0,
    borderDrainAccum: 0,
    wanderTimer: 0,
    wanderTurn: 0,
    wanderPhase: Math.random() * Math.PI * 2,
    aiDashUntil: 0,
    aiDashCooldown: rand(1.5, 3.5),
    aiStrafeDir: Math.random() < 0.5 ? -1 : 1,
    wildExpiresAt: 0,
    segments: segs,
    input: { x: 0, y: 0, nitro: false }
  };
}

function rebuildBody(snake) {
  const x = snake.x, y = snake.y;
  const count = getTargetSegments(snake.score);
  snake.segments = [];
  for (let i = 0; i < count; i++) snake.segments.push({ x: x - i * 18, y });
}

function createPlayer(socketId, nick) {
  const pos = findSafeSpawn([...state.players.values(), ...state.wildBots]);
  return createSnakeBase({
    x: pos.x,
    y: pos.y,
    color: randomColor(),
    nick,
    isPlayer: true,
    score: 0,
    segmentsCount: 3,
    socketId
  });
}

function createWildBot(now) {
  const pos = findSafeSpawn([...state.players.values(), ...state.wildBots]);
  const bot = createSnakeBase({
    x: pos.x,
    y: pos.y,
    color: '#1b5e20',
    nick: '☠️',
    isWild: true,
    score: 90,
    segmentsCount: 10
  });
  bot.wildExpiresAt = now + 60000;
  bot.aiDashCooldown = rand(0.8, 2.2);
  bot.aiStrafeDir = Math.random() < 0.5 ? -1 : 1;
  return bot;
}

function countFoods(kind) {
  let count = 0;
  for (const f of state.foods) if (f.kind === kind) count++;
  return count;
}

function spawnFood(kind, count = 1, x = null, y = null, color = null) {
  for (let i = 0; i < count; i++) {
    if (countFoods(kind) >= FOOD_LIMITS[kind]) return;
    const pos = (x === null || y === null) ? randomSpawnPosition() : { x, y };
    state.foods.push({ id: uid(), kind, x: pos.x, y: pos.y, color: color || null });
  }
}

function spawnInitialFoods() {
  spawnFood('green', 25);
  spawnFood('yellow', 12);
  spawnFood('pink', 6);
  spawnFood('red', 10);
  spawnFood('white', 4);
  spawnFood('rgb', 1);
  spawnFood('turbo', 1);
  spawnFood('magnet', 1);
}

function spawnCorpseFoods(snake) {
  for (const seg of snake.segments) {
    state.foods.push({
      id: uid(),
      kind: 'corpse',
      x: seg.x + rand(-4, 4),
      y: seg.y + rand(-4, 4),
      color: snake.color
    });
  }
}

function dropGreenFoodBehind(snake, amount) {
  const tail = snake.segments[snake.segments.length - 1];
  const backAngle = snake.angle + Math.PI;
  for (let i = 0; i < amount; i++) {
    state.foods.push({
      id: uid(),
      kind: 'green',
      x: clamp(tail.x + Math.cos(backAngle) * rand(8, 20) + rand(-8, 8), 0, MAP_MAX),
      y: clamp(tail.y + Math.sin(backAngle) * rand(8, 20) + rand(-8, 8), 0, MAP_MAX),
      color: null
    });
  }
}

function changeScore(snake, delta, dropTrail = false) {
  const oldScore = snake.score;
  const nextScore = Math.max(0, oldScore + delta);
  const actualDelta = nextScore - oldScore;
  snake.score = nextScore;
  syncSegmentsToScore(snake);
  if (dropTrail && actualDelta < 0) dropGreenFoodBehind(snake, Math.abs(actualDelta));
  return actualDelta;
}

function applyFoodEffect(snake, food) {
  switch (food.kind) {
    case 'green':
      changeScore(snake, +1, false);
      break;
    case 'corpse':
      changeScore(snake, +5, false);
      break;
    case 'yellow':
      changeScore(snake, +3, false);
      break;
    case 'pink':
      changeScore(snake, +5, false);
      break;
    case 'red':
      changeScore(snake, -10, false);
      break;
    case 'white':
      changeScore(snake, Math.floor(rand(-10, 11)), false);
      break;
    case 'rgb':
      changeScore(snake, +20, false);
      break;
    case 'turbo':
      snake.turboUntil = Math.max(snake.turboUntil, Date.now() + 30000);
      break;
    case 'magnet':
      snake.magnetUntil = Math.max(snake.magnetUntil, Date.now() + 40000);
      break;
  }
}

function killSnake(snake, dropCorpse = true) {
  if (!snake.alive) return;
  snake.alive = false;
  snake.respawnAt = snake.isWild ? Infinity : Date.now() + 1500;
  if (dropCorpse) spawnCorpseFoods(snake);

  if (snake.isPlayer && snake.socketId) {
    io.to(snake.socketId).emit('dead', { score: snake.score });
  }
}

function respawnSnake(snake) {
  const pos = findSafeSpawn([...state.players.values(), ...state.wildBots].filter(s => s !== snake));
  snake.x = pos.x;
  snake.y = pos.y;
  snake.angle = Math.random() * Math.PI * 2;
  snake.color = snake.isWild ? '#1b5e20' : randomColor();
  snake.score = snake.isWild ? 90 : 0;
  snake.alive = true;
  snake.respawnAt = 0;
  snake.turboUntil = 0;
  snake.magnetUntil = 0;
  snake.nitroHeld = false;
  snake.nitroDrainAccum = 0;
  snake.borderDrainAccum = 0;
  snake.aiDashUntil = 0;
  snake.aiDashCooldown = rand(1.5, 3.5);
  snake.wanderTimer = 0;
  snake.wanderTurn = 0;
  snake.wanderPhase = Math.random() * Math.PI * 2;
  if (snake.isWild) {
    snake.segments = Array.from({ length: 10 }, (_, i) => ({ x: pos.x - i * 18, y: pos.y }));
    snake.wildExpiresAt = Date.now() + 60000;
  } else {
    rebuildBody(snake);
  }
}

function randomCardinalWind() {
  const winds = [{ x: 0, y: -1 }, { x: 0, y: 1 }, { x: -1, y: 0 }, { x: 1, y: 0 }];
  return winds[Math.floor(Math.random() * winds.length)];
}

function startRandomEvent(now) {
  state.eventCount += 1;
  const isSuperSlot = (state.eventCount % 3 === 0);
  const normalEvents = ['border', 'apocalypse', 'storm', 'flood', 'foodRain'];
  const superEvents = ['superStorm', 'space'];

  let eventType;
  if (isSuperSlot) {
    eventType = (Math.random() < 0.5)
      ? normalEvents[Math.floor(Math.random() * normalEvents.length)]
      : superEvents[Math.floor(Math.random() * superEvents.length)];
  } else {
    eventType = normalEvents[Math.floor(Math.random() * normalEvents.length)];
  }

  if (eventType === 'border') {
    state.currentEvent = { type: 'border', start: now, shrinkEnd: now + 60000, end: now + 70000 };
    state.worldSize = MAP_MAX;
    return;
  }

  if (eventType === 'apocalypse') {
    state.currentEvent = { type: 'apocalypse', start: now, end: now + 60000 };
    state.wildBots = [createWildBot(now), createWildBot(now), createWildBot(now)];
    return;
  }

  if (eventType === 'storm') {
    state.currentEvent = { type: 'storm', start: now, end: now + 60000, wind: randomCardinalWind() };
    return;
  }

  if (eventType === 'superStorm') {
    state.currentEvent = { type: 'superStorm', start: now, end: now + 60000, wind: randomCardinalWind(), flashNext: now + 10000 };
    return;
  }

  if (eventType === 'flood') {
    state.currentEvent = { type: 'flood', start: now, riseEnd: now + 30000, holdEnd: now + 60000, end: now + 70000 };
    return;
  }

  if (eventType === 'foodRain') {
    state.currentEvent = { type: 'foodRain', start: now, end: now + 60000 };
    return;
  }

  if (eventType === 'space') {
    state.currentEvent = {
      type: 'space',
      start: now,
      blackHoleStart: now + 20000,
      blackHoleGrowEnd: now + 40000,
      blackHoleHoldEnd: now + 60000,
      holeRadius: 50,
      holeMax: 900,
      centerX: MAP_MAX / 2,
      centerY: MAP_MAX / 2
    };
  }
}

function clearEvent() {
  state.currentEvent = null;
  state.worldSize = MAP_MAX;
  state.wildBots = [];
  state.floodWaterLevel = 0;
  state.stormFlashAlpha = 0;
  state.spaceFlashAlpha = 0;
  }function updateEvent(now, dt) {
  if (!state.currentEvent) {
    if (now >= state.nextEventAt) {
      startRandomEvent(now);
      state.nextEventAt = now + 300000;
    }
    state.worldSize = MAP_MAX;
    return;
  }

  const ev = state.currentEvent;

  if (ev.type === 'border') {
    if (now < ev.shrinkEnd) {
      const t = clamp((now - ev.start) / 60000, 0, 1);
      state.worldSize = lerp(MAP_MAX, MAP_MIN, t);
    } else if (now < ev.end) {
      const t = clamp((now - ev.shrinkEnd) / 10000, 0, 1);
      state.worldSize = lerp(MAP_MIN, MAP_MAX, t);
    } else {
      clearEvent();
    }
    return;
  }

  if (ev.type === 'apocalypse') {
    if (now >= ev.end) clearEvent();
    return;
  }

  if (ev.type === 'storm' || ev.type === 'superStorm') {
    if (now >= ev.end) clearEvent();
    return;
  }

  if (ev.type === 'flood') {
    if (now >= ev.end) clearEvent();
    return;
  }

  if (ev.type === 'foodRain') {
    if (now >= ev.end) clearEvent();
    return;
  }

  if (ev.type === 'space') {
    if (now >= ev.blackHoleStart && now < ev.blackHoleGrowEnd) {
      const t = (now - ev.blackHoleStart) / 20000;
      ev.holeRadius = lerp(50, 900, clamp(t, 0, 1));
    } else if (now >= ev.blackHoleGrowEnd && now < ev.blackHoleHoldEnd) {
      ev.holeRadius = 900;
    } else if (now >= ev.blackHoleHoldEnd) {
      spawnFood('rgb', 10, MAP_MAX / 2, MAP_MAX / 2);
      clearEvent();
    }
  }
}

function isInFlood(snake) {
  if (!state.currentEvent || state.currentEvent.type !== 'flood') return false;
  const waterLine = MAP_MAX * (1 - clamp((Date.now() - state.currentEvent.start) / 30000, 0, 1));
  return snake.segments[0].y >= waterLine;
}

function getWindVector() {
  if (!state.currentEvent) return { x: 0, y: 0 };
  if (state.currentEvent.type === 'storm' || state.currentEvent.type === 'superStorm') {
    return state.currentEvent.wind || { x: 0, y: 0 };
  }
  return { x: 0, y: 0 };
}

function getStormPush(kind) {
  if (!state.currentEvent) return 0;
  if (state.currentEvent.type === 'superStorm') return kind === 'food' ? 100 : 120;
  if (state.currentEvent.type === 'storm') return kind === 'food' ? 50 : 60;
  return 0;
}

function getNearestPlayerTarget(bot) {
  let best = null;
  let bestDist = Infinity;
  for (const s of state.players.values()) {
    if (!s.alive) continue;
    const d = Math.hypot(bot.x - s.x, bot.y - s.y);
    if (d < bestDist) {
      bestDist = d;
      best = s;
    }
  }
  return best;
}

function getClosestMagnetSnake(food) {
  let best = null;
  let bestDist = Infinity;
  for (const s of [...state.players.values(), ...state.wildBots]) {
    if (!s.alive) continue;
    if (Date.now() > s.magnetUntil) continue;
    const head = s.segments[0];
    const d = Math.hypot(head.x - food.x, head.y - food.y);
    if (d <= 250 && d < bestDist) {
      best = s;
      bestDist = d;
    }
  }
  return best;
}

function countFoodsNow(kind) {
  let count = 0;
  for (const f of state.foods) if (f.kind === kind) count++;
  return count;
}

function spawnFromTimer(kind, amount) {
  if (countFoodsNow(kind) >= FOOD_LIMITS[kind]) return;
  const freeSlots = FOOD_LIMITS[kind] - countFoodsNow(kind);
  spawnFood(kind, Math.max(0, Math.min(amount, freeSlots)));
}

function updateFoodSpawns(dt) {
  const rain = state.currentEvent && state.currentEvent.type === 'foodRain' ? 2 : 1;

  state.foodTimers.green += dt;
  if (state.foodTimers.green >= 1 / rain) {
    const batches = Math.floor(state.foodTimers.green / (1 / rain));
    state.foodTimers.green -= batches * (1 / rain);
    spawnFromTimer('green', batches * 5 * rain);
  }

  state.foodTimers.yellow += dt;
  if (state.foodTimers.yellow >= 1 / rain) {
    const batches = Math.floor(state.foodTimers.yellow / (1 / rain));
    state.foodTimers.yellow -= batches * (1 / rain);
    spawnFromTimer('yellow', batches * 1 * rain);
  }

  state.foodTimers.pink += dt;
  if (state.foodTimers.pink >= 5 / rain) {
    const batches = Math.floor(state.foodTimers.pink / (5 / rain));
    state.foodTimers.pink -= batches * (5 / rain);
    spawnFromTimer('pink', batches * 1 * rain);
  }

  state.foodTimers.red += dt;
  if (state.foodTimers.red >= 1 / rain) {
    const batches = Math.floor(state.foodTimers.red / (1 / rain));
    state.foodTimers.red -= batches * (1 / rain);
    spawnFromTimer('red', batches * 1 * rain);
  }

  state.foodTimers.white += dt;
  if (state.foodTimers.white >= 30 / rain) {
    const batches = Math.floor(state.foodTimers.white / (30 / rain));
    state.foodTimers.white -= batches * (30 / rain);
    spawnFromTimer('white', batches * 3 * rain);
  }

  state.foodTimers.rgb += dt;
  if (state.foodTimers.rgb >= 30 / rain) {
    const batches = Math.floor(state.foodTimers.rgb / (30 / rain));
    state.foodTimers.rgb -= batches * (30 / rain);
    spawnFromTimer('rgb', batches * 1 * rain);
  }

  state.foodTimers.turbo += dt;
  if (state.foodTimers.turbo >= 60 / rain) {
    const batches = Math.floor(state.foodTimers.turbo / (60 / rain));
    state.foodTimers.turbo -= batches * (60 / rain);
    spawnFromTimer('turbo', batches * 1 * rain);
  }

  state.foodTimers.magnet += dt;
  if (state.foodTimers.magnet >= 40 / rain) {
    const batches = Math.floor(state.foodTimers.magnet / (40 / rain));
    state.foodTimers.magnet -= batches * (40 / rain);
    spawnFromTimer('magnet', batches * 1 * rain);
  }
}

function moveSnakeByInput(snake, nx, ny, dt, speed) {
  snake.x += nx * speed * dt;
  snake.y += ny * speed * dt;

  const w = getWorldRect();
  snake.x = clamp(snake.x, w.minX, w.maxX);
  snake.y = clamp(snake.y, w.minY, w.maxY);

  snake.segments[0].x = snake.x;
  snake.segments[0].y = snake.y;

  for (let i = 1; i < snake.segments.length; i++) {
    const prev = snake.segments[i - 1];
    const seg = snake.segments[i];
    const follow = 0.26;
    seg.x += (prev.x - seg.x) * follow;
    seg.y += (prev.y - seg.y) * follow;
  }
}

function updateSnakeCollisions() {
  const headRadius = 14;

  for (const a of [...state.players.values(), ...state.wildBots]) {
    if (!a.alive) continue;
    const head = a.segments[0];

    for (const b of [...state.players.values(), ...state.wildBots]) {
      if (!b.alive) continue;
      if (a.id === b.id) continue;

      for (let i = 1; i < b.segments.length; i++) {
        const seg = b.segments[i];
        if (Math.hypot(head.x - seg.x, head.y - seg.y) < headRadius * 2 - 2) {
          killSnake(a, true);
          break;
        }
      }
      if (!a.alive) break;
    }
  }
}

function updateBorderDamage(dt) {
  if (!state.currentEvent || state.currentEvent.type !== 'border') return;
  const w = getWorldRect();
  const thickness = 6;

  for (const snake of [...state.players.values(), ...state.wildBots]) {
    if (!snake.alive) continue;
    const head = snake.segments[0];
    const touching =
      head.x <= w.minX + thickness ||
      head.x >= w.maxX - thickness ||
      head.y <= w.minY + thickness ||
      head.y >= w.maxY - thickness;

    if (!touching) {
      snake.borderDrainAccum = 0;
      continue;
    }

    snake.borderDrainAccum += 10 * dt;
    while (snake.borderDrainAccum >= 1) {
      snake.borderDrainAccum -= 1;
      if (snake.score > 0) changeScore(snake, -1, false);
      else {
        killSnake(snake, true);
        break;
      }
    }
  }
}

function updateFloodState(now) {
  if (!state.currentEvent || state.currentEvent.type !== 'flood') return;

  if (now < state.currentEvent.riseEnd) {
    const t = (now - state.currentEvent.start) / 30000;
    state.floodWaterLevel = clamp(t, 0, 1);
  } else if (now < state.currentEvent.holdEnd) {
    state.floodWaterLevel = 1;
  } else if (now < state.currentEvent.end) {
    const t = (now - state.currentEvent.holdEnd) / 10000;
    state.floodWaterLevel = clamp(1 - t, 0, 1);
  } else {
    state.floodWaterLevel = 0;
  }
}

function updateEventState(now, dt) {
  if (!state.currentEvent) return;

  if (state.currentEvent.type === 'storm' || state.currentEvent.type === 'superStorm') {
    if (state.currentEvent.type === 'superStorm' && now >= state.currentEvent.flashNext) {
      state.stormFlashAlpha = 1;
      state.currentEvent.flashNext += 10000;
    }
    state.stormFlashAlpha = Math.max(0, state.stormFlashAlpha - dt * 1.6);
    return;
  }

  if (state.currentEvent.type === 'space') {
    if (now >= state.currentEvent.blackHoleStart && now < state.currentEvent.blackHoleGrowEnd) {
      const t = (now - state.currentEvent.blackHoleStart) / 20000;
      state.currentEvent.holeRadius = lerp(50, 900, clamp(t, 0, 1));
    } else if (now >= state.currentEvent.blackHoleGrowEnd && now < state.currentEvent.blackHoleHoldEnd) {
      state.currentEvent.holeRadius = 900;
    }
  }
}

function updateFoodInteractions(now, dt) {
  for (let i = state.foods.length - 1; i >= 0; i--) {
    const food = state.foods[i];
    let eaten = false;

    if (state.currentEvent && state.currentEvent.type === 'space') {
      const cx = state.currentEvent.centerX;
      const cy = state.currentEvent.centerY;
      const d = Math.hypot(food.x - cx, food.y - cy);
      if (d <= state.currentEvent.holeRadius) {
        state.foods.splice(i, 1);
        state.currentEvent.holeRadius = Math.min(900, state.currentEvent.holeRadius + 1);
        continue;
      }
    }

    for (const snake of [...state.players.values(), ...state.wildBots]) {
      if (!snake.alive) continue;
      const head = snake.segments[0];
      const hitRadius = PICKUP_RADIUS + 10;
      if (Math.hypot(head.x - food.x, head.y - food.y) <= hitRadius) {
        applyFoodEffect(snake, food);
        state.foods.splice(i, 1);
        eaten = true;
        break;
      }
    }
    if (eaten) continue;

    const attractor = getClosestMagnetSnake(food);
    if (attractor) {
      const head = attractor.segments[0];
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

  if (state.currentEvent && (state.currentEvent.type === 'storm' || state.currentEvent.type === 'superStorm')) {
    const wind = getWindVector();
    for (const food of state.foods) {
      food.x += wind.x * getStormPush('food') * dt;
      food.y += wind.y * getStormPush('food') * dt;
      food.x = clamp(food.x, 0, MAP_MAX);
      food.y = clamp(food.y, 0, MAP_MAX);
    }
  }
}

function getTopRanking() {
  return [...state.players.values()]
    .filter(p => p.alive || p.score > 0)
    .sort((a, b) => b.score - a.score)
    .slice(0, 10)
    .map(p => ({ id: p.id, nick: p.nick, score: p.score }));
}

function snapshotState() {
  return {
    worldSize: state.worldSize,
    event: state.currentEvent,
    floodWaterLevel: state.floodWaterLevel,
    stormFlashAlpha: state.stormFlashAlpha,
    spaceFlashAlpha: state.spaceFlashAlpha,
    spaceStars: state.spaceStars,
    foods: state.foods,
    snakes: [
      ...[...state.players.values()],
      ...state.wildBots
    ],
    ranking: getTopRanking()
  };
}

function step() {
  const now = Date.now();
  const dt = TICK_MS / 1000;

  updateEvent(now, dt);
  updateFoodSpawns(dt);
  updateFoodInteractions(now, dt);
  updateBorderDamage(dt);
  updateFloodState(now);
  updateSnakeCollisions();

  for (const snake of state.players.values()) {
    if (!snake.alive) {
      if (now >= snake.respawnAt) respawnSnake(snake);
      continue;
    }

    const input = snake.input || { x: 0, y: 0, nitro: false };
    const len = Math.hypot(input.x, input.y);
    let nx = 0, ny = 0;
    if (len > 0.001) {
      nx = input.x / len;
      ny = input.y / len;
      snake.angle = Math.atan2(ny, nx);
    }

    const turboActive = now < snake.turboUntil;
    const nitroActive = input.nitro && snake.score > 0 && !isInFlood(snake);
    const floodSlow = isInFlood(snake) ? 0.5 : 1;

    let speed = 190 * floodSlow;
    if (turboActive) speed *= 3;
    if (nitroActive) speed *= 2;

    const wind = getWindVector();
    if (state.currentEvent && (state.currentEvent.type === 'storm' || state.currentEvent.type === 'superStorm')) {
      const dirX = Math.cos(snake.angle);
      const dirY = Math.sin(snake.angle);
      const dot = dirX * wind.x + dirY * wind.y;
      if (dot > 0.2) speed *= 2;
      else if (dot < -0.2) speed *= 0.5;
      snake.x += wind.x * getStormPush('snake') * dt;
      snake.y += wind.y * getStormPush('snake') * dt;
    }

    moveSnakeByInput(snake, nx, ny, dt, speed);

    if (nitroActive) {
      snake.nitroDrainAccum += dt * 2;
      while (snake.nitroDrainAccum >= 1 && snake.score > 0) {
        snake.nitroDrainAccum -= 1;
        changeScore(snake, -1, true);
      }
      if (snake.score <= 0) {
        snake.input.nitro = false;
        snake.nitroDrainAccum = 0;
      }
    }
  }

  for (const bot of state.wildBots) {
    if (!bot.alive) {
      if (now >= bot.respawnAt) respawnSnake(bot);
      continue;
    }

    const floodSlow = isInFlood(bot) ? 0.5 : 1;
    const wind = getWindVector();
    const stormActive = state.currentEvent && (state.currentEvent.type === 'storm' || state.currentEvent.type === 'superStorm');

    if (bot.isWild) {
      if (now >= bot.wildExpiresAt) {
        killSnake(bot, true);
        continue;
      }

      const target = getNearestPlayerTarget(bot);
      if (target) {
        const dx = target.x - bot.x;
        const dy = target.y - bot.y;
        const dist = Math.hypot(dx, dy) || 1;
        const baseAngle = Math.atan2(dy, dx);
        const orbit = Math.sin(now * 0.002 + bot.wanderPhase) * 0.6 * bot.aiStrafeDir;
        let desired = baseAngle + orbit;
        if (dist < 180) desired += bot.aiStrafeDir * Math.PI / 3;

        bot.angle = approachAngle(bot.angle, desired, 0.09);

        if (bot.aiDashCooldown > 0) bot.aiDashCooldown -= dt;
        if (bot.aiDashCooldown <= 0 && dist < 360) {
          bot.aiDashUntil = now + 500;
          bot.aiDashCooldown = rand(1.7, 3.2);
          bot.aiStrafeDir *= -1;
        }

        const dash = now < bot.aiDashUntil;
        let speed = (dash ? 320 : 230) * floodSlow;

        if (stormActive) {
          const dirX = Math.cos(bot.angle);
          const dirY = Math.sin(bot.angle);
          const dot = dirX * wind.x + dirY * wind.y;
          if (dot > 0.2) speed *= 2;
          else if (dot < -0.2) speed *= 0.5;
          bot.x += wind.x * getStormPush('snake') * dt;
          bot.y += wind.y * getStormPush('snake') * dt;
        }

        const nx = Math.cos(bot.angle);
        const ny = Math.sin(bot.angle);
        moveSnakeByInput(bot, nx, ny, dt, speed);
      } else {
        moveSnakeByInput(bot, Math.cos(bot.angle), Math.sin(bot.angle), dt, 180 * floodSlow);
      }
    }
  }

  const ranking = getTopRanking();

  io.emit('state', {
    ...snapshotState(),
    ranking
  });

  for (const snake of state.players.values()) {
    if (!snake.alive && snake.isPlayer && snake.socketId) {
      io.to(snake.socketId).emit('dead', { score: snake.score });
    }
  }
}

io.on('connection', socket => {
  socket.emit('welcome', { id: socket.id });

  socket.on('join', ({ nick }) => {
    const name = String(nick || 'Jogador').trim().slice(0, 16) || 'Jogador';

    if (state.players.has(socket.id)) {
      const existing = state.players.get(socket.id);
      existing.nick = name;
      existing.socketId = socket.id;
      existing.isPlayer = true;
      existing.alive = true;
      existing.respawnAt = 0;
      existing.input = existing.input || { x: 0, y: 0, nitro: false };
      socket.emit('joined', { id: socket.id, nick: existing.nick });
      return;
    }

    const player = createPlayer(socket.id, name);
    state.players.set(socket.id, player);
    socket.emit('joined', { id: socket.id, nick: player.nick });
    socket.emit('banner', { text: 'Bem-vindo!' });
  });

  socket.on('restart', ({ nick }) => {
    const name = String(nick || 'Jogador').trim().slice(0, 16) || 'Jogador';
    let player = state.players.get(socket.id);
    if (!player) {
      player = createPlayer(socket.id, name);
      state.players.set(socket.id, player);
    } else {
      const pos = findSafeSpawn([...state.players.values(), ...state.wildBots].filter(s => s.id !== player.id));
      player.x = pos.x;
      player.y = pos.y;
      player.angle = Math.random() * Math.PI * 2;
      player.nick = name;
      player.color = randomColor();
      player.score = 0;
      player.alive = true;
      player.respawnAt = 0;
      player.turboUntil = 0;
      player.magnetUntil = 0;
      player.input = { x: 0, y: 0, nitro: false };
      rebuildBody(player);
    }
    socket.emit('respawned', { score: player.score });
    socket.emit('joined', { id: socket.id, nick: player.nick });
  });

  socket.on('input', input => {
    const player = state.players.get(socket.id);
    if (!player) return;

    const x = clamp(Number(input?.x) || 0, -1, 1);
    const y = clamp(Number(input?.y) || 0, -1, 1);
    const nitro = Boolean(input?.nitro);

    player.input = { x, y, nitro };
    player.nitroHeld = nitro;
  });

  socket.on('disconnect', () => {
    const player = state.players.get(socket.id);
    if (player) {
      player.alive = false;
      player.respawnAt = Infinity;
    }
  });
});

spawnInitialFoods();

setInterval(step, TICK_MS);

server.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});
