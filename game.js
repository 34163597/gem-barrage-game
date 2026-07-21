const canvas = document.querySelector("#game");
const ctx = canvas.getContext("2d", { alpha: false, desynchronized: true });
const platform = globalThis.GamePlatform;
const scoreEl = document.querySelector("#score");
const chainEl = document.querySelector("#chain");
const startCard = document.querySelector("#startCard");
const gameOverCard = document.querySelector("#gameOver");
const finalScore = document.querySelector("#finalScore");
const hint = document.querySelector("#hint");
const soundBtn = document.querySelector("#soundBtn");
const heatFill = document.querySelector("#heatFill");
const stormText = document.querySelector("#stormText");
const heatBar = document.querySelector(".heat");
const buffBar = document.querySelector("#buffBar");
const upgradeCard = document.querySelector("#upgradeCard");
const adAimBtn = document.querySelector("#adAimBtn");
const startLeaderboard = document.querySelector("#startLeaderboard");
const gameOverLeaderboard = document.querySelector("#gameOverLeaderboard");
const rankBtn = document.querySelector("#rankBtn");
const rankPanel = document.querySelector("#rankPanel");
const rankCloseBtn = document.querySelector("#rankCloseBtn");
const rankLeaderboard = document.querySelector("#rankLeaderboard");
const guardLayerInput = document.querySelector("#guardLayerInput");
const guardTestBtn = document.querySelector("#guardTestBtn");
const xpTestBtn = document.querySelector("#xpTestBtn");
const limitIceBtn = document.querySelector("#limitIceBtn");

const shapeColors = {
  diamond: "#5ff4ff",
  orb: "#b8ff5f",
  triangle: "#ff7bd5",
  pentagon: "#9b7bff",
  bomb: "#ff4b4b",
  hunterBomb: "#35ffd4",
  upgrade: "#ffd95f",
  megaBomb: "#ff8cff",
  split: "#ffb15f",
  mystery: "#ffffff"
};
let w, h, dpr, raf, last;
let score = 0, chain = 1, bestChain = 1, turn = 1, shake = 0;
let running = false, aiming = true, dragging = false;
let angle = -Math.PI / 2, launchX = 0, launchY = 0;
let balls = [], blocks = [], particles = [], popups = [], banners = [], trails = [], snowflakes = [], shockwaves = [], beams = [];
let aimGuideCache = null;
let blockSpatialIndex = new Map();
let corridorDepth = 0;
let audioCtx, masterGain, lastHitSound = 0;
let dropping = false, openingDrop = false;
let heat = 0, stormTimer = 0, choosingBuff = false;
let upgrades = {};
let screenFlash = 0;
let shotHits = 0;
let praisedComboTier = 0;
let pendingComboPraise = null;
let comboPraiseToast = null;
let goldenShots = 0;
let defenseCharge = 0;
let defenseRequired = 100;
let defenseReady = false;
let defenseLayers = 0;
let defenseFlash = 0;
let defenseBlast = null;
let adAimBoost = false;
let watchingAd = false;

const isMobile = globalThis.matchMedia?.("(pointer: coarse)")?.matches || Math.min(screen.width, screen.height) < 720;
const renderQuality = isMobile ? "mobile" : "desktop";
const maxParticles = isMobile ? 180 : 420;
const maxTrails = isMobile ? 120 : 260;
const targetRenderInterval = isMobile ? 1000 / 45 : 0;
let lastRender = 0;
const spatialCellSize = 92;

const GOLDEN_SHOT_REWARD = 3;
const DEFENSE_GROWTH = 1.3;
const DEFENSE_MAX_LAYERS = 5;
const DROP_GROWTH_PER_TURN = .05;
const DROP_GROWTH_MAX = 1;
const BOSS_ENABLED = false;
const BOSS_START_TURN = 7;
const BOSS_INTERVAL = 8;
const clamp = (n, min, max) => Math.max(min, Math.min(max, n));
const random = (min, max) => min + Math.random() * (max - min);
const grid = { side: 12, cell: 47, row: 43, top: 112 };
const upgradePool = [
  { id: "multi", icon: "+", name: "多重弹", description: "每次发射额外增加 1 颗弹珠，最多 2 级", max: 2, weight: .55 },
  { id: "power", icon: "P", name: "重击", description: "每次碰撞额外造成 1 点伤害", weight: .65 },
  { id: "pierce", icon: ">>", name: "晶钻弹", description: "每颗弹珠可穿透 2 次宝石，更容易钻进宝石群内部", weight: 1 },
  { id: "speed", icon: "S", name: "疾速弹", description: "弹珠速度提高 8%，并更不容易漏出宝石群", weight: 1.25 },
  { id: "heat", icon: "H", name: "晶能充能", description: "砸碎宝石时额外获得进度", weight: 1 },
  { id: "storm", icon: "C", name: "能量回流", description: "选择强化后保留一部分进度，最多保留 45%", max: 3, weight: 1 },
  { id: "blast", icon: "!", name: "爆破强化", description: "爆炸宝石和大爆炸宝石范围、伤害提升", weight: 1 },
  { id: "score", icon: "$", name: "砸宝石加分", description: "普通宝石得分提高 25%，并额外获得少量进度", weight: 1.2 },
  { id: "shatter", icon: "*", name: "晶片飞溅", description: "砸碎宝石时对近处宝石造成溅射伤害", weight: .65 },
  { id: "aim", icon: "L", name: "延长线", description: "瞄准辅助线变长，最多延长一倍", weight: 1.25 }
];

function resetUpgrades() {
  upgrades = Object.fromEntries(upgradePool.map(upgrade => [upgrade.id, 0]));
  updateBuffBar();
}
resetUpgrades();

function initAudio() {
  if (!audioCtx) {
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    masterGain = audioCtx.createGain();
    masterGain.gain.value = .52;
    masterGain.connect(audioCtx.destination);
  }
  if (audioCtx.state === "suspended") audioCtx.resume();
}

function tone({ frequency = 440, endFrequency = frequency, duration = .08, volume = .18, type = "sine", delay = 0 }) {
  if (!audioCtx || !masterGain) return;
  const now = audioCtx.currentTime + delay;
  const osc = audioCtx.createOscillator();
  const gain = audioCtx.createGain();
  osc.type = type;
  osc.frequency.setValueAtTime(frequency, now);
  osc.frequency.exponentialRampToValueAtTime(Math.max(20, endFrequency), now + duration);
  gain.gain.setValueAtTime(.0001, now);
  gain.gain.exponentialRampToValueAtTime(volume, now + .008);
  gain.gain.exponentialRampToValueAtTime(.0001, now + duration);
  osc.connect(gain); gain.connect(masterGain);
  osc.start(now); osc.stop(now + duration + .02);
}

function noiseBurst({ duration = .12, volume = .2, delay = 0, highpass = 900 }) {
  if (!audioCtx || !masterGain) return;
  const now = audioCtx.currentTime + delay;
  const buffer = audioCtx.createBuffer(1, Math.ceil(audioCtx.sampleRate * duration), audioCtx.sampleRate);
  const data = buffer.getChannelData(0);
  for (let i = 0; i < data.length; i++) {
    const fade = 1 - i / data.length;
    data[i] = (Math.random() * 2 - 1) * fade * fade;
  }
  const source = audioCtx.createBufferSource();
  const filter = audioCtx.createBiquadFilter();
  const gain = audioCtx.createGain();
  source.buffer = buffer;
  filter.type = "highpass";
  filter.frequency.value = highpass;
  gain.gain.setValueAtTime(volume, now);
  gain.gain.exponentialRampToValueAtTime(.0001, now + duration);
  source.connect(filter); filter.connect(gain); gain.connect(masterGain);
  source.start(now); source.stop(now + duration + .02);
}

function gemChime(base = 980, volume = .12, delay = 0) {
  const detune = random(-28, 28);
  tone({ frequency: base + detune, endFrequency: base * .82, duration: .11, volume, type: "sine", delay });
  tone({ frequency: base * 1.52 + detune, endFrequency: base * 1.14, duration: .085, volume: volume * .55, type: "sine", delay: delay + .006 });
  tone({ frequency: base * 2.18 + detune, endFrequency: base * 1.72, duration: .06, volume: volume * .28, type: "sine", delay: delay + .012 });
}

function playSound(name, strength = 1) {
  if (!audioCtx) return;
  if (name === "launch") {
    noiseBurst({ duration: .09, volume: .11, highpass: 760 });
    tone({ frequency: 180, endFrequency: 420, duration: .14, volume: .12, type: "sine" });
    gemChime(720, .055, .035);
  } else if (name === "hit") {
    const now = performance.now();
    if (now - lastHitSound < 42) return;
    lastHitSound = now;
    noiseBurst({ duration: .028, volume: .035, highpass: 4200 });
    gemChime(960 + Math.min(strength, 10) * 18, .105);
  } else if (name === "break") {
    noiseBurst({ duration: .13, volume: .26, highpass: 3600 });
    noiseBurst({ duration: .24, volume: .18, delay: .018, highpass: 1700 });
    gemChime(1320, .16);
    gemChime(1780, .095, .024);
    tone({ frequency: 520, endFrequency: 180, duration: .16, volume: .09, type: "sine", delay: .035 });
  } else if (name === "chain") {
    const level = Math.min(strength, 12);
    gemChime(760 + level * 42, .105);
    gemChime(1010 + level * 36, .06, .045);
  } else if (name === "gameover") {
    noiseBurst({ duration: .28, volume: .16, highpass: 950 });
    tone({ frequency: 280, endFrequency: 105, duration: .5, volume: .2, type: "sine" });
    tone({ frequency: 420, endFrequency: 160, duration: .38, volume: .09, type: "sine", delay: .04 });
  }
}

function resize() {
  // High-density phones pay heavily for full 2x canvas redraws. Keep the game crisp
  // while leaving enough headroom for collisions and effects during dense turns.
  dpr = Math.min(devicePixelRatio || 1, isMobile ? 1.25 : 2);
  w = canvas.clientWidth;
  h = canvas.clientHeight;
  canvas.width = w * dpr;
  canvas.height = h * dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  launchX = w / 2;
  launchY = h - 74;
  if (!snowflakes.length) seedSnow();
}

function seedSnow() {
  const count = isMobile
    ? Math.min(42, Math.max(24, Math.floor(w * h / 11800)))
    : Math.max(55, Math.floor(w * h / 6400));
  snowflakes = Array.from({ length: count }, () => makeSnowflake(random(0, h)));
}

function makeSnowflake(y = random(-40, -4)) {
  const depth = random(.35, 1);
  return {
    x: random(0, w),
    y,
    r: random(.8, 2.6) * depth,
    vy: random(18, 58) * depth,
    sway: random(8, 24) * depth,
    phase: random(0, Math.PI * 2),
    alpha: random(.2, .72) * depth
  };
}

function blockRadius(block) {
  const base = block.type === "orb" ? 16 : 18;
  return base * (block.size || 1);
}

function blockLayoutRadius(block) {
  return blockRadius(block) + (block.type === "triangle" ? 4 : 3);
}

function spatialCellKey(x, y) {
  return `${Math.floor(x / spatialCellSize)}:${Math.floor(y / spatialCellSize)}`;
}

function rebuildBlockSpatialIndex() {
  const next = new Map();
  for (const block of blocks) {
    if (block.value <= 0) continue;
    const radius = blockLayoutRadius(block) + 4;
    const minX = Math.floor((block.x - radius) / spatialCellSize);
    const maxX = Math.floor((block.x + radius) / spatialCellSize);
    const minY = Math.floor((block.y - radius) / spatialCellSize);
    const maxY = Math.floor((block.y + radius) / spatialCellSize);
    for (let cellX = minX; cellX <= maxX; cellX++) {
      for (let cellY = minY; cellY <= maxY; cellY++) {
        const key = `${cellX}:${cellY}`;
        const bucket = next.get(key) || [];
        bucket.push(block);
        next.set(key, bucket);
      }
    }
  }
  blockSpatialIndex = next;
}

function nearbyBlocks(x, y, radius) {
  if (!blockSpatialIndex.size) return blocks;
  const found = new Set();
  const minX = Math.floor((x - radius) / spatialCellSize);
  const maxX = Math.floor((x + radius) / spatialCellSize);
  const minY = Math.floor((y - radius) / spatialCellSize);
  const maxY = Math.floor((y + radius) / spatialCellSize);
  for (let cellX = minX; cellX <= maxX; cellX++) {
    for (let cellY = minY; cellY <= maxY; cellY++) {
      for (const block of blockSpatialIndex.get(`${cellX}:${cellY}`) || []) found.add(block);
    }
  }
  return found;
}

function isBossShieldRole(role) {
  return role === "shield";
}

function activeBossShieldNodes() {
  return blocks.filter(block => block.boss && isBossShieldRole(block.bossRole) && block.value > 0);
}

function bossShieldActive() {
  return activeBossShieldNodes().length >= 3;
}

function bossShieldPolygon() {
  const nodes = activeBossShieldNodes();
  if (nodes.length < 3) return [];
  const cx = nodes.reduce((sum, block) => sum + block.x, 0) / nodes.length;
  const cy = nodes.reduce((sum, block) => sum + block.y, 0) / nodes.length;
  return nodes.sort((a, b) => Math.atan2(a.y - cy, a.x - cx) - Math.atan2(b.y - cy, b.x - cx));
}

function pointInBossShieldPolygon(x, y, polygon) {
  let inside = false;
  for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
    const a = polygon[i], b = polygon[j];
    const crosses = (a.y > y) !== (b.y > y) && x < (b.x - a.x) * (y - a.y) / ((b.y - a.y) || .001) + a.x;
    if (crosses) inside = !inside;
  }
  return inside;
}

function setShieldedHealth(block, shielded) {
  if (isBossShieldRole(block.bossRole)) return;
  if (shielded && !block.shieldedByLine) {
    block.shieldBaseMax = block.max;
    block.max = Math.ceil(block.max * 2);
    block.value = Math.ceil(block.value * 2);
    block.shieldedByLine = true;
    block.pulse = 1;
    return;
  }
  if (!shielded && block.shieldedByLine) {
    block.max = block.shieldBaseMax || Math.ceil(block.max / 2);
    block.value = Math.max(1, Math.ceil(block.value / 2));
    block.shieldedByLine = false;
    block.shieldWeakened = true;
    block.pulse = 1;
  }
}

function updateBossShieldField() {
  const polygon = bossShieldPolygon();
  const active = polygon.length >= 3;
  for (const block of blocks) {
    if (block.value <= 0) continue;
    const protectedByLine = active && pointInBossShieldPolygon(block.x, block.y, polygon);
    setShieldedHealth(block, protectedByLine);
  }
}

function weakenBossShield() {
  if (bossShieldActive()) return;
  for (const block of blocks) {
    if (!block.shieldedByLine) continue;
    setShieldedHealth(block, false);
    burst(block.x, block.y, "#ffd76b", 8);
  }
  popups.push({ x: w / 2, y: grid.top + 56, text: "SHIELD DOWN", life: 1.2 });
  showBanner("SHIELD DOWN", "CORE WEAKENED", "#ffd76b", 1.45);
  playSound("chain", 8);
}

function makeBlock(x, y, value, type = "diamond", forcedSpecial = null) {
  const roll = Math.random();
  const special = forcedSpecial ?? (
    roll < .03 ? "bomb" :
    roll < .036 ? "megaBomb" :
    roll < .13 ? "hunterBomb" :
    roll < .15 ? "split" :
    roll < .19 ? "mystery" :
    ""
  );
  const health = special === "megaBomb" ? value * 2 : value;
  return { x, y, targetY: y, value: health, max: health, type, special, size: random(.9, 1.1), hit: 0, spin: random(-.2, .2), pulse: 0 };
}

function enforceSingleMegaBomb(list) {
  let found = false;
  for (const block of list) {
    if (block.special !== "megaBomb") continue;
    if (!found) {
      found = true;
      continue;
    }
    block.special = "";
    block.value = Math.ceil(block.value / 2);
    block.max = block.value;
  }
}

function normalizeExplosive(block) {
  if (block.special === "megaBomb") {
    block.value = Math.max(1, Math.ceil(block.value / 2));
    block.max = block.value;
  }
  block.special = "";
  block.exploded = false;
}

function enforceBombSpread(list, minDistance = 128) {
  const kept = [];
  for (const block of list) {
    if (block.special !== "bomb" && block.special !== "megaBomb" && block.special !== "hunterBomb" && block.special !== "mystery") continue;
    const y = block.targetY ?? block.y;
    const tooClose = kept.some(other => Math.hypot(block.x - other.x, y - other.y) < minDistance);
    if (tooClose) {
      normalizeExplosive(block);
    } else {
      kept.push({ x: block.x, y });
    }
  }
}

function enforceUpgradeLimit(list) {
  let kept = 0;
  for (const block of list) {
    if (block.special !== "upgrade") continue;
    if (kept < 2) {
      kept += 1;
      continue;
    }
    block.special = "";
  }
}

function randomBlockType() {
  const roll = Math.random();
  if (roll < .22) return "triangle";
  if (roll < .43) return "orb";
  if (roll < .6) return "pentagon";
  return "diamond";
}

function blockHealth(round = turn) {
  const stage = Math.floor((Math.max(1, round) - 1) / 3);
  const min = 1 + Math.floor(stage * .72);
  const max = 4 + stage * 2;
  return Math.floor(random(min, max + 1));
}

function dropGrowthBonus(round = turn) {
  return clamp((round - 1) * DROP_GROWTH_PER_TURN, 0, DROP_GROWTH_MAX);
}

function rowDropDistance(round = turn) {
  const baseDistance = grid.row * 2 / 3 * (1 + dropGrowthBonus(round));
  const failureY = launchY - 52;
  const frontY = blocks.reduce((deepest, block) => Math.max(deepest, block.targetY ?? block.y), grid.top);
  const pressure = clamp((frontY - grid.top) / Math.max(1, failureY - grid.top), 0, 1);
  const safetyScale = 1.8 - pressure * 1.3;
  return baseDistance * safetyScale;
}

function blockColor(block) {
  if (block.boss) return "#ffd76b";
  if (block.special && shapeColors[block.special]) return shapeColors[block.special];
  return shapeColors[block.type];
}

function icePalette(block) {
  if (block.boss) return [
    "rgba(255, 250, 206, .96)",
    "rgba(255, 202, 58, .84)",
    "rgba(120, 52, 206, .9)",
    "rgba(255, 246, 156, 1)"
  ];
  if (block.special === "bomb") return [
    "rgba(255, 218, 205, .96)",
    "rgba(255, 70, 70, .9)",
    "rgba(112, 8, 34, .92)",
    "rgba(255, 235, 222, 1)"
  ];
  if (block.special === "hunterBomb") return [
    "rgba(218, 255, 248, .96)",
    "rgba(40, 255, 205, .9)",
    "rgba(5, 94, 132, .92)",
    "rgba(220, 255, 250, 1)"
  ];
  if (block.special === "upgrade") return [
    "rgba(255, 250, 206, .96)",
    "rgba(255, 220, 64, .9)",
    "rgba(126, 82, 11, .92)",
    "rgba(255, 248, 190, 1)"
  ];
  if (block.special === "megaBomb") return [
    "rgba(255, 226, 255, .96)",
    "rgba(228, 95, 255, .9)",
    "rgba(74, 28, 138, .94)",
    "rgba(255, 224, 255, 1)"
  ];
  if (block.special === "split") return [
    "rgba(255, 241, 214, .96)",
    "rgba(255, 175, 88, .88)",
    "rgba(129, 58, 16, .9)",
    "rgba(255, 238, 208, 1)"
  ];
  if (block.special === "mystery") return [
    "rgba(255, 255, 255, .96)",
    "rgba(188, 235, 255, .84)",
    "rgba(86, 64, 184, .9)",
    "rgba(255, 255, 255, 1)"
  ];
  if (block.type === "orb") return [
    "rgba(246, 255, 218, .95)",
    "rgba(184, 255, 95, .86)",
    "rgba(34, 118, 66, .9)",
    "rgba(248, 255, 222, 1)"
  ];
  if (block.type === "triangle") return [
    "rgba(255, 224, 250, .95)",
    "rgba(255, 112, 210, .86)",
    "rgba(124, 24, 112, .9)",
    "rgba(255, 232, 253, 1)"
  ];
  if (block.type === "pentagon") return [
    "rgba(237, 228, 255, .95)",
    "rgba(154, 120, 255, .86)",
    "rgba(58, 45, 145, .9)",
    "rgba(240, 232, 255, 1)"
  ];
  return [
    "rgba(226, 255, 255, .95)",
    "rgba(76, 238, 255, .86)",
    "rgba(18, 92, 160, .9)",
    "rgba(225, 255, 255, 1)"
  ];
}

function corridorDistance(col, cols, depth) {
  const center = (cols - 1) / 2;
  const lane = center + Math.sin(depth * .62) * 1.1;
  return Math.abs(col - lane);
}

function isCorridorCell(col, cols, depth) {
  const distance = corridorDistance(col, cols, depth);
  if (distance < .68) return true;
  // Keep small ricochet pockets, but avoid a continuous empty central band.
  return depth % 4 === 2 && distance < 1.55;
}

function cellPosition(col, row, gap) {
  const stagger = row % 2 ? gap * .32 : -gap * .18;
  return {
    x: clamp(grid.side + gap * (col + .5) + stagger + random(-18, 18), grid.side + 18, w - grid.side - 18),
    y: grid.top + row * grid.row + random(-15, 15)
  };
}

function skipPackedCell(col, depth, density = 1) {
  const pocket = Math.sin(col * 1.7 + depth * 1.15) + Math.cos(col * .65 - depth * 1.8);
  const skip = pocket > .45 ? .015 : pocket < -.65 ? .15 : .055;
  return Math.random() < clamp(1 - density + skip, .015, .62);
}

function isOpenCorridor(x, depth, cols, gap) {
  const col = (x - grid.side) / gap - .5;
  return isCorridorCell(col, cols, depth);
}

function canPlaceBlock(x, y, list = blocks, type = "diamond", ignored = null, special = "", gap = 2) {
  const radius = blockLayoutRadius({ type, special });
  return list.every(block => {
    if (block === ignored) return true;
    const checkY = block.targetY ?? block.y;
    const minDistance = radius + blockLayoutRadius(block) + gap;
    return Math.hypot(block.x - x, checkY - y) >= minDistance;
  });
}

function addAttachedPairs(list, chance = .2, sources = [...list]) {
  for (const source of sources) {
    if (Math.random() > chance) continue;
    const type = randomBlockType();
    const distance = blockLayoutRadius(source) + blockLayoutRadius({ type }) + 2;
    const start = random(0, Math.PI * 2);
    for (let attempt = 0; attempt < 8; attempt++) {
      const direction = start + attempt * Math.PI / 4;
      const x = source.x + Math.cos(direction) * distance;
      const y = source.y + Math.sin(direction) * distance;
      if (x < grid.side + 18 || x > w - grid.side - 18 || y < grid.top - 18 || !canPlaceBlock(x, y, list, type, source, "", 1)) continue;
      const value = blockHealth();
      const block = makeBlock(x, y, value, type);
      block.targetY = source.targetY + Math.sin(direction) * distance;
      list.push(block);
      break;
    }
  }
}

function separateBlocks(list = blocks, iterations = 5) {
  for (let pass = 0; pass < iterations; pass++) {
    for (let i = 0; i < list.length; i++) {
      const a = list[i];
      if (a.value <= 0) continue;
      for (let j = i + 1; j < list.length; j++) {
        const b = list[j];
        if (b.value <= 0) continue;
        const ay = a.targetY ?? a.y;
        const by = b.targetY ?? b.y;
        const dx = b.x - a.x;
        const dy = by - ay;
        const distance = Math.hypot(dx, dy) || .001;
        const minDistance = blockLayoutRadius(a) + blockLayoutRadius(b) + 2.5;
        if (distance >= minDistance) continue;
        const push = (minDistance - distance) * .52;
        const nx = dx / distance;
        const ny = dy / distance;
        a.x = clamp(a.x - nx * push, grid.side + 24, w - grid.side - 24);
        b.x = clamp(b.x + nx * push, grid.side + 24, w - grid.side - 24);
        a.targetY = Math.max(grid.top - 22, ay - ny * push);
        b.targetY = Math.max(grid.top - 22, by + ny * push);
        if (!dropping) {
          a.y = a.targetY;
          b.y = b.targetY;
        }
      }
    }
  }
}

function addCorridorAccents(list, cols, gap, rows) {
  for (let row = 1; row < rows; row += 2) {
    const depth = rows - 1 - row;
    const center = (cols - 1) / 2 + Math.sin(depth * .62) * 1.1;
    const side = row % 4 === 1 ? -1 : 1;
    const x = grid.side + gap * (center + .5 + side * random(.8, 1.25));
    const y = grid.top + row * grid.row + random(-8, 8);
    const type = randomBlockType();
    if (!canPlaceBlock(x, y, list, type)) continue;
    const value = blockHealth();
    list.push(makeBlock(x, y, value, type));
  }
}

function fillRandomGaps(list, cols, gap, rows, attempts) {
  for (let i = 0; i < attempts; i++) {
    const row = Math.floor(random(0, rows));
    const depth = rows - 1 - row;
    const x = random(grid.side + 18, w - grid.side - 18);
    const y = grid.top + row * grid.row + random(-18, 18);
    const type = randomBlockType();
    if (isOpenCorridor(x, depth, cols, gap) || !canPlaceBlock(x, y, list, type)) continue;
    const value = blockHealth();
    list.push(makeBlock(x, y, value, type));
  }
}

function isBossTurn(round = turn) {
  return BOSS_ENABLED && round >= BOSS_START_TURN && (round - BOSS_START_TURN) % BOSS_INTERVAL === 0;
}

function addPlaneBoss(dropDistance) {
  const spacingX = clamp((w - grid.side * 2) / 8, 34, 42);
  const spacingY = 36;
  const centerX = w / 2;
  const centerY = grid.top + 72;
  const bossHealth = Math.ceil(blockHealth(turn) * 1.75);
  const blueprint = [
    [0, -2, "orb", 1.15, "shield"],
    [-1, -1, "diamond", 1.15, "body"], [0, -1, "diamond", 1.35, "body"], [1, -1, "diamond", 1.15, "body"],
    [-3, 0, "triangle", 1, "wing"], [-2, 0, "diamond", 1.05, "wing"], [-1, 0, "diamond", 1.2, "body"], [0, 0, "orb", 1.8, "core"], [1, 0, "diamond", 1.2, "body"], [2, 0, "diamond", 1.05, "wing"], [3, 0, "triangle", 1, "wing"],
    [-3, 1, "orb", 1.05, "shield"], [-1, 1, "diamond", 1.1, "body"], [0, 1, "diamond", 1.25, "body"], [1, 1, "diamond", 1.1, "body"], [3, 1, "orb", 1.05, "shield"],
    [-1, 2, "triangle", 1, "tail"], [0, 2, "pentagon", 1.2, "tail"], [1, 2, "triangle", 1, "tail"]
  ];

  let added = 0;
  for (const [ox, oy, type, hpScale, role] of blueprint) {
    const x = centerX + ox * spacingX + random(-3, 3);
    const y = centerY + oy * spacingY + random(-2, 2);
    if (!canPlaceBlock(x, y, blocks, type, null, "", 1)) continue;
    const block = makeBlock(x, y - dropDistance - random(20, 54), Math.ceil(bossHealth * hpScale), type, "");
    block.targetY = y;
    block.boss = true;
    block.bossRole = role;
    block.size = .86;
    block.spin = ox * .025;
    blocks.push(block);
    added += 1;
  }

  if (added > 0) {
    updateBossShieldField();
    showBanner("BOSS INCOMING", "ICE FIGHTER FORMATION", "#c9fbff", 1.65);
    popups.push({ x: centerX, y: centerY - 92, text: "BOSS", life: 1.2 });
    shake = Math.max(shake, 8);
  }
  return added;
}

function seedBlocks() {
  blocks = [];
  const cols = Math.max(6, Math.floor((w - grid.side * 2) / grid.cell));
  const gap = (w - grid.side * 2) / cols;
  const rows = 4;
  for (let row = 0; row < rows; row++) {
    const depth = rows - 1 - row;
    for (let col = 0; col < cols; col++) {
      if (isCorridorCell(col, cols, depth) || skipPackedCell(col, depth, .66)) continue;
      const { x, y } = cellPosition(col, row, gap);
      const type = randomBlockType();
      if (!canPlaceBlock(x, y, blocks, type)) continue;
      const value = blockHealth();
      blocks.push(makeBlock(x, y, value, type));
    }
  }
  fillRandomGaps(blocks, cols, gap, rows, 14);
  addCorridorAccents(blocks, cols, gap, rows);
  addAttachedPairs(blocks, .09);
  enforceSingleMegaBomb(blocks);
  enforceBombSpread(blocks);
  enforceUpgradeLimit(blocks);
  separateBlocks(blocks, 8);
  corridorDepth = rows;
}

function startOpeningDrop() {
  openingDrop = true;
  dropping = true;
  aiming = false;
  for (const block of blocks) {
    block.targetY = block.y;
    block.y -= random(240, 420);
  }
  hint.textContent = "宝石阵列正在落下...";
}

function startGame() {
  initAudio();
  score = 0; chain = 1; bestChain = 1; turn = 1; shake = 0; heat = 0; stormTimer = 0; choosingBuff = false;
  goldenShots = 0;
  defenseCharge = 0;
  defenseRequired = 100;
  defenseReady = false;
  defenseLayers = 0;
  defenseFlash = 0;
  defenseBlast = null;
  adAimBoost = false;
  watchingAd = false;
  shotHits = 0;
  praisedComboTier = 0;
  pendingComboPraise = null;
  comboPraiseToast = null;
  resetUpgrades();
  balls = []; particles = []; popups = []; banners = []; trails = []; shockwaves = []; beams = []; aimGuideCache = null; dropping = false; openingDrop = false;
  seedBlocks();
  running = true;
  startOpeningDrop();
  startCard.classList.add("hidden");
  gameOverCard.classList.add("hidden");
  upgradeCard.classList.add("hidden");
  rankPanel?.classList.add("hidden");
  rankBtn?.classList.remove("active");
  renderLeaderboard(startLeaderboard);
  updateAdAimButton();
  updateHud();
}

function updateHud() {
  scoreEl.textContent = String(score).padStart(6, "0");
  chainEl.textContent = `x${chain}`;
  heatFill.style.width = `${goldenShots > 0 ? 100 : heat}%`;
  stormText.textContent = goldenShots > 0 ? `GOLD x${goldenShots}` : `${Math.round(heat)}%`;
  heatBar.classList.toggle("ready", goldenShots > 0 || heat >= 100);
  heatBar.classList.toggle("golden", goldenShots > 0);
}

function updateBuffBar() {
  if (!buffBar) return;
  buffBar.innerHTML = upgradePool
    .filter(upgrade => upgrades[upgrade.id] > 0)
    .map(upgrade => `<div class="buff" title="${upgrade.name}"><em>${upgrade.icon}</em><strong>${upgrade.name}</strong><span>x${upgrades[upgrade.id]}</span></div>`)
    .join("");
}

function showBanner(title, subtitle, color = "#ffd76b", duration = 1.65) {
  banners.push({ title, subtitle, color, life: duration, maxLife: duration });
}

const leaderboardKey = "gem-pinball-leaderboard-v1";

function loadLeaderboard() {
  try {
    const value = JSON.parse(platform.storage.get(leaderboardKey) || "[]");
    return Array.isArray(value) ? value : [];
  } catch {
    return [];
  }
}

function saveLeaderboard(entries) {
  platform.storage.set(leaderboardKey, JSON.stringify(entries.slice(0, 10)));
}

function recordLeaderboardRun() {
  const entry = { score, bestChain, turn, at: Date.now() };
  const entries = [...loadLeaderboard(), entry]
    .sort((a, b) => b.score - a.score || b.bestChain - a.bestChain || b.turn - a.turn)
    .slice(0, 10);
  saveLeaderboard(entries);
  return { entries, rank: entries.indexOf(entry) + 1 || null };
}

function renderLeaderboard(target, entries = loadLeaderboard(), highlightRank = 0) {
  if (!target) return;
  const top = entries.slice(0, 5);
  if (!top.length) {
    target.innerHTML = "<h3>LOCAL RANK</h3><div class=\"rank-row\"><em>-</em><span>暂无记录</span><strong>PLAY</strong></div>";
    return;
  }
  target.innerHTML = [
    "<h3>LOCAL RANK</h3>",
    ...top.map((entry, index) => `
      <div class="rank-row${index + 1 === highlightRank ? " current" : ""}">
        <em>#${index + 1}</em>
        <span>x${entry.bestChain} · R${Math.max(1, entry.turn)}</span>
        <strong>${String(entry.score).padStart(6, "0")}</strong>
      </div>
    `)
  ].join("");
}

const comboPraiseTiers = [
  { hits: 5, title: "漂亮连击", subtitle: "GEM COMBO x5", color: "#8dffea" },
  { hits: 10, title: "宝石猎手", subtitle: "DOUBLE DIGITS", color: "#b8ff5f" },
  { hits: 20, title: "连锁大师", subtitle: "CRYSTAL RUSH", color: "#ffd95f" },
  { hits: 35, title: "粉碎风暴", subtitle: "SMASHING STORM", color: "#ff8cff" },
  { hits: 50, title: "超神弹射", subtitle: "UNSTOPPABLE", color: "#ffb15f" },
  { hits: 80, title: "宝石收割机", subtitle: "FIELD DOMINATION", color: "#5ff4ff" },
  { hits: 120, title: "传奇一击", subtitle: "LEGENDARY SHOT", color: "#ffd76b" }
];

function checkComboPraise() {
  const tier = comboPraiseTiers
    .filter(item => chain >= item.hits && item.hits > praisedComboTier)
    .pop();
  if (!tier) return;
  praisedComboTier = tier.hits;
  pendingComboPraise = { ...tier, chain };
}

function showComboPraiseSummary() {
  if (!pendingComboPraise) return;
  comboPraiseToast = { ...pendingComboPraise, life: 2.2, maxLife: 2.2 };
  pendingComboPraise = null;
  screenFlash = Math.max(screenFlash, .08);
  playSound("chain", Math.min(14, Math.ceil(comboPraiseToast.hits / 8)));
}

function updateAdAimButton() {
  if (!adAimBtn) return;
  adAimBtn.disabled = watchingAd || adAimBoost;
  adAimBtn.classList.toggle("active", adAimBoost);
  if (watchingAd) adAimBtn.innerHTML = "广告中<br /><span>请稍等</span>";
  else if (adAimBoost) adAimBtn.innerHTML = "延长线<br /><span>ON</span>";
  else adAimBtn.innerHTML = "看广告<br /><span>延长线</span>";
}

function completeAdAimReward() {
  watchingAd = false;
  adAimBoost = true;
  popups.push({ x: w / 2, y: h * .62, text: "AIM GUIDE x2", life: 1.15 });
  hint.textContent = "广告奖励：延长线翻倍，并开启反弹预测";
  playSound("chain", 8);
  updateAdAimButton();
}

function watchAdForAim() {
  if (watchingAd || adAimBoost) return;
  initAudio();
  watchingAd = true;
  hint.textContent = "广告播放中...完成后获得双倍延长线";
  updateAdAimButton();
  platform.delay(completeAdAimReward, 1200);
}

function launchPlan(golden = goldenShots > 0) {
  const count = golden ? 5 : 1 + Math.min(2, upgrades.multi);
  const speed = 690 * (1 + upgrades.speed * .08);
  const radius = golden ? 8 : 7;
  return Array.from({ length: count }, (_, i) => ({
    angle: angle + (i - (count - 1) / 2) * (golden ? .075 : .075),
    golden,
    radius,
    speed
  }));
}

function activateGoldenMissiles() {
  heat = 0;
  goldenShots = GOLDEN_SHOT_REWARD;
  upgradeCard.classList.add("hidden");
  choosingBuff = false;
  showBanner("XP OVERKILL", `GOLD SHOTS x${GOLDEN_SHOT_REWARD} · SCORE RUSH`, "#ffd76b", 1.85);
  screenFlash = Math.max(screenFlash, .62);
  popups.push({ x: w / 2, y: h * .55, text: `GOLD SHOTS x${GOLDEN_SHOT_REWARD}`, life: 1.35 });
  hint.textContent = `金色飞弹已充能 · 接下来 ${GOLDEN_SHOT_REWARD} 次发射都是五连弹`;
  playSound("chain", 10);
  updateHud();
}

function spawnBall() {
  if (!running || !aiming || dropping || choosingBuff) return;
  aiming = false;
  aimGuideCache = null;
  chain = 1; shotHits = 0; praisedComboTier = 0; pendingComboPraise = null; comboPraiseToast = null;
  const golden = goldenShots > 0;
  const plan = launchPlan(golden);
  if (golden) goldenShots -= 1;
  for (const shot of plan) {
    balls.push({ x: launchX, y: launchY, vx: Math.cos(shot.angle) * shot.speed, vy: Math.sin(shot.angle) * shot.speed, r: shot.radius, alive: true, pierce: upgrades.pierce * 2, saves: 4 + upgrades.speed, golden, wallBounces: 0, lastWallY: launchY });
  }
  playSound("launch");
  hint.textContent = golden ? `金色飞弹发射 · 剩余 ${goldenShots} 次` : "连锁反弹中";
  updateHud();
}

function burst(x, y, color, amount = 12) {
  const available = Math.max(0, maxParticles - particles.length);
  const budget = Math.min(amount, available);
  for (let i = 0; i < budget; i++) {
    const a = random(0, Math.PI * 2), speed = random(55, 220);
    const life = random(.24, .58);
    particles.push({
      x, y,
      vx: Math.cos(a) * speed,
      vy: Math.sin(a) * speed,
      life,
      max: life,
      r: random(2.5, 6.5),
      color,
      rot: a + Math.PI / 2,
      spin: random(-8, 8),
      kind: i % 3 === 0 ? "spark" : "shard"
    });
  }
}

function explodeBomb(block) {
  if (block.exploded) return;
  block.exploded = true;
  const radius = 118 + upgrades.blast * 18;
  let broken = 1;
  for (const nearby of blocks) {
    if (nearby === block || nearby.value <= 0 || Math.hypot(nearby.x - block.x, nearby.y - block.y) > radius) continue;
    nearby.value -= 3 + upgrades.blast;
    if (nearby.value <= 0) broken += 1;
    nearby.pulse = 1;
    burst(nearby.x, nearby.y, blockColor(nearby), 8);
  }
  block.value = 0;
  addBuffCharge(broken);
  shockwaves.push({ x: block.x, y: block.y, radius: 12, max: radius, life: .62, maxLife: .62 });
  burst(block.x, block.y, "#e6fbff", 52);
  playSound("break");
  shake = 16;
  popups.push({ x: block.x, y: block.y, text: "GEM BOOM!", life: .9 });
}

function triggerMegaBomb(block) {
  if (block.exploded) return;
  block.exploded = true;
  const radius = 236 + upgrades.blast * 24;
  screenFlash = .55;
  shake = 20;
  shockwaves.push({ x: block.x, y: block.y, radius: 18, max: radius, life: .78, maxLife: .78 });
  let cleared = 0;
  let broken = 1;
  for (const target of blocks) {
    if (target === block || target.value <= 0 || Math.hypot(target.x - block.x, target.y - block.y) > radius) continue;
    target.value -= 6 + upgrades.blast * 2;
    cleared += 1;
    if (target.value <= 0) broken += 1;
    target.pulse = 1;
    burst(target.x, target.y, blockColor(target), 11);
  }
  block.value = 0;
  addBuffCharge(broken);
  burst(block.x, block.y, "#efe3ff", 72);
  popups.push({ x: block.x, y: block.y - 16, text: "MEGA BOOM!", life: 1.25 });
  score += cleared * 90 * Math.max(1, chain);
  playSound("break");
  playSound("chain", 12);
}

function triggerHunterBomb(block) {
  if (block.exploded) return;
  block.exploded = true;
  const targets = blocks
    .filter(target => target !== block && target.value > 0)
    .sort((a, b) => {
      const ay = a.targetY ?? a.y;
      const by = b.targetY ?? b.y;
      if (by !== ay) return by - ay;
      return Math.abs(a.x - w / 2) - Math.abs(b.x - w / 2);
    });
  const target = targets[0];
  block.value = 0;
  burst(block.x, block.y, "#bafff4", 36);
  if (!target) {
    popups.push({ x: block.x, y: block.y - 16, text: "SEEKER READY", life: .85 });
    return;
  }
  beams.push({ x1: block.x, y1: block.y, x2: target.x, y2: target.y, life: .42, maxLife: .42 });
  target.value = 0;
  target.pulse = 1;
  burst(target.x, target.y, blockColor(target), 46);
  shockwaves.push({ x: target.x, y: target.y, radius: 10, max: 82, life: .5, maxLife: .5 });
  popups.push({ x: target.x, y: target.y - 18, text: "HUNT!", life: .9 });
  score += 520 * Math.max(1, chain);
  addBuffCharge(1);
  playSound("chain", 9);
}

function triggerSplitGem(block) {
  if (block.exploded) return;
  block.exploded = true;
  block.value = 0;
  const angle = -Math.PI / 2 + random(-.28, .28);
  const speed = 620 + random(-35, 55);
  balls.push({
    x: block.x,
    y: block.y,
    vx: Math.cos(angle) * speed,
    vy: Math.sin(angle) * speed,
    r: 6,
    alive: true,
    pierce: 0,
    saves: 2,
    golden: false,
    wallBounces: 0,
    lastWallY: block.y
  });
  burst(block.x, block.y, "#ffdfaa", 34);
  shockwaves.push({ x: block.x, y: block.y, radius: 8, max: 66, life: .4, maxLife: .4 });
  popups.push({ x: block.x, y: block.y - 18, text: "SPLIT +1", life: .95 });
  playSound("chain", 7);
}

function triggerMysteryGem(block) {
  if (block.exploded) return;
  const effects = ["bomb", "megaBomb", "hunterBomb", "split"];
  const effect = effects[Math.floor(Math.random() * effects.length)];
  popups.push({ x: block.x, y: block.y - 24, text: `? ${effect === "bomb" ? "爆" : effect === "megaBomb" ? "大爆" : effect === "hunterBomb" ? "追" : "分裂"}`, life: .95 });
  block.special = effect;
  block.exploded = false;
  if (effect === "bomb") explodeBomb(block);
  else if (effect === "megaBomb") triggerMegaBomb(block);
  else if (effect === "hunterBomb") triggerHunterBomb(block);
  else triggerSplitGem(block);
}

function triggerBossWing(block) {
  if (!block.boss || block.bossRole !== "wing" || block.wingBurst) return;
  block.wingBurst = true;
  const radius = 86;
  let broken = 0;
  shockwaves.push({ x: block.x, y: block.y, radius: 8, max: radius, life: .42, maxLife: .42 });
  for (const target of blocks) {
    if (target === block || target.value <= 0 || Math.hypot(target.x - block.x, target.y - block.y) > radius) continue;
    target.value -= target.boss ? 3 : 4;
    target.pulse = 1;
    burst(target.x, target.y, blockColor(target), target.boss ? 8 : 12);
    if (target.value <= 0) broken += 1;
  }
  popups.push({ x: block.x, y: block.y - 18, text: "WING BURST", life: .9 });
  score += (220 + broken * 80) * Math.max(1, chain);
  playSound("chain", 8);
  const core = blocks.find(target => target.boss && target.bossRole === "core" && target.value <= 0);
  if (core) defeatBoss(core);
}

function triggerBossNodeDown(block) {
  if (!block.boss || !isBossShieldRole(block.bossRole) || block.nodeDown) return;
  block.nodeDown = true;
  shockwaves.push({ x: block.x, y: block.y, radius: 8, max: 110, life: .52, maxLife: .52 });
  burst(block.x, block.y, "#ffd76b", 34);
  popups.push({ x: block.x, y: block.y - 22, text: "NODE DOWN", life: 1 });
  showBanner("NODE DOWN", `${activeBossShieldNodes().length} SHIELD NODES LEFT`, "#ffd76b", 1.05);
  shake = Math.max(shake, 10);
  playSound("chain", 8);
}

function defeatBoss(core) {
  const bossBlocks = blocks.filter(block => block.boss && block.value > 0);
  if (bossBlocks.length === 0 && core?.bossDefeated) return;
  if (core) core.bossDefeated = true;
  const centerX = core?.x ?? w / 2;
  const centerY = core?.y ?? grid.top + 72;
  for (const part of blocks) {
    if (!part.boss) continue;
    part.value = 0;
    part.pulse = 1;
    burst(part.x, part.y, blockColor(part), part.bossRole === "core" ? 42 : 18);
  }
  blocks = blocks.filter(block => !block.boss && block.value > 0);
  let swept = 0;
  for (const block of blocks) {
    if (block.value <= 0) continue;
    block.value = 0;
    block.pulse = 1;
    swept += 1;
    burst(block.x, block.y, blockColor(block), 12);
  }
  blocks = blocks.filter(block => block.value > 0);
  shockwaves.push({ x: centerX, y: centerY, radius: 20, max: 260, life: .9, maxLife: .9 });
  beams.push({ x1: centerX - 160, y1: centerY, x2: centerX + 160, y2: centerY, life: .55, maxLife: .55, color: "#ffd76b", width: 9 });
  score += (3600 + swept * 180) * Math.max(1, chain);
  screenFlash = Math.max(screenFlash, .72);
  shake = Math.max(shake, 24);
  showBanner("BOSS DESTROYED", "FIELD SWEEP · GOLD MISSILES READY", "#ffd76b", 1.9);
  popups.push({ x: centerX, y: centerY - 42, text: "BOSS DOWN!", life: 1.35 });
  if (swept > 0) popups.push({ x: w / 2, y: centerY + 18, text: `FIELD SWEEP x${swept}`, life: 1.2 });
  activateGoldenMissiles();
  playSound("break");
  playSound("chain", 14);
  updateHud();
}

function resolveBossBreaks() {
  const core = blocks.find(block => block.boss && block.bossRole === "core" && block.value <= 0);
  if (core) {
    defeatBoss(core);
    return;
  }
  if (blocks.some(block => block.boss && isBossShieldRole(block.bossRole) && block.value <= 0)) {
    for (const node of blocks) {
      if (node.boss && isBossShieldRole(node.bossRole) && node.value <= 0) triggerBossNodeDown(node);
    }
    weakenBossShield();
  }
  for (const wing of blocks) {
    if (wing.boss && wing.bossRole === "wing" && wing.value <= 0 && !wing.wingBurst) {
      triggerBossWing(wing);
    }
  }
}

function defenseLineY() {
  return launchY - 76;
}

function defenseLayerHeight() {
  const targetTop = Math.max(grid.top + 250, h * .26);
  return clamp((defenseLineY() - targetTop) / DEFENSE_MAX_LAYERS, 90, 260);
}

function addDefenseCharge(amount = 1) {
  if (amount <= 0 || defenseLayers >= DEFENSE_MAX_LAYERS) return;
  defenseCharge += amount;
  while (defenseCharge >= defenseRequired && defenseLayers < DEFENSE_MAX_LAYERS) {
    defenseCharge -= defenseRequired;
    defenseLayers += 1;
    defenseReady = defenseLayers > 0;
    defenseRequired = Math.ceil(defenseRequired * DEFENSE_GROWTH);
    defenseFlash = .7;
    showBanner("GEM GUARD +1", `PROTECTION LAYER x${defenseLayers}`, "#5bbcff", 1.45);
    popups.push({ x: w / 2, y: defenseLineY() - 54, text: `保护层 +1  当前 x${defenseLayers}`, life: 1.45 });
    playSound("chain", 7 + defenseLayers);
  }
  if (defenseLayers >= DEFENSE_MAX_LAYERS) defenseCharge = 0;
}

function triggerDefenseLine(emergency = false) {
  if (defenseLayers <= 0 || defenseBlast) return false;
  const layers = clamp(Math.floor(defenseLayers), 1, DEFENSE_MAX_LAYERS);
  defenseReady = false;
  defenseCharge = 0;
  defenseLayers = 0;
  defenseFlash = .9;
  shake = Math.max(shake, 12 + layers * 3);
  const y = defenseLineY();
  const layerHeight = defenseLayerHeight();
  defenseBlast = { layers, index: 0, timer: 0, y, layerHeight, cleared: 0, emergency };
  showBanner("GEM GUARD", `x${layers} LAYER CHAIN`, "#5bbcff", 1.35);
  popups.push({ x: w / 2, y: y - layers * layerHeight - 18, text: `GEM GUARD x${layers}!`, life: 1.35 });
  playSound("chain", 9 + layers);
  return true;
}

function resolveDefenseBlastLayer() {
  if (!defenseBlast || defenseBlast.index >= defenseBlast.layers) return;
  const { layers, index, y, layerHeight } = defenseBlast;
  const lineY = y - index * layerHeight;
  const layerTop = y - (index + 1) * layerHeight;
  const layerBottom = index === 0 ? y + 22 : y - index * layerHeight + 22;
  let cleared = 0;
  beams.push({ x1: 0, y1: lineY, x2: w, y2: lineY, life: .66, maxLife: .66, color: "#48b7ff", width: 7 + index });
  for (let x = 28; x < w; x += 72) {
    shockwaves.push({ x, y: lineY, radius: 8, max: 82 + index * 14, life: .56, maxLife: .56 });
    burst(x, lineY, "#8fdcff", 12 + index * 3);
  }
  for (const block of blocks) {
    if (block.value <= 0) continue;
    const blockY = block.targetY ?? block.y;
    const inLayer = blockY + blockLayoutRadius(block) >= layerTop && blockY - blockLayoutRadius(block) <= layerBottom;
    const crossesFailureLine = defenseBlast.emergency && blockY + blockLayoutRadius(block) >= launchY - 56;
    if (!inLayer && !crossesFailureLine) continue;
    block.value = 0;
    block.pulse = 1;
    cleared += 1;
    burst(block.x, block.y, blockColor(block), 14);
  }
  blocks = blocks.filter(block => block.value > 0);
  defenseBlast.cleared += cleared;
  score += cleared * 150 * Math.max(1, chain) * (index + 1);
  popups.push({ x: w / 2, y: lineY - 24, text: `LAYER ${index + 1}/${layers}`, life: .9 });
  defenseFlash = .75;
  shake = Math.max(shake, 13 + index * 4);
  playSound("break");
  playSound("chain", 7 + index);
  defenseBlast.index += 1;
  defenseBlast.timer = .18;
  if (defenseBlast.index >= defenseBlast.layers) {
    popups.push({ x: w / 2, y: y - layers * layerHeight - 20, text: `GUARD CLEARED ${defenseBlast.cleared}`, life: 1.1 });
    defenseBlast = null;
  }
  updateHud();
}

function testDefenseLayers() {
  const layers = clamp(parseInt(guardLayerInput?.value || "1", 10) || 1, 1, DEFENSE_MAX_LAYERS);
  defenseLayers = layers;
  defenseReady = true;
  defenseCharge = 0;
  defenseFlash = .8;
  triggerDefenseLine();
}

function addBuffCharge(breaks = 1) {
  if (breaks <= 0 || choosingBuff || goldenShots > 0) return;
  heat = Math.min(100, heat + breaks * (1 + upgrades.heat * .25 + upgrades.score * .1));
  if (heat >= 100) {
    heat = 100;
    activateGoldenMissiles();
  }
}

function hitBlock(block, ball) {
  shotHits += 1;
  addDefenseCharge(1);
  if (block.special === "bomb" && !block.exploded) {
    explodeBomb(block);
    score += 180 * chain;
    updateHud();
    return;
  }
  const damage = (1 + upgrades.power) * (ball.golden ? 2 : 1);
  block.value -= damage;
  block.pulse = 1;
  chain += 1;
  bestChain = Math.max(bestChain, chain);
  checkComboPraise();
  score += 10 * chain;
  shake = Math.min(8, shake + 1.4);
  popups.push({ x: block.x, y: block.y - 20, text: `+${10 * chain}`, life: .6 });
  burst(ball.x, ball.y, blockColor(block), 5);
  playSound("hit", chain);
  if (chain > 2 && chain % 8 === 0) playSound("chain", chain / 8);
  if (block.value <= 0) {
    if (block.special !== "megaBomb") addBuffCharge(1);
    score += 70 * chain * (1 + upgrades.score * .25);
    burst(block.x, block.y, blockColor(block), 22);
    playSound("break");
    if (block.boss && block.bossRole === "core") {
      defeatBoss(block);
      return;
    }
    if (block.boss && isBossShieldRole(block.bossRole)) {
      triggerBossNodeDown(block);
      weakenBossShield();
    }
    if (block.boss && block.bossRole === "wing") {
      triggerBossWing(block);
    }
    if (block.special === "megaBomb") {
      triggerMegaBomb(block);
      score += 900 * chain;
    }
    if (block.special === "hunterBomb") {
      triggerHunterBomb(block);
    }
    if (block.special === "split") {
      triggerSplitGem(block);
    }
    if (block.special === "mystery") {
      triggerMysteryGem(block);
    }
    if (block.special === "upgrade") {
      grantRandomUpgrade(block);
    }
    if (upgrades.shatter > 0) {
      const shatterDamage = Math.ceil(upgrades.shatter / 2);
      for (const nearby of blocks) {
        if (nearby === block || nearby.value <= 0 || Math.hypot(nearby.x - block.x, nearby.y - block.y) > 46) continue;
        nearby.value -= shatterDamage;
        nearby.pulse = 1;
      }
    }
    popups.push({ x: block.x, y: block.y, text: chain > 6 ? "CHAIN!" : "BREAK", life: .8 });
  }
  updateHud();
}

function addRow() {
  aimGuideCache = null;
  turn += 1;
  dropping = true;
  const dropBonus = dropGrowthBonus(turn);
  const dropDistance = rowDropDistance(turn);
  blocks.forEach(block => block.targetY += dropDistance);
  const reachesFailureLine = () => blocks.some(block => block.value > 0 && block.targetY > launchY - 52);
  if (reachesFailureLine() && (defenseLayers > 0 || defenseBlast)) {
    if (defenseLayers > 0) triggerDefenseLine(true);
    if (defenseBlast) {
      defenseBlast.emergency = true;
      resolveDefenseBlastLayer();
    }
  } else if (defenseLayers > 0 && blocks.some(block => block.targetY + blockLayoutRadius(block) > defenseLineY())) {
    triggerDefenseLine();
  }
  if (reachesFailureLine()) {
    endGame();
    return;
  }
  const cols = Math.max(6, Math.floor((w - grid.side * 2) / grid.cell));
  const gap = (w - grid.side * 2) / cols;
  const density = clamp(.66 + turn * .05, .7, .98);
  if (isBossTurn(turn)) {
    addPlaneBoss(dropDistance);
  } else {
    for (let col = 0; col < cols; col++) {
      if (isCorridorCell(col, cols, corridorDepth) || skipPackedCell(col, corridorDepth, density)) continue;
      const { x, y } = cellPosition(col, 0, gap);
      const type = randomBlockType();
      if (!canPlaceBlock(x, y, blocks, type)) continue;
      const block = makeBlock(x, y - dropDistance, blockHealth(), type);
      block.targetY = y;
      blocks.push(block);
    }
    const gapAttempts = Math.round(4 + turn * .85);
    for (let i = 0; i < gapAttempts; i++) {
      const x = random(grid.side + 18, w - grid.side - 18);
      const y = grid.top + random(-18, 18);
      const type = randomBlockType();
      if (isOpenCorridor(x, corridorDepth, cols, gap) || !canPlaceBlock(x, y, blocks, type)) continue;
      const block = makeBlock(x, y - dropDistance, blockHealth(), type);
      block.targetY = y;
      blocks.push(block);
    }
    if (corridorDepth % 2 === 1) {
      const center = (cols - 1) / 2 + Math.sin(corridorDepth * .62) * 1.1;
      const side = corridorDepth % 4 === 1 ? -1 : 1;
      const x = grid.side + gap * (center + .5 + side * random(.8, 1.25));
      const y = grid.top + random(-8, 8);
      const type = randomBlockType();
      if (canPlaceBlock(x, y, blocks, type)) {
        const block = makeBlock(x, y - dropDistance, blockHealth(), type);
        block.targetY = y;
        blocks.push(block);
      }
    }
    addAttachedPairs(blocks, clamp(.05 + turn * .012, .06, .2), blocks.filter(block => block.y < grid.top + 22));
  }
  enforceSingleMegaBomb(blocks);
  enforceBombSpread(blocks);
  enforceUpgradeLimit(blocks);
  separateBlocks(blocks, 8);
  corridorDepth += 1;
  hint.textContent = `宝石阵列下落中 · 压力 +${Math.round(dropBonus * 100)}%`;
}

function grantRandomUpgrade(block) {
  const upgrade = upgradePool[Math.floor(Math.random() * upgradePool.length)];
  upgrades[upgrade.id] += 1;
  updateBuffBar();
  popups.push({ x: block.x, y: block.y - 12, text: `获得 ${upgrade.name}`, life: 1.7 });
  popups.push({ x: w / 2, y: h * .58, text: `BUFF: ${upgrade.name}`, life: 1.25 });
  hint.textContent = `获得强化：${upgrade.name} · ${upgrade.description}`;
  playSound("chain", 8);
}

function endGame() {
  running = false; aiming = false;
  playSound("gameover");
  const leaderboard = recordLeaderboardRun();
  finalScore.textContent = `得分 ${score} · 最大连锁 x${bestChain}`;
  finalScore.textContent += leaderboard.rank ? ` · LOCAL RANK #${leaderboard.rank}` : " · OUTSIDE TOP 10";
  renderLeaderboard(gameOverLeaderboard, leaderboard.entries, leaderboard.rank);
  gameOverCard.classList.remove("hidden");
}

function localPoint(block, x, y) {
  const angle = -(block.type === "diamond" ? Math.PI / 4 + block.spin * .08 : block.spin * .08);
  const dx = x - block.x;
  const dy = y - block.y;
  return {
    x: dx * Math.cos(angle) - dy * Math.sin(angle),
    y: dx * Math.sin(angle) + dy * Math.cos(angle),
    angle
  };
}

function worldVector(angle, x, y) {
  const a = -angle;
  return {
    x: x * Math.cos(a) - y * Math.sin(a),
    y: x * Math.sin(a) + y * Math.cos(a)
  };
}

function closestPointOnSegment(px, py, ax, ay, bx, by) {
  const vx = bx - ax;
  const vy = by - ay;
  const lenSq = vx * vx + vy * vy || 1;
  const t = clamp(((px - ax) * vx + (py - ay) * vy) / lenSq, 0, 1);
  return { x: ax + vx * t, y: ay + vy * t };
}

function pointInPolygon(point, vertices) {
  let inside = false;
  for (let i = 0, j = vertices.length - 1; i < vertices.length; j = i++) {
    const a = vertices[i];
    const b = vertices[j];
    if ((a.y > point.y) !== (b.y > point.y) && point.x < (b.x - a.x) * (point.y - a.y) / (b.y - a.y || .001) + a.x) inside = !inside;
  }
  return inside;
}

function iceVertices(block, radius) {
  if (block.type === "triangle") return [
    { x: 0, y: -radius },
    { x: radius * .94, y: radius * .72 },
    { x: -radius * .94, y: radius * .72 }
  ];
  if (block.type === "pentagon") return Array.from({ length: 5 }, (_, i) => {
    const angle = -Math.PI / 2 + i * Math.PI * 2 / 5;
    return { x: Math.cos(angle) * radius * .96, y: Math.sin(angle) * radius * .96 };
  });
  return [
    { x: -radius * .72, y: -radius * .72 },
    { x: radius * .72, y: -radius * .72 },
    { x: radius * .72, y: radius * .72 },
    { x: -radius * .72, y: radius * .72 }
  ];
}

function ballBlockCollision(ball, block) {
  const radius = blockRadius(block);
  const broad = radius + ball.r + 1;
  if (Math.hypot(ball.x - block.x, ball.y - block.y) > broad) return null;
  if (block.type === "orb") {
    const dx = ball.x - block.x;
    const dy = ball.y - block.y;
    const distance = Math.hypot(dx, dy) || 1;
    if (distance >= broad) return null;
    return { nx: dx / distance, ny: dy / distance, depth: broad - distance };
  }

  const local = localPoint(block, ball.x, ball.y);
  const vertices = iceVertices(block, radius);
  let closest = null;
  let bestDistance = Infinity;
  for (let i = 0; i < vertices.length; i++) {
    const a = vertices[i];
    const b = vertices[(i + 1) % vertices.length];
    const point = closestPointOnSegment(local.x, local.y, a.x, a.y, b.x, b.y);
    const distance = Math.hypot(local.x - point.x, local.y - point.y);
    if (distance < bestDistance) {
      bestDistance = distance;
      closest = point;
    }
  }
  const inside = pointInPolygon(local, vertices);
  if (!inside && bestDistance > ball.r + 1.5) return null;
  let nx = local.x - closest.x;
  let ny = local.y - closest.y;
  let len = Math.hypot(nx, ny);
  if (len < .001) {
    nx = local.x;
    ny = local.y;
    len = Math.hypot(nx, ny) || 1;
  }
  const normal = worldVector(local.angle, nx / len, ny / len);
  return { nx: normal.x, ny: normal.y, depth: inside ? ball.r + 1 : ball.r - bestDistance + 1.5 };
}

function reflectBall(ball, block, collision) {
  const len = Math.hypot(collision.nx, collision.ny) || 1;
  const nx = collision.nx / len;
  const ny = collision.ny / len;
  const dot = ball.vx * nx + ball.vy * ny;
  ball.vx -= 2 * dot * nx;
  ball.vy -= 2 * dot * ny;
  const speed = Math.hypot(ball.vx, ball.vy);
  const targetSpeed = clamp(speed * 1.06, 720, 920);
  ball.vx = ball.vx / speed * targetSpeed;
  ball.vy = ball.vy / speed * targetSpeed;
  const push = Math.max(1, collision.depth);
  ball.x += nx * push;
  ball.y += ny * push;
}

function reflectVector(vx, vy, nx, ny) {
  const len = Math.hypot(nx, ny) || 1;
  const normalX = nx / len;
  const normalY = ny / len;
  const dot = vx * normalX + vy * normalY;
  return {
    x: vx - 2 * dot * normalX,
    y: vy - 2 * dot * normalY
  };
}

function aimGuidePoints(shot, length, predictive) {
  const guideAngle = shot.angle;
  if (!predictive) {
    return Array.from({ length: Math.ceil(length / 14) }, (_, i) => {
      const distance = 20 + i * 14;
      return {
        x: launchX + Math.cos(guideAngle) * distance,
        y: launchY + Math.sin(guideAngle) * distance,
        distance
      };
    }).filter(point => point.distance < length);
  }

  const points = [];
  const previewHealth = new Map(blocks.map(block => [block, block.value]));
  const probe = {
    x: launchX,
    y: launchY,
    vx: Math.cos(guideAngle) * shot.speed,
    vy: Math.sin(guideAngle) * shot.speed,
    r: shot.radius,
    saves: 0,
    golden: shot.golden
  };
  let travelled = 0;
  let cooldown = 0;
  const dt = 1 / 240;
  while (travelled < length && probe.y < h + 20) {
    guideBallInsideIce(probe, dt, true);
    const lastX = probe.x;
    const lastY = probe.y;
    probe.x += probe.vx * dt;
    probe.y += probe.vy * dt;
    travelled += Math.hypot(probe.x - lastX, probe.y - lastY);
    cooldown = Math.max(0, cooldown - Math.hypot(probe.x - lastX, probe.y - lastY));

    if (probe.x < probe.r + 12 || probe.x > w - probe.r - 12) {
      probe.vx *= -1;
      probe.x = clamp(probe.x, probe.r + 12, w - probe.r - 12);
      cooldown = 20;
    }
    if (probe.y < probe.r + 84) {
      probe.vy = Math.abs(probe.vy);
      probe.y = probe.r + 84;
      cooldown = 20;
    }
    if (cooldown <= 0) {
      for (const block of nearbyBlocks(probe.x, probe.y, 42)) {
        const currentValue = previewHealth.get(block) ?? block.value;
        if (currentValue <= 0) continue;
        const collision = ballBlockCollision(probe, block);
        if (!collision) continue;
        reflectBall(probe, block, collision);
        const damage = block.special === "bomb" ? currentValue : (1 + upgrades.power) * (probe.golden ? 2 : 1);
        previewHealth.set(block, currentValue - damage);
        cooldown = 28;
        break;
      }
    }
    if (travelled % 20 < Math.hypot(probe.x - lastX, probe.y - lastY)) points.push({ x: probe.x, y: probe.y, distance: travelled });
  }
  return points;
}

function cachedAimGuidePoints(shot, length, index) {
  const key = [
    index,
    shot.angle.toFixed(4),
    shot.golden,
    shot.radius,
    shot.speed,
    length,
    blocks.length,
    turn
  ].join("|");
  const cache = aimGuideCache ?? new Map();
  aimGuideCache = cache;
  if (!cache.has(key)) cache.set(key, aimGuidePoints(shot, length, true));
  return cache.get(key);
}

function iceFieldInfo(ball) {
  let weight = 0, cx = 0, cy = 0, bottom = 0, nearest = Infinity;
  for (const block of nearbyBlocks(ball.x, ball.y, 160)) {
    if (block.value <= 0) continue;
    const dx = block.x - ball.x;
    const dy = block.y - ball.y;
    const distance = Math.hypot(dx, dy);
    nearest = Math.min(nearest, distance - blockLayoutRadius(block));
    if (distance > 150) continue;
    const influence = 1 - distance / 150;
    weight += influence;
    cx += block.x * influence;
    cy += block.y * influence;
    bottom = Math.max(bottom, block.y + blockLayoutRadius(block));
  }
  if (!weight) return null;
  return { x: cx / weight, y: cy / weight, bottom, nearest, strength: Math.min(1, weight / 2.8) };
}

function guideBallInsideIce(ball, dt, preview = false) {
  const field = iceFieldInfo(ball);
  if (!field || field.nearest > 28 + upgrades.speed * 2) return;
  const speed = Math.hypot(ball.vx, ball.vy) || 1;
  const dx = field.x - ball.x;
  const dy = field.y - ball.y;
  const len = Math.hypot(dx, dy) || 1;
  const force = (150 + upgrades.speed * 22) * field.strength;
  ball.vx += dx / len * force * dt;
  ball.vy += dy / len * force * dt;
  const newSpeed = Math.hypot(ball.vx, ball.vy) || 1;
  const targetSpeed = clamp(Math.max(speed, newSpeed), 700, 900);
  ball.vx = ball.vx / newSpeed * targetSpeed;
  ball.vy = ball.vy / newSpeed * targetSpeed;

  const slippingOut = ball.y > field.y + 30 && ball.y < field.bottom + 48 + upgrades.speed * 4;
  if (ball.saves > 0 && ball.vy > 0 && field.nearest < 10 + upgrades.speed && slippingOut) {
    ball.saves -= 1;
    ball.vy = -Math.abs(ball.vy) * .9;
    ball.vx += (field.x - ball.x) * 2.2;
    if (!preview) popups.push({ x: ball.x, y: ball.y - 12, text: "REBOUND", life: .55 });
  }
}

function resolveWallLoop(ball) {
  const yDelta = Math.abs((ball.lastWallY ?? ball.y) - ball.y);
  ball.wallBounces = yDelta < 34 ? (ball.wallBounces || 0) + 1 : 1;
  ball.lastWallY = ball.y;
  if (ball.wallBounces < 7) return;
  const speed = Math.hypot(ball.vx, ball.vy) || 720;
  const vertical = Math.max(Math.abs(ball.vy), speed * .34);
  ball.vy = ball.y < h * .56 ? Math.abs(vertical) : -Math.abs(vertical);
  ball.vx = Math.sign(ball.vx || random(-1, 1)) * Math.sqrt(Math.max(1, speed * speed - ball.vy * ball.vy));
  ball.wallBounces = 0;
  popups.push({ x: ball.x, y: ball.y - 12, text: "ANGLE FIX", life: .55 });
}

function step(dt) {
  shake *= .88;
  screenFlash = Math.max(0, screenFlash - dt * 2.4);
  defenseFlash = Math.max(0, defenseFlash - dt * 1.8);
  if (defenseBlast) {
    defenseBlast.timer -= dt;
    if (defenseBlast.timer <= 0) resolveDefenseBlastLayer();
  }
  if (stormTimer > 0) {
    stormTimer = Math.max(0, stormTimer - dt);
    updateHud();
  }
  snowflakes.forEach(flake => {
    flake.phase += dt * .85;
    flake.x += Math.sin(flake.phase) * flake.sway * dt;
    flake.y += flake.vy * dt;
    if (flake.y > h + 8) Object.assign(flake, makeSnowflake());
    if (flake.x < -8) flake.x = w + 8;
    if (flake.x > w + 8) flake.x = -8;
  });
  const settleDistance = openingDrop ? 2.4 : .8;
  blocks.forEach(block => {
    block.pulse *= .86;
    block.spin += dt * .35;
    if (Math.abs(block.targetY - block.y) > settleDistance) {
      const dropSpeed = openingDrop ? 8.8 : 7.5;
      block.y += (block.targetY - block.y) * Math.min(1, dt * dropSpeed);
    } else {
      block.y = block.targetY;
    }
  });
  if (dropping && !openingDrop) separateBlocks(blocks, isMobile ? 1 : 2);
  if (dropping && blocks.every(block => Math.abs(block.y - block.targetY) <= settleDistance)) {
    blocks.forEach(block => { block.y = block.targetY; });
    dropping = false;
    openingDrop = false;
    aiming = !choosingBuff;
    hint.textContent = choosingBuff ? "能量已满 · 选择一个强化" : "左右拖动调整角度 · 点击发射";
  }

  rebuildBlockSpatialIndex();
  for (const ball of balls) {
    if (!ball.alive) continue;
    const substeps = 4;
    for (let s = 0; s < substeps; s++) {
      guideBallInsideIce(ball, dt / substeps);
      ball.x += ball.vx * dt / substeps;
      ball.y += ball.vy * dt / substeps;
      if (ball.x < ball.r + 12 || ball.x > w - ball.r - 12) {
        ball.vx *= -1;
        ball.x = clamp(ball.x, ball.r + 12, w - ball.r - 12);
      }
      if (ball.y < ball.r + 84) {
        ball.vy = Math.abs(ball.vy);
        ball.y = ball.r + 84;
      }
      for (const block of nearbyBlocks(ball.x, ball.y, 48)) {
        if (block.value <= 0 || block.hit > 0) continue;
        const collision = ballBlockCollision(ball, block);
        if (collision) {
          if (ball.pierce > 0) ball.pierce -= 1;
          else reflectBall(ball, block, collision);
          block.hit = .09;
          hitBlock(block, ball);
          break;
        }
      }
      guideBallInsideIce(ball, dt / substeps);
    }
    if (ball.y > h + 20) ball.alive = false;
    ball.trailTimer = (ball.trailTimer || 0) - dt;
    if (ball.trailTimer <= 0 && trails.length < maxTrails) {
      trails.push({ x: ball.x, y: ball.y, life: .18, golden: ball.golden });
      ball.trailTimer = isMobile ? .035 : .02;
    }
  }
  blocks.forEach(block => block.hit = Math.max(0, block.hit - dt));
  if (BOSS_ENABLED) {
    resolveBossBreaks();
    updateBossShieldField();
  }
  blocks = blocks.filter(block => block.value > 0);
  particles.forEach(p => { p.x += p.vx * dt; p.y += p.vy * dt; p.vy += 150 * dt; p.rot += p.spin * dt; p.life -= dt; });
  shockwaves.forEach(wave => { wave.life -= dt; wave.radius += (wave.max - wave.radius) * Math.min(1, dt * 9); });
  beams.forEach(beam => { beam.life -= dt; });
  popups.forEach(p => { p.y -= 32 * dt; p.life -= dt; });
  banners.forEach(banner => { banner.life -= dt; });
  if (comboPraiseToast) comboPraiseToast.life -= dt;
  trails.forEach(p => p.life -= dt);
  particles = particles.filter(p => p.life > 0);
  shockwaves = shockwaves.filter(wave => wave.life > 0);
  beams = beams.filter(beam => beam.life > 0);
  popups = popups.filter(p => p.life > 0);
  banners = banners.filter(banner => banner.life > 0);
  if (comboPraiseToast && comboPraiseToast.life <= 0) comboPraiseToast = null;
  trails = trails.filter(p => p.life > 0);

  if (!aiming && balls.length && balls.every(ball => !ball.alive)) {
    balls = [];
    showComboPraiseSummary();
    if (choosingBuff) {
      hint.textContent = "能量已满 · 选择一个强化";
    } else addRow();
  }
}

function drawDiamond(block, radius) {
  ctx.save();
  ctx.translate(block.x, block.y);
  ctx.rotate(Math.PI / 4 + block.spin * .08);
  ctx.fillRect(-radius * .72, -radius * .72, radius * 1.44, radius * 1.44);
  ctx.restore();
}

function drawTriangle(block, radius) {
  ctx.save();
  ctx.translate(block.x, block.y);
  ctx.rotate(block.spin * .08);
  ctx.beginPath();
  ctx.moveTo(0, -radius);
  ctx.lineTo(radius * .94, radius * .72);
  ctx.lineTo(-radius * .94, radius * .72);
  ctx.closePath();
  ctx.fill();
  ctx.restore();
}

function traceIceShape(block, radius, offsetX = 0, offsetY = 0) {
  ctx.beginPath();
  if (block.type === "orb") {
    ctx.arc(block.x + offsetX, block.y + offsetY, radius, 0, Math.PI * 2);
    return;
  }
  ctx.save();
  ctx.translate(block.x + offsetX, block.y + offsetY);
  ctx.rotate(block.type === "diamond" ? Math.PI / 4 + block.spin * .08 : block.spin * .08);
  if (block.type === "triangle") {
    ctx.moveTo(0, -radius);
    ctx.lineTo(radius * .94, radius * .72);
    ctx.lineTo(-radius * .94, radius * .72);
  } else if (block.type === "pentagon") {
    for (let i = 0; i < 5; i++) {
      const angle = -Math.PI / 2 + i * Math.PI * 2 / 5;
      const x = Math.cos(angle) * radius * .96;
      const y = Math.sin(angle) * radius * .96;
      if (i === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    }
  } else {
    ctx.rect(-radius * .72, -radius * .72, radius * 1.44, radius * 1.44);
  }
  ctx.closePath();
  ctx.restore();
}

function drawSimpleGem(block, radius) {
  const color = blockColor(block);
  const palette = icePalette(block);
  ctx.save();
  ctx.shadowColor = color;
  ctx.shadowBlur = 9 + block.pulse * 10;
  const face = ctx.createLinearGradient(block.x - radius, block.y - radius, block.x + radius, block.y + radius);
  face.addColorStop(0, palette[0]);
  face.addColorStop(.55, palette[1]);
  face.addColorStop(1, palette[2]);
  ctx.fillStyle = face;
  traceIceShape(block, radius);
  ctx.fill();
  ctx.shadowBlur = 0;
  ctx.strokeStyle = palette[3];
  ctx.lineWidth = 1.7;
  ctx.stroke();
  ctx.strokeStyle = "rgba(255,255,255,.48)";
  ctx.lineWidth = .8;
  ctx.beginPath();
  ctx.moveTo(block.x - radius * .58, block.y - radius * .42);
  ctx.lineTo(block.x + radius * .48, block.y + radius * .18);
  ctx.stroke();
  ctx.restore();
}

function drawIceBlock(block, radius) {
  const color = blockColor(block);
  const damage = 1 - block.value / block.max;
  const toughness = clamp(block.max / 18, 0, 1);
  ctx.save();

  // Neon gem style: dark glass thickness below, bright refractive face on top.
  const depthLayers = renderQuality === "mobile" ? 4 : 10;
  for (let depth = depthLayers; depth >= 1; depth--) {
    const ratio = depth / depthLayers;
    ctx.fillStyle = `rgba(8, 17, 38, ${.18 + ratio * (.18 + toughness * .1)})`;
    traceIceShape(block, radius, depth * (.75 + toughness * .16), depth * (1.05 + toughness * .22));
    ctx.fill();
  }

  ctx.shadowColor = color;
  ctx.shadowBlur = 18 + block.pulse * 24 + toughness * 10;
  const face = ctx.createLinearGradient(block.x - radius, block.y - radius, block.x + radius, block.y + radius);
  const palette = icePalette(block);
  face.addColorStop(0, palette[0]);
  face.addColorStop(.42, palette[1]);
  face.addColorStop(.7, block.shieldedByLine ? "rgba(255, 226, 92, .66)" : "rgba(255, 255, 255, .18)");
  face.addColorStop(1, palette[2]);
  ctx.fillStyle = face;
  traceIceShape(block, radius);
  ctx.fill();
  ctx.shadowBlur = 0;

  ctx.globalAlpha = .32;
  ctx.fillStyle = "#ffffff";
  traceIceShape(block, radius * .76, -radius * .08, -radius * .12);
  ctx.fill();
  ctx.globalAlpha = 1;

  ctx.strokeStyle = palette[3];
  ctx.lineWidth = block.shieldedByLine ? 2.8 : 2 + toughness * .75;
  ctx.stroke();

  ctx.strokeStyle = color;
  ctx.lineWidth = .9;
  ctx.shadowColor = color;
  ctx.shadowBlur = 10;
  traceIceShape(block, radius + 3);
  ctx.stroke();
  ctx.shadowBlur = 0;

  if (block.shieldedByLine) {
    ctx.strokeStyle = "rgba(255, 224, 96, .86)";
    ctx.lineWidth = 3.2;
    ctx.shadowColor = "#ffd76b";
    ctx.shadowBlur = 18;
    traceIceShape(block, radius + 6);
    ctx.stroke();
    ctx.shadowBlur = 0;
  }

  // Clip the internal facets to the current gem silhouette.
  traceIceShape(block, radius - 1);
  ctx.clip();

  const coreGlow = ctx.createRadialGradient(block.x - radius * .18, block.y - radius * .22, radius * .08, block.x, block.y, radius * .92);
  coreGlow.addColorStop(0, "rgba(255,255,255,.62)");
  coreGlow.addColorStop(.34, "rgba(255,255,255,.18)");
  coreGlow.addColorStop(1, "rgba(255,255,255,0)");
  ctx.fillStyle = coreGlow;
  ctx.fillRect(block.x - radius, block.y - radius, radius * 2, radius * 2);

  ctx.fillStyle = "rgba(255,255,255,.24)";
  ctx.beginPath();
  ctx.moveTo(block.x - radius * .9, block.y - radius * .78);
  ctx.lineTo(block.x + radius * .02, block.y - radius * .9);
  ctx.lineTo(block.x - radius * .28, block.y + radius * .08);
  ctx.closePath();
  ctx.fill();

  ctx.fillStyle = "rgba(0, 0, 0, .14)";
  ctx.beginPath();
  ctx.moveTo(block.x + radius * .08, block.y - radius * .82);
  ctx.lineTo(block.x + radius * .92, block.y + radius * .28);
  ctx.lineTo(block.x - radius * .22, block.y + radius * .14);
  ctx.closePath();
  ctx.fill();

  ctx.strokeStyle = "rgba(255,255,255,.82)";
  ctx.lineWidth = 1.15;
  ctx.beginPath();
  ctx.moveTo(block.x - radius * .62, block.y - radius * .45);
  ctx.lineTo(block.x + radius * .02, block.y - radius * .72);
  ctx.lineTo(block.x + radius * .54, block.y - radius * .18);
  ctx.stroke();

  ctx.strokeStyle = `rgba(255, 255, 255, ${.2 + toughness * .22})`;
  ctx.lineWidth = .9;
  ctx.beginPath();
  ctx.moveTo(block.x - radius * .72, block.y + radius * .25);
  ctx.lineTo(block.x + radius * .66, block.y - radius * .5);
  ctx.moveTo(block.x - radius * .42, block.y - radius * .65);
  ctx.lineTo(block.x + radius * .28, block.y + radius * .58);
  ctx.moveTo(block.x - radius * .08, block.y - radius * .08);
  ctx.lineTo(block.x + radius * .74, block.y + radius * .48);
  ctx.stroke();

  if (renderQuality === "desktop") {
    ctx.globalCompositeOperation = "screen";
    ctx.strokeStyle = "rgba(255,255,255,.26)";
    ctx.lineWidth = .75;
    for (let i = 0; i < 3; i++) {
      const offset = (i - 1) * radius * .24;
      ctx.beginPath();
      ctx.moveTo(block.x - radius * .86, block.y + offset);
      ctx.quadraticCurveTo(block.x - radius * .05, block.y - radius * .34 + offset * .2, block.x + radius * .78, block.y + offset * .42);
      ctx.stroke();
    }
    ctx.globalCompositeOperation = "source-over";
  }

  ctx.shadowColor = color;
  ctx.shadowBlur = 12;
  ctx.fillStyle = "rgba(255,255,255,.5)";
  ctx.beginPath();
  ctx.arc(block.x - radius * .28, block.y - radius * .34, radius * .1, 0, Math.PI * 2);
  ctx.fill();
  ctx.fillStyle = "rgba(255,255,255,.38)";
  ctx.beginPath();
  ctx.arc(block.x + radius * .34, block.y + radius * .18, radius * .055, 0, Math.PI * 2);
  ctx.fill();
  ctx.shadowBlur = 0;

  if (damage > .18) {
    ctx.strokeStyle = `rgba(255, 255, 255, ${.55 + damage * .4})`;
    ctx.lineWidth = 1.25 + damage * 1.05;
    ctx.beginPath();
    ctx.moveTo(block.x + radius * .08, block.y - radius * .72);
    ctx.lineTo(block.x - radius * .12, block.y - radius * .02);
    ctx.lineTo(block.x + radius * .48, block.y + radius * .46);
    ctx.moveTo(block.x - radius * .12, block.y - radius * .02);
    ctx.lineTo(block.x - radius * .58, block.y + radius * .26);
    ctx.moveTo(block.x - radius * .12, block.y - radius * .02);
    ctx.lineTo(block.x + radius * .16, block.y + radius * .66);
    ctx.stroke();
  }
  ctx.restore();
}

function drawMysteryGift(block, radius) {
  const boxW = radius * 1.62;
  const boxH = radius * 1.26;
  const boxX = block.x - boxW / 2;
  const boxY = block.y - boxH * .08;
  const lidY = boxY - radius * .5;
  ctx.save();
  ctx.translate(block.x, block.y);
  ctx.rotate(block.spin * .045);
  ctx.translate(-block.x, -block.y);

  ctx.shadowColor = "#ffd66b";
  ctx.shadowBlur = 20 + block.pulse * 18;
  const body = ctx.createLinearGradient(boxX, boxY, boxX + boxW, boxY + boxH);
  body.addColorStop(0, "#ff85c8");
  body.addColorStop(.45, "#c75aff");
  body.addColorStop(1, "#682bc9");
  ctx.fillStyle = body;
  ctx.beginPath();
  ctx.roundRect(boxX, boxY, boxW, boxH, radius * .17);
  ctx.fill();

  const lid = ctx.createLinearGradient(boxX, lidY, boxX + boxW, lidY + radius * .52);
  lid.addColorStop(0, "#ffd88c");
  lid.addColorStop(.46, "#ff9d4d");
  lid.addColorStop(1, "#e85b8a");
  ctx.fillStyle = lid;
  ctx.beginPath();
  ctx.roundRect(boxX - radius * .1, lidY, boxW + radius * .2, radius * .52, radius * .13);
  ctx.fill();

  ctx.shadowBlur = 0;
  ctx.fillStyle = "rgba(255, 245, 180, .92)";
  ctx.fillRect(block.x - radius * .15, lidY - radius * .05, radius * .3, boxH + radius * .6);
  ctx.fillRect(boxX - radius * .02, boxY + boxH * .43, boxW + radius * .04, radius * .18);

  ctx.strokeStyle = "rgba(255, 250, 220, .92)";
  ctx.lineWidth = 1.7;
  ctx.beginPath();
  ctx.roundRect(boxX, boxY, boxW, boxH, radius * .17);
  ctx.stroke();
  ctx.beginPath();
  ctx.roundRect(boxX - radius * .1, lidY, boxW + radius * .2, radius * .52, radius * .13);
  ctx.stroke();

  ctx.fillStyle = "#fff3a4";
  ctx.beginPath();
  ctx.ellipse(block.x - radius * .2, lidY - radius * .12, radius * .25, radius * .14, -.55, 0, Math.PI * 2);
  ctx.ellipse(block.x + radius * .2, lidY - radius * .12, radius * .25, radius * .14, .55, 0, Math.PI * 2);
  ctx.fill();
  ctx.fillStyle = "#ffffff";
  ctx.beginPath();
  ctx.arc(block.x - radius * .3, boxY + radius * .2, radius * .08, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();
}

function specialGemLabel(block) {
  if (block.special === "bomb") return { text: "爆", color: "#ff4b4b", fill: "rgba(255, 50, 50, .22)" };
  if (block.special === "megaBomb") return { text: "大爆", color: "#ff8cff", fill: "rgba(228, 95, 255, .2)" };
  if (block.special === "hunterBomb") return { text: "追", color: "#35ffd4", fill: "rgba(53, 255, 212, .18)" };
  if (block.special === "split") return { text: "裂", color: "#ffb15f", fill: "rgba(255, 177, 95, .22)" };
  if (block.special === "mystery") return null;
  if (block.special === "upgrade") return { text: "UP", color: "#ffd95f", fill: "rgba(255, 217, 95, .22)" };
  if (block.special) return { text: "SP", color: blockColor(block), fill: "rgba(255,255,255,.14)" };
  return null;
}

function drawSpecialGemMarker(block, radius) {
  const label = specialGemLabel(block);
  if (!label) return;
  const color = label.color;
  ctx.save();
  ctx.translate(block.x, block.y);
  ctx.shadowColor = color;
  ctx.shadowBlur = 12;

  const badgeW = label.text.length > 2 ? 28 : 22;
  const badgeH = 13;
  const badgeY = -radius - 13;
  ctx.fillStyle = label.fill;
  ctx.strokeStyle = color;
  ctx.lineWidth = 1.4;
  ctx.beginPath();
  ctx.roundRect(-badgeW / 2, badgeY, badgeW, badgeH, 4);
  ctx.fill();
  ctx.stroke();

  ctx.shadowBlur = 7;
  ctx.fillStyle = "#fff8e8";
  ctx.font = label.text.length > 2 ? "900 8px monospace" : "900 9px monospace";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillText(label.text, 0, badgeY + badgeH / 2 + .5);
  ctx.restore();
}

function drawBossFormation() {
  const bossBlocks = blocks.filter(block => block.boss && block.value > 0);
  if (bossBlocks.length < 4) return;
  const minX = Math.min(...bossBlocks.map(block => block.x));
  const maxX = Math.max(...bossBlocks.map(block => block.x));
  const minY = Math.min(...bossBlocks.map(block => block.y));
  const maxY = Math.max(...bossBlocks.map(block => block.y));
  const centerX = bossBlocks.reduce((sum, block) => sum + block.x, 0) / bossBlocks.length;
  const centerY = bossBlocks.reduce((sum, block) => sum + block.y, 0) / bossBlocks.length;
  const core = bossBlocks.find(block => block.bossRole === "core");
  const shieldNodes = bossShieldPolygon();
  const pulse = .65 + Math.sin(performance.now() * .006) * .18;

  ctx.save();
  ctx.shadowColor = "#ffd76b";
  ctx.shadowBlur = 24;
  ctx.strokeStyle = `rgba(255, 215, 98, ${.55 + pulse * .3})`;
  ctx.fillStyle = `rgba(111, 62, 170, ${.1 + pulse * .04})`;
  ctx.lineWidth = 3.2;
  ctx.beginPath();
  ctx.moveTo(centerX, minY - 34);
  ctx.lineTo(maxX + 46, centerY - 4);
  ctx.lineTo(centerX + 28, centerY + 15);
  ctx.lineTo(centerX + 22, maxY + 35);
  ctx.lineTo(centerX, maxY + 20);
  ctx.lineTo(centerX - 22, maxY + 35);
  ctx.lineTo(centerX - 28, centerY + 15);
  ctx.lineTo(minX - 46, centerY - 4);
  ctx.closePath();
  ctx.fill();
  ctx.stroke();

  if (shieldNodes.length >= 2) {
    ctx.shadowColor = "#ffd76b";
    ctx.shadowBlur = 22;
    ctx.strokeStyle = `rgba(255, 220, 86, ${bossShieldActive() ? .86 : .45})`;
    ctx.lineWidth = bossShieldActive() ? 4.2 : 2.3;
    ctx.setLineDash(bossShieldActive() ? [] : [8, 7]);
    if (shieldNodes.length >= 3) {
      ctx.fillStyle = `rgba(255, 215, 98, ${bossShieldActive() ? .1 : .035})`;
      ctx.beginPath();
      shieldNodes.forEach((node, index) => {
        if (index === 0) ctx.moveTo(node.x, node.y);
        else ctx.lineTo(node.x, node.y);
      });
      ctx.closePath();
      ctx.fill();
    }
    ctx.beginPath();
    shieldNodes.forEach((node, index) => {
      if (index === 0) ctx.moveTo(node.x, node.y);
      else ctx.lineTo(node.x, node.y);
    });
    ctx.closePath();
    ctx.stroke();
    ctx.strokeStyle = `rgba(255, 252, 211, ${bossShieldActive() ? .48 : .2})`;
    ctx.lineWidth = 1.1;
    ctx.beginPath();
    shieldNodes.forEach((node, index) => {
      const next = shieldNodes[(index + 1) % shieldNodes.length];
      const mx = (node.x + next.x) / 2 + Math.sin(performance.now() * .01 + index) * 8;
      const my = (node.y + next.y) / 2 + Math.cos(performance.now() * .012 + index) * 8;
      ctx.moveTo(node.x, node.y);
      ctx.quadraticCurveTo(mx, my, next.x, next.y);
    });
    ctx.stroke();
    ctx.setLineDash([]);

    if (core) {
      ctx.strokeStyle = `rgba(255, 242, 168, ${bossShieldActive() ? .46 : .22})`;
      ctx.lineWidth = 1.4;
      ctx.beginPath();
      for (const node of shieldNodes) {
        ctx.moveTo(node.x, node.y);
        ctx.lineTo(core.x, core.y);
      }
      ctx.stroke();
    }

    if (bossShieldActive()) {
      ctx.shadowBlur = 10;
      ctx.fillStyle = "rgba(255, 235, 150, .86)";
      ctx.font = "900 10px monospace";
      ctx.textAlign = "center";
      ctx.fillText("x2 HP FIELD", centerX, centerY + 58);
    }
  }

  ctx.shadowBlur = 12;
  ctx.strokeStyle = "rgba(255, 245, 180, .72)";
  ctx.lineWidth = 1.4;
  ctx.beginPath();
  ctx.moveTo(centerX, minY - 22);
  ctx.lineTo(centerX, maxY + 20);
  ctx.moveTo(minX - 26, centerY - 2);
  ctx.lineTo(maxX + 26, centerY - 2);
  ctx.stroke();

  ctx.shadowBlur = 18;
  ctx.fillStyle = "rgba(255, 215, 98, .92)";
  ctx.font = "900 15px monospace";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillText("BOSS", centerX, minY - 54);

  ctx.strokeStyle = "rgba(255, 96, 96, .9)";
  ctx.lineWidth = 3;
  ctx.shadowColor = "#ff5252";
  ctx.shadowBlur = 20;
  ctx.beginPath();
  ctx.arc(core?.x ?? centerX, core?.y ?? centerY, 24 + Math.sin(performance.now() * .008) * 3, 0, Math.PI * 2);
  ctx.stroke();
  ctx.shadowBlur = 0;
  ctx.fillStyle = "rgba(255, 96, 96, .9)";
  ctx.font = "900 10px monospace";
  ctx.fillText("CORE", core?.x ?? centerX, (core?.y ?? centerY) + 34);
  ctx.restore();
}

function drawArcticBackground() {
  const time = performance.now() * .001;
  const bg = ctx.createLinearGradient(0, 0, 0, h);
  bg.addColorStop(0, "#08263a");
  bg.addColorStop(.42, "#041522");
  bg.addColorStop(1, "#01070d");
  ctx.fillStyle = bg;
  ctx.fillRect(-12, -12, w + 24, h + 24);

  const aurora = ctx.createLinearGradient(0, 0, w, h * .34);
  aurora.addColorStop(0, "rgba(61, 255, 214, 0)");
  aurora.addColorStop(.35, "rgba(86, 220, 255, .18)");
  aurora.addColorStop(.58, "rgba(177, 112, 255, .12)");
  aurora.addColorStop(1, "rgba(61, 255, 214, 0)");
  ctx.save();
  ctx.globalAlpha = .8;
  ctx.fillStyle = aurora;
  ctx.beginPath();
  ctx.moveTo(-30, 40 + Math.sin(time) * 10);
  ctx.bezierCurveTo(w * .25, 10 + Math.sin(time * 1.6) * 18, w * .56, 90, w + 30, 44 + Math.cos(time * 1.2) * 16);
  ctx.lineTo(w + 30, 170);
  ctx.bezierCurveTo(w * .58, 124, w * .24, 132 + Math.sin(time * 1.4) * 12, -30, 160);
  ctx.closePath();
  ctx.fill();
  ctx.restore();

  ctx.save();
  ctx.globalAlpha = .12;
  ctx.strokeStyle = "#bff8ff";
  ctx.lineWidth = 1;
  for (let i = 0; i < 9; i++) {
    const x = (i + .5) * w / 9 + Math.sin(time * .6 + i) * 8;
    ctx.beginPath();
    ctx.moveTo(x, 86);
    ctx.lineTo(x + Math.sin(i * 1.7) * 34, h * .58);
    ctx.lineTo(x + Math.cos(i * 1.2) * 62, h);
    ctx.stroke();
  }
  ctx.restore();

  const floor = ctx.createLinearGradient(0, launchY - 34, 0, h + 20);
  floor.addColorStop(0, "rgba(93, 211, 255, .08)");
  floor.addColorStop(.2, "rgba(132, 238, 255, .18)");
  floor.addColorStop(1, "rgba(2, 9, 15, .62)");
  ctx.fillStyle = floor;
  ctx.fillRect(-12, launchY - 36, w + 24, h - launchY + 60);
}

function draw() {
  ctx.clearRect(0, 0, w, h);
  ctx.save();
  ctx.translate(random(-shake, shake), random(-shake, shake));
  drawArcticBackground();
  if (stormTimer > 0) {
    ctx.fillStyle = `rgba(138, 225, 255, ${.05 + Math.sin(performance.now() * .01) * .025})`;
    ctx.fillRect(-12, -12, w + 24, h + 24);
  }
  if (screenFlash > 0) {
    ctx.fillStyle = `rgba(221, 238, 255, ${screenFlash * .58})`;
    ctx.fillRect(-12, -12, w + 24, h + 24);
  }

  for (const flake of snowflakes) {
    ctx.globalAlpha = flake.alpha;
    ctx.fillStyle = "#e8fbff";
    ctx.beginPath();
    ctx.arc(flake.x, flake.y, flake.r, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalAlpha = 1;

  ctx.strokeStyle = "rgba(118,245,219,.13)";
  ctx.setLineDash([4, 6]); ctx.beginPath(); ctx.moveTo(0, 90); ctx.lineTo(w, 90); ctx.stroke(); ctx.setLineDash([]);
  if (defenseCharge > 0 || defenseLayers > 0 || defenseFlash > 0) {
    const y = defenseLineY();
    const layerHeight = defenseLayerHeight();
    const chargeRatio = defenseLayers >= DEFENSE_MAX_LAYERS ? 1 : defenseCharge / defenseRequired;
    const pulse = .6 + Math.sin(performance.now() * .008) * .25 + defenseFlash * .65;
    ctx.globalAlpha = defenseLayers > 0 ? 1 : Math.max(.24, defenseFlash);
    ctx.strokeStyle = "rgba(91, 190, 255, .18)";
    ctx.lineWidth = 5;
    ctx.shadowBlur = 0;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w, y);
    ctx.stroke();
    ctx.strokeStyle = `rgba(91, 190, 255, ${clamp(pulse, .2, 1)})`;
    ctx.lineWidth = defenseLayers > 0 ? 4 + defenseLayers : 7;
    ctx.shadowColor = "#5bbcff";
    ctx.shadowBlur = defenseLayers > 0 ? 16 + defenseLayers * 5 : 10 + defenseFlash * 24;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w * chargeRatio, y);
    ctx.stroke();
    ctx.shadowBlur = 0;
    ctx.textAlign = "center";
    ctx.shadowColor = "#5bbcff";
    ctx.shadowBlur = 12;
    ctx.fillStyle = "rgba(210, 248, 255, .95)";
    ctx.font = "900 18px monospace";
    ctx.fillText(`GUARD x${defenseLayers}`, w / 2, y - 30);
    ctx.shadowBlur = 0;
    if (defenseLayers < DEFENSE_MAX_LAYERS) {
      ctx.font = "800 11px monospace";
      ctx.fillText(`NEXT ${Math.floor(chargeRatio * 100)}%`, w / 2, y - 13);
    } else {
      ctx.font = "900 12px monospace";
      ctx.fillText("MAX LAYER", w / 2, y - 13);
    }
    ctx.globalAlpha = 1;
  }
  ctx.fillStyle = "rgba(255,82,82,.14)"; ctx.fillRect(0, launchY - 40, w, 2);

  if (BOSS_ENABLED) drawBossFormation();
  for (const block of blocks) {
    const radius = blockRadius(block) + block.pulse * 4;
    if (block.special === "mystery") drawMysteryGift(block, radius);
    else if (isMobile && blocks.length > 28) drawSimpleGem(block, radius);
    else drawIceBlock(block, radius);
    ctx.font = "900 13px monospace"; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.lineWidth = 3;
    ctx.strokeStyle = "rgba(3, 14, 28, .72)";
    ctx.strokeText(block.value, block.x, block.y + 1);
    ctx.fillStyle = "#f3feff";
    ctx.shadowColor = blockColor(block);
    ctx.shadowBlur = 6;
    ctx.fillText(block.value, block.x, block.y + 1);
    ctx.shadowBlur = 0;
    if (BOSS_ENABLED && block.boss) {
      ctx.shadowColor = "#ffd76b";
      ctx.shadowBlur = 14;
      ctx.fillStyle = "#fff1a8";
      ctx.font = "900 7px monospace";
      if (block.bossRole === "core") {
        ctx.fillText("CORE", block.x, block.y - 13);
      } else if (isBossShieldRole(block.bossRole)) {
        ctx.fillText("NODE", block.x, block.y - 13);
      } else if (block.bossRole === "wing") {
        ctx.fillText("WING", block.x, block.y - 13);
      } else if (block.shieldedByLine) {
        ctx.fillText("x2", block.x, block.y - 13);
      }
      ctx.strokeStyle = "rgba(255, 215, 98, .88)";
      ctx.lineWidth = isBossShieldRole(block.bossRole) ? 3 : 1.6;
      ctx.beginPath();
      ctx.arc(block.x, block.y, radius + (isBossShieldRole(block.bossRole) ? 8 : 4), 0, Math.PI * 2);
      ctx.stroke();
      ctx.shadowBlur = 0;
    }
    drawSpecialGemMarker(block, radius);
  }

  for (const trail of trails) {
    ctx.globalAlpha = trail.life / .18 * .55;
    ctx.fillStyle = trail.golden ? "#ffd76b" : "#fff";
    ctx.beginPath(); ctx.arc(trail.x, trail.y, 4, 0, Math.PI * 2); ctx.fill();
  }
  ctx.globalAlpha = 1;
  for (const beam of beams) {
    const alpha = beam.life / beam.maxLife;
    ctx.globalAlpha = alpha;
    ctx.strokeStyle = beam.color || "#8dffea";
    ctx.lineWidth = beam.width || 4;
    ctx.shadowColor = beam.color || "#8dffea";
    ctx.shadowBlur = 18;
    ctx.beginPath();
    ctx.moveTo(beam.x1, beam.y1);
    ctx.lineTo(beam.x2, beam.y2);
    ctx.stroke();
    ctx.strokeStyle = "rgba(255,255,255,.85)";
    ctx.lineWidth = 1.4;
    ctx.beginPath();
    ctx.moveTo(beam.x1, beam.y1);
    ctx.lineTo(beam.x2, beam.y2);
    ctx.stroke();
    ctx.shadowBlur = 0;
  }
  ctx.globalAlpha = 1;
  for (const ball of balls.filter(b => b.alive)) {
    const speed = Math.hypot(ball.vx, ball.vy) || 1;
    const tx = -ball.vx / speed;
    const ty = -ball.vy / speed;
    if (ball.golden) {
      const tail = 34;
      const flame = ctx.createLinearGradient(ball.x, ball.y, ball.x + tx * tail, ball.y + ty * tail);
      flame.addColorStop(0, "rgba(255, 232, 112, .82)");
      flame.addColorStop(.55, "rgba(255, 143, 45, .28)");
      flame.addColorStop(1, "rgba(255, 143, 45, 0)");
      ctx.strokeStyle = flame;
      ctx.lineWidth = ball.r * 1.35;
      ctx.lineCap = "round";
      ctx.shadowColor = "#ffd76b";
      ctx.shadowBlur = 18;
      ctx.beginPath();
      ctx.moveTo(ball.x + tx * 4, ball.y + ty * 4);
      ctx.lineTo(ball.x + tx * tail, ball.y + ty * tail);
      ctx.stroke();
      ctx.lineCap = "butt";
    }
    ctx.shadowColor = ball.golden ? "#ffd76b" : "#fff";
    ctx.shadowBlur = ball.golden ? 30 : 16;
    const ballFill = ctx.createRadialGradient(ball.x - ball.r * .35, ball.y - ball.r * .35, 1, ball.x, ball.y, ball.r * 1.4);
    ballFill.addColorStop(0, "#ffffff");
    ballFill.addColorStop(.42, ball.golden ? "#ffe27a" : "#dffbff");
    ballFill.addColorStop(1, ball.golden ? "#ff9f1f" : "#8eeaff");
    ctx.fillStyle = ballFill;
    ctx.beginPath(); ctx.arc(ball.x, ball.y, ball.r, 0, Math.PI * 2); ctx.fill();
    if (ball.golden) {
      ctx.shadowBlur = 0;
      ctx.fillStyle = "rgba(255,255,245,.86)";
      ctx.beginPath(); ctx.arc(ball.x - ball.r * .22, ball.y - ball.r * .22, ball.r * .42, 0, Math.PI * 2); ctx.fill();
    }
    ctx.shadowBlur = 0;
  }
  for (const p of particles) {
    const fade = p.life / p.max;
    ctx.globalAlpha = fade * fade;
    ctx.save();
    if (p.kind === "spark") {
      const length = p.r * (2.4 + fade * 3.2);
      const angle = Math.atan2(p.vy, p.vx);
      ctx.translate(p.x, p.y);
      ctx.rotate(angle);
      ctx.strokeStyle = p.color;
      ctx.lineWidth = Math.max(1, p.r * .32);
      ctx.shadowColor = p.color;
      ctx.shadowBlur = 10;
      ctx.beginPath();
      ctx.moveTo(-length, 0);
      ctx.lineTo(0, 0);
      ctx.stroke();
      ctx.fillStyle = "#ffffff";
      ctx.beginPath();
      ctx.arc(0, 0, Math.max(1.2, p.r * .28), 0, Math.PI * 2);
      ctx.fill();
    } else {
      ctx.fillStyle = p.color;
      ctx.shadowColor = p.color;
      ctx.shadowBlur = 8;
      ctx.translate(p.x, p.y);
      ctx.rotate(p.rot);
      ctx.beginPath();
      ctx.moveTo(0, -p.r * 1.25);
      ctx.lineTo(p.r * .62, p.r * .72);
      ctx.lineTo(-p.r * .58, p.r * .5);
      ctx.closePath();
      ctx.fill();
      ctx.fillStyle = "rgba(255,255,255,.52)";
      ctx.beginPath();
      ctx.moveTo(0, -p.r * .86);
      ctx.lineTo(p.r * .3, p.r * .1);
      ctx.lineTo(-p.r * .22, p.r * .1);
      ctx.closePath();
      ctx.fill();
    }
    ctx.restore();
  }
  ctx.globalAlpha = 1;
  for (const wave of shockwaves) {
    const progress = 1 - wave.life / wave.maxLife;
    const fade = Math.pow(wave.life / wave.maxLife, 1.45);
    const coreSize = Math.max(16, wave.radius * (.2 + (1 - progress) * .14));
    const rays = 8 + Math.floor((wave.max || 80) / 70);
    ctx.save();
    ctx.globalCompositeOperation = "screen";
    ctx.globalAlpha = fade * .42;
    const bloom = ctx.createRadialGradient(wave.x, wave.y, 0, wave.x, wave.y, coreSize);
    bloom.addColorStop(0, "rgba(255,255,255,.96)");
    bloom.addColorStop(.2, "rgba(141,238,255,.7)");
    bloom.addColorStop(1, "rgba(105,192,255,0)");
    ctx.fillStyle = bloom;
    ctx.beginPath();
    ctx.arc(wave.x, wave.y, coreSize, 0, Math.PI * 2);
    ctx.fill();

    ctx.translate(wave.x, wave.y);
    ctx.rotate(progress * .7 + wave.max * .01);
    ctx.strokeStyle = "#bdf6ff";
    ctx.shadowColor = "#6ddfff";
    ctx.shadowBlur = 13;
    ctx.lineWidth = Math.max(1.2, 3.2 - progress * 1.6);
    ctx.globalAlpha = fade * .82;
    for (let i = 0; i < rays; i++) {
      const angle = i * Math.PI * 2 / rays;
      const inner = wave.radius * (.44 + (i % 3) * .055);
      const outer = wave.radius * (.76 + (i % 2) * .13);
      ctx.beginPath();
      ctx.moveTo(Math.cos(angle) * inner, Math.sin(angle) * inner);
      ctx.lineTo(Math.cos(angle) * outer, Math.sin(angle) * outer);
      ctx.stroke();
    }
    ctx.restore();
  }
  ctx.globalAlpha = 1;
  for (const banner of banners) {
    const t = banner.life / banner.maxLife;
    const alpha = Math.min(1, t * 2.8);
    const scale = 1 + (1 - t) * .08;
    const y = h * .42 - (1 - t) * 18;
    ctx.globalAlpha = alpha;
    ctx.fillStyle = `rgba(2, 8, 14, ${.5 * alpha})`;
    ctx.fillRect(-12, y - 58, w + 24, 118);
    ctx.strokeStyle = banner.color;
    ctx.lineWidth = 2;
    ctx.shadowColor = banner.color;
    ctx.shadowBlur = 28;
    ctx.beginPath();
    ctx.moveTo(w * .12, y + 38);
    ctx.lineTo(w * .88, y + 38);
    ctx.stroke();
    ctx.save();
    ctx.translate(w / 2, y);
    ctx.scale(scale, scale);
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillStyle = banner.color;
    ctx.font = "900 28px monospace";
    ctx.fillText(banner.title, 0, -12);
    ctx.shadowBlur = 0;
    ctx.fillStyle = "rgba(255,255,255,.88)";
    ctx.font = "800 11px monospace";
    ctx.fillText(banner.subtitle, 0, 20);
    ctx.restore();
    ctx.shadowBlur = 0;
  }
  ctx.globalAlpha = 1;
  if (comboPraiseToast) {
    const toast = comboPraiseToast;
    const t = toast.life / toast.maxLife;
    const alpha = Math.min(1, t * 3);
    const cardW = 138;
    const cardH = 52;
    const x = w - cardW - 16 + (1 - alpha) * 18;
    const y = 106;
    const nextTier = comboPraiseTiers.find(item => item.hits > toast.hits);
    const progress = nextTier ? clamp(toast.chain / nextTier.hits, 0, 1) : 1;
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.shadowColor = toast.color;
    ctx.shadowBlur = 14;
    ctx.fillStyle = "rgba(3, 15, 28, .78)";
    ctx.strokeStyle = toast.color;
    ctx.lineWidth = 1.4;
    ctx.beginPath();
    ctx.roundRect(x, y, cardW, cardH, 12);
    ctx.fill();
    ctx.stroke();
    ctx.shadowBlur = 0;

    ctx.textAlign = "left";
    ctx.textBaseline = "middle";
    ctx.fillStyle = "rgba(225, 255, 255, .72)";
    ctx.font = "800 9px monospace";
    ctx.fillText("COMBO RESULT", x + 12, y + 12);
    ctx.fillStyle = toast.color;
    ctx.font = "900 23px monospace";
    ctx.fillText(`x${toast.chain}`, x + 12, y + 31);
    ctx.fillStyle = "rgba(255,255,255,.9)";
    ctx.font = "900 10px monospace";
    ctx.textAlign = "right";
    ctx.fillText(toast.title, x + cardW - 10, y + 31);

    ctx.fillStyle = "rgba(255,255,255,.15)";
    ctx.fillRect(x + 12, y + cardH - 9, cardW - 24, 3);
    ctx.fillStyle = toast.color;
    ctx.fillRect(x + 12, y + cardH - 9, (cardW - 24) * progress, 3);
    ctx.restore();
  }
  ctx.globalAlpha = 1;
  for (const p of popups) {
    ctx.globalAlpha = Math.min(1, p.life * 2);
    ctx.fillStyle = "#fff"; ctx.font = "800 15px monospace"; ctx.textAlign = "center";
    ctx.fillText(p.text, p.x, p.y);
  }
  ctx.globalAlpha = 1;

  for (const flake of snowflakes) {
    if (flake.r < 1.65) continue;
    ctx.globalAlpha = flake.alpha * .42;
    ctx.fillStyle = "#fff";
    ctx.beginPath();
    ctx.arc(flake.x, flake.y, flake.r * 1.35, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalAlpha = 1;

  if (running && aiming) {
    const baseLength = 276;
    const length = adAimBoost ? baseLength * 2 : baseLength * Math.min(2, 1 + upgrades.aim * .25);
    const plan = launchPlan(goldenShots > 0);
    for (let index = 0; index < plan.length; index++) {
      const shot = plan[index];
      const points = cachedAimGuidePoints(shot, length, index);
      for (const point of points) {
        const progress = point.distance / length;
        const radius = 3.7 - progress * 2.35;
        ctx.globalAlpha = (.78 * (1 - progress) + .08) * (plan.length > 1 ? .78 : 1);
        ctx.fillStyle = goldenShots > 0 ? "#ffd76b" : adAimBoost ? "#9eeeff" : "#effffa";
        ctx.beginPath();
        ctx.arc(point.x, point.y, radius, 0, Math.PI * 2);
        ctx.fill();
      }
    }
    ctx.globalAlpha = 1;
  }
  const launcherGolden = goldenShots > 0;
  ctx.strokeStyle = launcherGolden ? "rgba(255, 215, 98, .72)" : "rgba(139, 239, 255, .5)";
  ctx.lineWidth = 2;
  ctx.shadowColor = launcherGolden ? "#ffd76b" : "#72ddff";
  ctx.shadowBlur = launcherGolden ? 28 : 16;
  ctx.beginPath();
  ctx.arc(launchX, launchY, launcherGolden ? 22 : 17, 0, Math.PI * 2);
  ctx.stroke();
  ctx.fillStyle = launcherGolden ? "#ffd76b" : "#b9f3ff";
  ctx.shadowColor = launcherGolden ? "#ffd76b" : "#72ddff";
  ctx.shadowBlur = launcherGolden ? 26 : 18;
  ctx.beginPath(); ctx.arc(launchX, launchY, launcherGolden ? 12 : 10, 0, Math.PI * 2); ctx.fill();
  if (launcherGolden) {
    ctx.shadowBlur = 0;
    ctx.fillStyle = "rgba(255,255,245,.86)";
    ctx.beginPath(); ctx.arc(launchX - 3, launchY - 3, 4.2, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = "#fff0a8";
    ctx.font = "900 11px monospace"; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.fillText(`x${goldenShots}`, launchX, launchY - 23);
  }
  ctx.shadowBlur = 0;
  ctx.restore();
}

function loop(ts) {
  const dt = Math.min(.03, (ts - (last || ts)) / 1000);
  last = ts;
  if (running) step(dt);
  if (!targetRenderInterval || ts - lastRender >= targetRenderInterval) {
    draw();
    lastRender = ts;
  }
  raf = platform.frame(loop);
}

function setAim(clientX) {
  const rect = canvas.getBoundingClientRect();
  const ratio = clamp((clientX - rect.left) / rect.width, 0, 1);
  const nextAngle = clamp(-Math.PI + ratio * Math.PI, -Math.PI + .2, -.2);
  if (Math.abs(nextAngle - angle) > .0005) aimGuideCache = null;
  angle = nextAngle;
}

canvas.addEventListener("pointerdown", e => { dragging = true; setAim(e.clientX); });
canvas.addEventListener("pointermove", e => { if (dragging) setAim(e.clientX); });
canvas.addEventListener("pointerup", e => {
  if (!dragging) return;
  dragging = false;
  setAim(e.clientX);
  spawnBall();
});
window.addEventListener("keydown", e => {
  if (e.key === "ArrowLeft") angle = clamp(angle - .08, -Math.PI + .2, -.2);
  if (e.key === "ArrowRight") angle = clamp(angle + .08, -Math.PI + .2, -.2);
  if (e.key === " " || e.key === "Enter") spawnBall();
});
soundBtn.addEventListener("click", e => {
  e.stopPropagation();
  initAudio();
  masterGain.gain.value = masterGain.gain.value > 0 ? 0 : .52;
  const enabled = masterGain.gain.value > 0;
  soundBtn.textContent = enabled ? "音效 ON" : "音效 OFF";
  soundBtn.setAttribute("aria-label", enabled ? "关闭音效" : "开启音效");
});
adAimBtn?.addEventListener("click", e => {
  e.stopPropagation();
  watchAdForAim();
});
rankBtn?.addEventListener("click", e => {
  e.stopPropagation();
  const opening = rankPanel.classList.contains("hidden");
  renderLeaderboard(rankLeaderboard);
  rankPanel.classList.toggle("hidden", !opening);
  rankBtn.classList.toggle("active", opening);
});
rankCloseBtn?.addEventListener("click", e => {
  e.stopPropagation();
  rankPanel.classList.add("hidden");
  rankBtn?.classList.remove("active");
});
guardTestBtn?.addEventListener("click", e => {
  e.stopPropagation();
  testDefenseLayers();
});
xpTestBtn?.addEventListener("click", e => {
  e.stopPropagation();
  initAudio();
  activateGoldenMissiles();
});
document.querySelector("#startBtn").addEventListener("click", startGame);
document.querySelector("#restartBtn").addEventListener("click", startGame);
window.addEventListener("resize", resize);
resize();
seedBlocks();
updateAdAimButton();
raf = platform.frame(loop);
