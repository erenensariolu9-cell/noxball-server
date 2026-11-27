/* =====================================================================
   NOXBALL MAÇ SUNUCUSU  (Render)   v2.2
   - SADECE maçı yönetir: fizik, skor, geri sayım, gol, bitiş.
   - v2.2: Gelişmiş 2v2 / 3v3 Takım Bot Zekâsı:
       * Dinamik rol dağılımı (Forvet / Kaleci / Kanat-Destek) + insan takım arkadaşı uyumu
       * Köşe, direk ve duvar sekmeli yörünge tahmini
       * Kale boşluklarına nişan, duvar sektirme (bank shot) ve açık takım arkadaşına pas
       * Şut koridorundan çekilme (kendi şutunu kesmeme) ve köşe kilidi çözme
   Ortam değişkenleri: MAC_SECRET, HF_URL, PORT
   ===================================================================== */
'use strict';
const http = require('http');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = +process.env.PORT || 10000;
const SECRET = process.env.MAC_SECRET || '';
const HF_URL = (process.env.HF_URL || '').replace(/\/+$/, '');
if (!SECRET) console.warn('[UYARI] MAC_SECRET tanımlı değil: hiçbir oyuncu odaya alınmaz.');
if (!HF_URL) console.warn('[UYARI] HF_URL tanımlı değil: maç sonuçları Hugging Face\'e iletilemez.');

/* ---------------- Oyun sabitleri (oyun.html ile aynı olmalı) ---------------- */
const STEP = 1000 / 60;
const KOSE_R = 30, DIREK_R = 5;
const SEKME = 0.94;
const MAX_TOP_HIZI = 17;
const HEDEF_GOL = 3;
const GERI_SAYIM = 180;
const GOL_KUTLAMA = 180;
const MIN_MAC_MS = 15000;
const KOPMA_TOLERANS = 6000;
const SUSKUNLUK_MS = 7000;
const ODA_BEKLEME_MS = 80000;

const ZOOM = { 1: 1, 2: 1.6, 3: 2.0 };
const DK = { 1: 1, 2: 1.48, 3: 1.81 };
function geo(T) {
  const f = ZOOM[T], dk = DK[T], w = 320 * f, h = 530 * f, cx = 40 + w / 2;
  return { f, dk, dr: 24 * dk, br: 14 * dk, direk: DIREK_R * f, sol: 40, ust: 35, w, h, sag: 40 + w, alt: 35 + h, mid: 35 + h / 2, cx, kSol: cx - 70 * f, kSag: cx + 70 * f };
}
const GEO = { 1: geo(1), 2: geo(2), 3: geo(3) };
const R6 = ['a', 'b', 'c', 'd', 'e', 'f'];

/* ---------------- Bilet doğrulama ---------------- */
function biletCoz(tk) {
  if (!SECRET || typeof tk !== 'string' || tk.length > 400) return null;
  const i = tk.indexOf('.');
  if (i < 1) return null;
  const yuk = tk.slice(0, i), imza = tk.slice(i + 1);
  const bek = crypto.createHmac('sha256', SECRET).update(yuk).digest('base64url');
  const a = Buffer.from(imza), b = Buffer.from(bek);
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return null;
  let p; try { p = JSON.parse(Buffer.from(yuk, 'base64url').toString('utf8')); } catch (_) { return null; }
  if (!p || typeof p.mid !== 'string' || !(p.r === 'mavi' || p.r === 'kirmizi') || !(p.exp > Date.now())) return null;
  if (p.m === 2 || p.m === 3) {
    if (!R6.slice(0, p.m * 2).includes(p.p) || !(Number.isInteger(p.s) && p.s >= 0 && p.s < p.m)) return null;
    if (p.bot === 1) { const n = p.n | 0; if (!(n >= 1 && n <= p.m) || R6.indexOf(p.p) >= n) return null; }
  } else if (p.p !== 'a' && p.p !== 'b') return null;
  return p;
}

/* ---------------- Odalar ---------------- */
const odalar = new Map();
const bitenler = new Map();
const kisitla = (v, a, b) => Math.max(a, Math.min(b, v));

function baslangic(G, T, renk, slot) {
  return { x: T === 1 ? G.cx : G.sol + G.w * (slot + 1) / (T + 1), y: renk === 'mavi' ? G.alt - 85 * G.f : G.ust + 85 * G.f };
}
function yeniDisk(p, r) { return { x: p.x, y: p.y, r: r, vx: 0, vy: 0, hedefX: p.x, hedefY: p.y, ox0: p.x, oy0: p.y }; }
function yeniOda(id, T, bot, botRenk, insan) {
  const G = GEO[T];
  const o = {
    id, T, v2: T > 1, G, bot: !!bot, botRenk: botRenk || '', insan: Math.max(1, Math.min(T, insan || T)),
    olusma: Date.now(), t0: 0, basladi: false, bitti2: false,
    oy: {}, roller: [],
    top: { x: G.cx, y: G.mid, r: G.br, vx: 0, vy: 0, surtunme: 0.986, aci: 0 },
    dk: { mavi: [], kirmizi: [] }, liste: [],
    gol: { aktif: false, kim: '', z: 0 },
    skorM: 0, skorK: 0, bitenKim: null, sonVuran: 'mavi', sayac: GERI_SAYIM, tick: 0,
    sSonAnahtar: '', sSonG: 0, sSonV: 0, sSonZaman: 0,
    botTohum: Math.random() * 100, bs: {}
  };
  for (const renk of ['mavi', 'kirmizi']) for (let s = 0; s < T; s++) { const d = yeniDisk(baslangic(G, T, renk, s), G.dr); o.dk[renk].push(d); o.liste.push([d, renk]); }
  o.roller = T === 1 ? ['a', 'b'] : (o.bot ? R6.slice(0, o.insan) : R6.slice(0, T * 2));
  return o;
}
const zaman = o => Math.round(o.tick * STEP * 10) / 10;
function gonder(ws, obj) { if (ws && ws.readyState === 1) { try { ws.send(typeof obj === 'string' ? obj : JSON.stringify(obj)); } catch (_) {} } }
function yayin(o, obj, hizli) {
  const s = JSON.stringify(obj);
  for (const r of o.roller) {
    const oy = o.oy[r];
    if (!oy || !oy.ws || oy.ws.readyState !== 1) continue;
    if (hizli && oy.ws.bufferedAmount > 16384) continue;
    try { oy.ws.send(s); } catch (_) {}
  }
}
const diskOf = (o, oy) => o.dk[oy.renk][oy.slot];

/* ---------------- FİZİK ---------------- */
function diskKisit(o, d, renk) {
  const G = o.G, r = d.r;
  d.x = kisitla(d.x, G.sol + r, G.sag - r);
  d.y = renk === 'mavi' ? kisitla(d.y, G.mid + r, G.alt - r) : kisitla(d.y, G.ust + r, G.mid - r);
}
function diskAyir(o) {
  for (const renk of ['mavi', 'kirmizi']) {
    const a = o.dk[renk];
    for (let pas = 0; pas < 4; pas++) for (let i = 0; i < a.length; i++) for (let j = i + 1; j < a.length; j++) {
      const p = a[i], q = a[j]; let dx = q.x - p.x, dy = q.y - p.y, m = Math.hypot(dx, dy); const min = p.r + q.r;
      if (m >= min) continue;
      if (m < 0.001) { dx = 1; dy = 0; m = 1; }
      const ov = (min - m) / 2, nx = dx / m, ny = dy / m;
      p.x -= nx * ov; p.y -= ny * ov; q.x += nx * ov; q.y += ny * ov;
      diskKisit(o, p, renk); diskKisit(o, q, renk);
    }
  }
}
function diskleriHareket(o) {
  for (const [d] of o.liste) { d.ox0 = d.x; d.oy0 = d.y; d.x += (d.hedefX - d.x) * 0.35; d.y += (d.hedefY - d.y) * 0.35; }
  if (o.T > 1) diskAyir(o);
  for (const [d] of o.liste) { d.vx = d.x - d.ox0; d.vy = d.y - d.oy0; }
}
function olay(o, s) { yayin(o, { k: 'a', t: zaman(o), s: s, w: o.sonVuran === 'kirmizi' ? 1 : 0 }); }

function carpismayiCoz(o, disk, renk) {
  const t = o.top, G = o.G;
  const dx = t.x - disk.x, dy = t.y - disk.y, mesafe = Math.sqrt(dx * dx + dy * dy), minM = t.r + disk.r;
  if (!(mesafe < minM)) return;
  const ileri = renk === 'mavi' ? -1 : 1;
  let nx, ny;
  if (mesafe > 0.0001) { nx = dx / mesafe; ny = dy / mesafe; } else { nx = 0; ny = ileri; }
  const ic = minM - mesafe;
  const px = t.x + nx * ic, py = t.y + ny * ic, kapi = t.x > G.kSol && t.x < G.kSag;
  const bx = (px - t.r < G.sol && nx < 0) || (px + t.r > G.sag && nx > 0);
  const by = !kapi && ((py - t.r < G.ust && ny < 0) || (py + t.r > G.alt && ny > 0));
  if (bx && by) {
    nx = G.cx >= t.x ? 1 : -1; ny = G.mid >= t.y ? 1 : -1; const m = Math.hypot(nx, ny); nx /= m; ny /= m;
    t.x = kisitla(disk.x + nx * minM, G.sol + t.r, G.sag - t.r); t.y = kisitla(disk.y + ny * minM, G.ust + t.r, G.alt - t.r);
  } else if (bx) {
    ny = Math.abs(ny) < 0.15 ? ileri : (ny >= 0 ? 1 : -1); nx = 0;
    t.y = disk.y + ny * Math.sqrt(Math.max(1, minM * minM - dx * dx));
    t.x = kisitla(t.x, G.sol + t.r, G.sag - t.r);
  } else if (by) {
    nx = Math.abs(nx) < 0.15 ? (G.cx >= t.x ? 1 : -1) : (nx >= 0 ? 1 : -1); ny = 0;
    t.x = disk.x + nx * Math.sqrt(Math.max(1, minM * minM - dy * dy));
    t.y = kisitla(t.y, G.ust + t.r, G.alt - t.r);
  } else { t.x = px; t.y = py; }
  const vg = Math.sqrt(disk.vx * disk.vx + disk.vy * disk.vy);
  t.vx = nx * (vg * 0.95 + 4.2) + disk.vx * 0.35;
  t.vy = ny * (vg * 0.95 + 4.2) + disk.vy * 0.35;
  o.sonVuran = renk; olay(o, 1);
  const mh = Math.sqrt(t.vx * t.vx + t.vy * t.vy);
  if (mh > MAX_TOP_HIZI) { t.vx = (t.vx / mh) * MAX_TOP_HIZI; t.vy = (t.vy / mh) * MAX_TOP_HIZI; }
}
function direkCarpismasi(o, px, py) {
  const t = o.top, dr = o.G.direk, dx = t.x - px, dy = t.y - py, dist = Math.sqrt(dx * dx + dy * dy), minD = t.r + dr;
  if (dist < minD && dist > 0) {
    const nx = dx / dist, ny = dy / dist;
    t.x = px + nx * minD; t.y = py + ny * minD;
    const dot = t.vx * nx + t.vy * ny;
    if (dot < 0) { t.vx = (t.vx - 2 * dot * nx) * SEKME; t.vy = (t.vy - 2 * dot * ny) * SEKME; olay(o, 2); }
  }
}
function koseCarpismasi(o, cx, cy) {
  const t = o.top, dx = t.x - cx, dy = t.y - cy, dist = Math.sqrt(dx * dx + dy * dy), maxD = KOSE_R - t.r;
  if (dist > maxD && dist > 0) {
    const nx = dx / dist, ny = dy / dist;
    t.x = cx + nx * maxD; t.y = cy + ny * maxD;
    const dot = t.vx * nx + t.vy * ny;
    if (dot > 0) { t.vx = (t.vx - 2 * dot * nx) * SEKME; t.vy = (t.vy - 2 * dot * ny) * SEKME; }
  }
}
function golBaslat(o, kim) {
  if (o.gol.aktif) return;
  const t = o.top;
  o.gol.aktif = true; o.gol.kim = kim; o.gol.z = GOL_KUTLAMA;
  const vs = Math.sqrt(t.vx * t.vx + t.vy * t.vy), sallanma = Math.min(18, Math.max(5, vs * 0.8));
  if (kim === 'mavi') o.skorM++; else o.skorK++;
  yayin(o, { k: 'g', t: zaman(o), w: kim, m: o.skorM, r: o.skorK, s: Math.round(sallanma * 10) / 10 });
  if (o.skorM >= HEDEF_GOL || o.skorK >= HEDEF_GOL) o.bitenKim = kim;
  t.vx *= 0.2; t.vy *= 0.2;
}
function santraSifirla(o) {
  const t = o.top, G = o.G;
  o.gol.aktif = false;
  t.x = G.cx; t.y = G.mid; t.vx = 0; t.vy = 0;
  for (const renk of ['mavi', 'kirmizi']) o.dk[renk].forEach((d, s) => {
    const p = baslangic(G, o.T, renk, s);
    Object.assign(d, { x: p.x, y: p.y, hedefX: p.x, hedefY: p.y, vx: 0, vy: 0, ox0: p.x, oy0: p.y });
  });
  o.sonVuran = 'mavi'; o.bs = {};
}

/* ---------------- GELİŞMİŞ 2v2 / 3v3 BOT ZEKÂSI (v2.2) ---------------- */
const BOT_HIZ = 12.2;

function simDirekNokta(x, y, vx, vy, px, py, minD) {
  const dx = x - px, dy = y - py, dist = Math.hypot(dx, dy);
  if (dist < minD && dist > 0) {
    const nx = dx / dist, ny = dy / dist;
    x = px + nx * minD; y = py + ny * minD;
    const dot = vx * nx + vy * ny;
    if (dot < 0) { vx = (vx - 2 * dot * nx) * SEKME; vy = (vy - 2 * dot * ny) * SEKME; }
  }
  return [x, y, vx, vy];
}

function topIz(o, n) {
  const t = o.top, G = o.G, r = t.r, minD = r + G.direk, maxK = KOSE_R - r, out = [];
  let x = t.x, y = t.y, vx = t.vx, vy = t.vy;
  for (let i = 0; i < n; i++) {
    x += vx; y += vy; vx *= t.surtunme; vy *= t.surtunme;
    [x, y, vx, vy] = simDirekNokta(x, y, vx, vy, G.kSol, G.ust, minD);
    [x, y, vx, vy] = simDirekNokta(x, y, vx, vy, G.kSag, G.ust, minD);
    [x, y, vx, vy] = simDirekNokta(x, y, vx, vy, G.kSol, G.alt, minD);
    [x, y, vx, vy] = simDirekNokta(x, y, vx, vy, G.kSag, G.alt, minD);
    let kx = -1, ky = -1;
    if (x < G.sol + KOSE_R && y < G.ust + KOSE_R) { kx = G.sol + KOSE_R; ky = G.ust + KOSE_R; }
    else if (x > G.sag - KOSE_R && y < G.ust + KOSE_R) { kx = G.sag - KOSE_R; ky = G.ust + KOSE_R; }
    else if (x < G.sol + KOSE_R && y > G.alt - KOSE_R) { kx = G.sol + KOSE_R; ky = G.alt - KOSE_R; }
    else if (x > G.sag - KOSE_R && y > G.alt - KOSE_R) { kx = G.sag - KOSE_R; ky = G.alt - KOSE_R; }
    if (kx >= 0) {
      const dx = x - kx, dy = y - ky, dist = Math.hypot(dx, dy);
      if (dist > maxK && dist > 0) {
        const nx = dx / dist, ny = dy / dist;
        x = kx + nx * maxK; y = ky + ny * maxK;
        const dot = vx * nx + vy * ny;
        if (dot > 0) { vx = (vx - 2 * dot * nx) * SEKME; vy = (vy - 2 * dot * ny) * SEKME; }
      }
    } else {
      if (x - r < G.sol) { x = G.sol + r; vx = -vx * SEKME; } else if (x + r > G.sag) { x = G.sag - r; vx = -vx * SEKME; }
      if (!(x > G.kSol && x < G.kSag)) {
        if (y - r < G.ust) { y = G.ust + r; vy = -vy * SEKME; } else if (y + r > G.alt) { y = G.alt - r; vy = -vy * SEKME; }
      }
    }
    out.push({ x, y, vx, vy });
  }
  return out;
}

function botGit(o, d, alt, tx, ty, hiz) {
  const G = o.G, toplam = G.ust + G.alt, wy = alt ? toplam - ty : ty;
  const dx = tx - d.x, dy = wy - d.y, dist = Math.hypot(dx, dy), adim = hiz / 0.35;
  const k = dist > adim ? adim / dist : 1;
  d.hedefX = kisitla(d.x + dx * k, G.sol + d.r, G.sag - d.r);
  d.hedefY = alt ? kisitla(d.y + dy * k, G.mid + d.r, G.alt - d.r) : kisitla(d.y + dy * k, G.ust + d.r, G.mid - d.r);
}

function noktaDogruMesafe(px, py, x0, y0, x1, y1) {
  const sx = x1 - x0, sy = y1 - y0, L2 = sx * sx + sy * sy || 1;
  const u = kisitla(((px - x0) * sx + (py - y0) * sy) / L2, 0, 1);
  return Math.hypot(px - (x0 + sx * u), py - (y0 + sy * u));
}

function botTakim(o, renk, slotlar) {
  if (!slotlar.length) return;
  const G = o.G, f = G.f, t = o.top, alt = renk === 'mavi', toplam = G.ust + G.alt;
  const V = y => alt ? toplam - y : y;
  const Vy = vy => alt ? -vy : vy;
  const hiz = BOT_HIZ * Math.sqrt(f);
  const botSet = new Set(slotlar);
  const allD = o.dk[renk];
  const O = o.dk[renk === 'mavi' ? 'kirmizi' : 'mavi'].map(d => ({ x: d.x, y: V(d.y), vx: d.vx, vy: Vy(d.vy) }));
  const r = allD[0].r, minM = t.r + r, reachY = G.mid + minM * 0.55;

  const iz = topIz(o, 55).map(p => ({ x: p.x, y: V(p.y), vx: p.vx, vy: Vy(p.vy) }));
  const bx = t.x, by = V(t.y), bvx = t.vx, bvy = Vy(t.vy), hizTop = Math.hypot(bvx, bvy);

  // En yakın rakibin topa uzaklığı (baskı ölçüsü)
  let minOppDist = 1e9;
  for (const od of O) minOppDist = Math.min(minOppDist, Math.hypot(od.x - bx, od.y - by));

  // Köşe / duvar kilidi kırıcı
  const st = o.bs[renk] || (o.bs[renk] = { sx: 0, sy: 0, n: 0, geri: 0, varyant: 0, bek: 0, atakIdx: -1 });
  const duvarYakin = (px, py) => px - G.sol < t.r + 36 * f || G.sag - px < t.r + 36 * f || py - G.ust < t.r + 30 * f;
  if (duvarYakin(bx, by) && by < G.mid && Math.hypot(bx - st.sx, by - st.sy) < 55 * f) {
    if (++st.n > 65) { st.n = 0; st.geri = 38; st.varyant = (st.varyant + 1) % 3; }
  } else { st.sx = bx; st.sy = by; st.n = 0; }
  const geri = st.geri > 0; if (geri) st.geri--;

  // Yol açıklığı: rakip disklerin bu çizgiye en yakın mesafesi
  const yolTemiz = (x0, y0, x1, y1) => {
    let cl = 1e9;
    for (const od of O) cl = Math.min(cl, noktaDogruMesafe(od.x, od.y, x0, y0, x1, y1));
    return cl;
  };

  // En iyi şut / duvar sektirme / pas hedefini seç
  const aimY = G.alt + 22 * f;
  const hedefSec = (q, dyv, dxv, dIdx) => {
    // 1) Direkt kale şutları (7 nokta)
    let bestX = G.cx, bestY = aimY, bestScore = -1e9, bestClear = -1;
    for (let i = -3; i <= 3; i++) {
      const ax = G.cx + i * 19 * f;
      const cl = yolTemiz(q.x, q.y, ax, aimY);
      const score = cl - Math.abs(i) * 4.5 * f;
      if (score > bestScore) { bestScore = score; bestX = ax; bestClear = cl; }
    }
    // 2) Direkt yol çok kapalıysa yan duvardan sektirme (bank shot) dene
    if (bestClear < r * 1.15 && q.y > G.ust + 80 * f) {
      for (const duvarX of [G.sol + t.r, G.sag - t.r]) {
        const mirX = 2 * duvarX - G.cx;
        const tWall = (duvarX - q.x) / ((mirX - q.x) || 0.001);
        if (tWall > 0.05 && tWall < 0.85) {
          const wy = q.y + (aimY - q.y) * tWall;
          if (wy > q.y && wy < G.alt - 40 * f) {
            const clBank = Math.min(yolTemiz(q.x, q.y, duvarX, wy), yolTemiz(duvarX, wy, G.cx, aimY));
            if (clBank > bestClear + 14 * f) { bestClear = clBank; bestX = mirX; bestY = aimY; }
          }
        }
      }
    }
    // 3) 2v2 / 3v3 Pas: şut kapalıysa ve açıkta uygun bir takım arkadaşı varsa pas at
    if (allD.length >= 2 && bestClear < r * 0.95 && q.y < G.mid - 20 * f) {
      for (let j = 0; j < allD.length; j++) {
        if (j === dIdx) continue;
        const tm = allD[j], tmy = V(tm.y);
        if (tmy > G.mid - 28 * f || tmy < G.ust + 55 * f) continue;
        if (Math.hypot(tm.x - q.x, tmy - q.y) < minM * 3) continue;
        const pasCl = yolTemiz(q.x, q.y, tm.x, tmy + 20 * f);
        const tmShotCl = yolTemiz(tm.x, tmy, G.cx, aimY);
        if (pasCl > r * 1.1 && tmShotCl > bestClear + 16 * f) {
          return { ax: tm.x, ay: tmy + 22 * f };
        }
      }
    }
    return { ax: bestX + Math.sin(o.tick * 0.013 + o.botTohum) * 4 * f, ay: bestY };
  };

  // Topun bizim yarı sahadaki yetişme analizi (tüm takım için)
  const bilgi = allD.map((d, i) => {
    const dy = V(d.y);
    for (let k = 0; k < iz.length; k++) {
      const q = iz[k];
      if (q.y > reachY) continue;
      const dist = Math.hypot(q.x - d.x, q.y - dy);
      if (dist <= hiz * (k + 6) + minM * 0.5) {
        const wrongSide = dy > q.y - minM * 0.25 ? 10 : 0;      // topun önündeyse başka takım arkadaşına öncelik ver
        const humanBonus = !botSet.has(i) && Math.hypot(d.vx, d.vy) > 1.6 && dist < 130 * f ? -5 : 0;
        return { k: k + 1, q, score: (k + 1) + wrongSide + humanBonus };
      }
    }
    return { k: Infinity, q: null, score: Infinity };
  });

  // Forvet (atak) seçimi + hafif hysteresis (titremeyi önler)
  let atak = -1, bestScore = Infinity;
  bilgi.forEach((b, i) => { if (b.score < bestScore) { bestScore = b.score; atak = i; } });
  if (st.atakIdx >= 0 && st.atakIdx < allD.length && bilgi[st.atakIdx].score < bestScore + 3.5) {
    atak = st.atakIdx;
  }
  if (allD.length === 1 && atak >= 0 && bilgi[atak].k > 34) atak = -1;
  st.atakIdx = atak;

  // Kale tehdidi (top yörüngesi + rakibin olası şut çizgisi)
  const tehditP = iz.find(p => p.y <= G.ust + t.r + 18 * f && p.x > G.kSol - t.r * 1.2 && p.x < G.kSag + t.r * 1.2) || null;
  let projX = G.cx + (bx - G.cx) * 0.42;
  for (const od of O) {
    if (od.y > by + 5 * f && Math.hypot(od.x - bx, od.y - by) < 120 * f) {
      const tG = (G.ust - od.y) / ((by - od.y) || -0.001);
      if (tG > 0 && tG < 8) {
        const gx = od.x + (bx - od.x) * tG;
        if (gx > G.kSol - 35 * f && gx < G.kSag + 35 * f) { projX = kisitla(gx, G.kSol + r * 0.5, G.kSag - r * 0.5); break; }
      }
    }
  }

  // Top karşı yarıdaysa, topa en yakın oyuncu aktif baskı/bekleme pozisyonu alır
  let bekleyen = -1;
  if (atak < 0 && allD.length > 1) {
    let bd = 1e9;
    allD.forEach((d, i) => { const m = Math.hypot(d.x - bx, V(d.y) - by); if (m < bd) { bd = m; bekleyen = i; } });
  }
  // Kaleci: atak/bekleyen dışındaki en gerideki (kendi kalesine en yakın) oyuncu
  let kaleci = -1, kY = 1e9;
  allD.forEach((d, i) => {
    if (i === atak || i === bekleyen) return;
    const y = V(d.y);
    if (kaleci < 0 || y < kY) { kaleci = i; kY = y; }
  });
  if (kaleci < 0 && atak < 0 && bekleyen < 0) kaleci = 0;

  // Forvetin hedefi (koridor kaçınması için)
  const atakHedef = atak >= 0 ? hedefSec(bilgi[atak].q, V(allD[atak].y), allD[atak].x, atak) : null;
  const uzak = (tx, ty) => {
    // Topa yapışma + forvetin şut koridorunu kesme
    let x = tx, y = ty;
    const dx = x - bx, dy = y - by, m = Math.hypot(dx, dy), mn = minM * 2.4;
    if (m < mn) { const u = m > 0.001 ? [dx / m, dy / m] : [0, -1]; x = bx + u[0] * mn; y = by + u[1] * mn; }
    if (atak >= 0 && atakHedef) {
      const aq = bilgi[atak].q;
      const distKor = noktaDogruMesafe(x, y, aq.x, aq.y, atakHedef.ax, atakHedef.ay);
      if (distKor < minM * 2.1) {
        const push = (x >= aq.x ? 1 : -1) * (minM * 2.2 - distKor);
        x = kisitla(x + push, G.sol + r, G.sag - r);
      }
    }
    return [x, y];
  };

  const giris = iz.find(p => p.y <= reachY), hx = giris ? giris.x : bx;
  const hazirX = kisitla(G.cx + (hx - G.cx) * 0.65, G.sol + r, G.sag - r), hazirY = G.mid - 82 * f;

  let destekSay = 0;
  allD.forEach((d, i) => {
    if (!botSet.has(i)) return;     // insan oyuncuyu yönetme
    const dyv = V(d.y);

    if (i === atak) {
      const q = bilgi[i].q, kk = bilgi[i].k;
      if (geri && duvarYakin(bx, by)) {
        const cx0 = G.cx - bx, cy0 = (G.mid - 40 * f) - by, m0 = Math.hypot(cx0, cy0) || 1;
        botGit(o, d, alt, bx + cx0 / m0 * minM * 3.2, by + cy0 / m0 * minM * 3.2, hiz);
        return;
      }
      let ax = atakHedef.ax, ay = atakHedef.ay;
      if (duvarYakin(q.x, q.y)) {
        const ic = q.x < G.cx ? 1 : -1;
        if (st.varyant === 0) { ax = q.y - G.ust < t.r + 30 * f ? G.cx : q.x + ic * 75 * f; ay = q.y + 150 * f; }
        else if (st.varyant === 1) { ax = G.cx; ay = q.y + 80 * f; }
      }
      let ux = ax - q.x, uy = ay - q.y; const um = Math.hypot(ux, uy) || 1; ux /= um; uy /= um;
      const rx = d.x - q.x, ry = dyv - q.y;
      const boyunca = rx * ux + ry * uy, dik = -rx * uy + ry * ux, yakin = Math.hypot(rx, ry);
      const hizali = boyunca < -minM * 0.25 && Math.abs(dik) < minM * 0.8 + 10 * f;
      st.bek = hizali ? st.bek + 1 : 0;

      const baski = minOppDist < 95 * f;
      const vur = hizali && yakin < minM + 95 * f && (hizTop > 2 ? kk <= 9 : (baski || st.bek >= 6));
      if (vur) {
        botGit(o, d, alt, q.x + ux * minM * 0.75, q.y + uy * minM * 0.75, hiz * 1.38);
      } else if (boyunca < -minM * 0.25) {
        const wx = kisitla(q.x - ux * (minM + 12 * f), G.sol + r + 2, G.sag - r - 2);
        const wy = kisitla(q.y - uy * (minM + 12 * f), G.ust + r + 2, G.mid - r - 2);
        botGit(o, d, alt, wx, wy, hiz);
      } else {
        // Topun önündeyiz: duvardan uzak taraftan dolaş (kendi kaleye çarpma!)
        const solBos = q.x - G.sol, sagBos = G.sag - q.x;
        const yan = Math.abs(solBos - sagBos) > 25 * f ? (sagBos > solBos ? 1 : -1) : (dik >= 0 ? 1 : -1);
        botGit(o, d, alt, q.x - ux * (minM + 16 * f) - uy * yan * (minM + 20 * f), q.y - uy * (minM + 16 * f) + ux * yan * (minM + 20 * f), hiz);
      }
    } else if (i === bekleyen) {
      if (tehditP) {
        const ky = G.ust + 42 * f;
        botGit(o, d, alt, kisitla(tehditP.x + (tehditP.x < G.cx ? r * 1.8 : -r * 1.8), G.sol + r, G.sag - r), ky, hiz * 1.32);
      } else {
        const p = uzak(hazirX, hazirY);
        botGit(o, d, alt, p[0], p[1], hiz);
      }
    } else if (i === kaleci) {
      const ky = G.ust + 40 * f;
      let kx = projX, h = hiz;
      const gelen = iz.find(p => p.y <= ky + 22 * f);
      if (tehditP) { kx = tehditP.x; h = hiz * 1.4; }
      else if (gelen && gelen.vy < -0.7) { kx = gelen.x; h = hiz * 1.25; }
      kx = kisitla(kx, G.kSol + r * 0.5, G.kSag - r * 0.5);
      const kp = (tehditP || hizTop > 2.5) ? [kx, ky] : uzak(kx, ky);
      botGit(o, d, alt, kp[0], kp[1], h);
    } else {
      // 3v3 Kanat / Destek oyuncusu
      const yan = (destekSay++ % 2 ? 1 : -1);
      if (tehditP && kaleci >= 0 && Math.abs(allD[kaleci].x - tehditP.x) > 48 * f) {
        botGit(o, d, alt, kisitla(tehditP.x - yan * (r * 1.6), G.kSol, G.kSag), G.ust + 44 * f, hiz * 1.32);
        return;
      }
      const kanatX = bx < G.cx ? G.cx + 78 * f * (yan > 0 ? 1 : 0.4) : G.cx - 78 * f * (yan > 0 ? 1 : 0.4);
      const dy0 = atak >= 0 ? G.mid - 74 * f : G.mid - 98 * f;
      const sp = uzak(kisitla(kanatX, G.sol + r + 10 * f, G.sag - r - 10 * f), dy0);
      botGit(o, d, alt, sp[0], sp[1], hiz);
    }
  });
}

function botAdim(o) {
  botTakim(o, o.botRenk, Array.from({ length: o.T }, (_, i) => i));
  if (o.insan < o.T) botTakim(o, o.botRenk === 'mavi' ? 'kirmizi' : 'mavi', Array.from({ length: o.T - o.insan }, (_, i) => o.insan + i));
}

function adim(o) {
  const t = o.top, G = o.G;
  if (o.sayac > 0) { o.sayac--; diskleriHareket(o); return; }

  if (o.gol.aktif) {
    o.gol.z--;
    t.x += t.vx; t.y += t.vy; t.vx *= 0.85; t.vy *= 0.85;
    if (o.gol.z <= 0) {
      if (o.bitenKim) {
        if (o.v2) macBitirV2(o, o.bitenKim, 'bitti');
        else macBitir(o, rolOf(o, o.bitenKim), 'bitti');
      } else santraSifirla(o);
    }
    return;
  }

  if (o.bot) botAdim(o);
  diskleriHareket(o);

  const gh = Math.sqrt(t.vx * t.vx + t.vy * t.vy);
  if (gh > MAX_TOP_HIZI) { t.vx = (t.vx / gh) * MAX_TOP_HIZI; t.vy = (t.vy / gh) * MAX_TOP_HIZI; }
  t.x += t.vx; t.y += t.vy;
  t.aci += (t.vx + t.vy) * 0.035;
  t.vx *= t.surtunme; t.vy *= t.surtunme;
  if (Math.abs(t.vx) < 0.05) t.vx = 0;
  if (Math.abs(t.vy) < 0.05) t.vy = 0;

  direkCarpismasi(o, G.kSol, G.ust); direkCarpismasi(o, G.kSag, G.ust);
  direkCarpismasi(o, G.kSol, G.alt); direkCarpismasi(o, G.kSag, G.alt);

  if (t.x < G.sol + KOSE_R && t.y < G.ust + KOSE_R) koseCarpismasi(o, G.sol + KOSE_R, G.ust + KOSE_R);
  else if (t.x > G.sag - KOSE_R && t.y < G.ust + KOSE_R) koseCarpismasi(o, G.sag - KOSE_R, G.ust + KOSE_R);
  else if (t.x < G.sol + KOSE_R && t.y > G.alt - KOSE_R) koseCarpismasi(o, G.sol + KOSE_R, G.alt - KOSE_R);
  else if (t.x > G.sag - KOSE_R && t.y > G.alt - KOSE_R) koseCarpismasi(o, G.sag - KOSE_R, G.alt - KOSE_R);
  else {
    if (t.x - t.r < G.sol) { t.x = G.sol + t.r; t.vx *= -SEKME; }
    else if (t.x + t.r > G.sag) { t.x = G.sag - t.r; t.vx *= -SEKME; }

    if (t.x > G.kSol && t.x < G.kSag) {
      if (t.y + t.r < G.ust) golBaslat(o, 'mavi');
    } else if (t.y - t.r < G.ust) { t.y = G.ust + t.r; t.vy *= -SEKME; }

    if (t.x > G.kSol && t.x < G.kSag) {
      if (t.y - t.r > G.alt) golBaslat(o, 'kirmizi');
    } else if (t.y + t.r > G.alt) { t.y = G.alt - t.r; t.vy *= -SEKME; }
  }
  for (const [d, renk] of o.liste) carpismayiCoz(o, d, renk);
}

function goruntu(o) {
  o.tick++;
  const t = o.top;
  const g = o.gol.aktif ? (o.gol.kim === 'mavi' ? 1 : 2) : 0, v = o.sonVuran === 'kirmizi' ? 1 : 0;
  const durumDegisti = g !== o.sSonG || v !== o.sSonV;
  const r = q => Math.round(q * 10) / 10;
  const b = [r(t.x), r(t.y), r(t.vx), r(t.vy), Math.round(t.aci * 100) / 100];
  const m = [], rk = [];
  for (const d of o.dk.mavi) m.push(r(d.x), r(d.y));
  for (const d of o.dk.kirmizi) rk.push(r(d.x), r(d.y));
  const now = Date.now();
  const anahtar = b.join() + '|' + m.join() + '|' + rk.join() + '|' + g + v + '|' + Math.ceil(o.sayac / 60);
  if (g === 0 && !durumDegisti && anahtar === o.sSonAnahtar && now - o.sSonZaman < 250) return;
  o.sSonAnahtar = anahtar; o.sSonZaman = now; o.sSonG = g; o.sSonV = v;
  yayin(o, { k: o.v2 ? 's2' : 's', t: zaman(o), b: b, m: m, r: rk, g: g, z: o.gol.z, v: v, c: o.sayac }, true);
}

/* ---------------- Maç yaşam döngüsü ---------------- */
const rolOf = (o, renk) => (o.oy.a && o.oy.a.renk === renk) ? 'a' : 'b';
const digerRol = r => r === 'a' ? 'b' : 'a';
const renkOf = (o, rol) => o.oy[rol] ? o.oy[rol].renk : null;

function odaKapat(o, gecikme) {
  o.bitti2 = true;
  bitenler.set(o.id, Date.now());
  setTimeout(() => {
    for (const r of o.roller) { const oy = o.oy[r]; if (oy && oy.ws) { oy.ws.oy = null; try { oy.ws.close(); } catch (_) {} } }
    odalar.delete(o.id);
  }, gecikme || 0);
}
function macBitir(o, kazRol, neden) {
  if (o.bitti2) return;
  const kazRenk = renkOf(o, kazRol);
  yayin(o, { k: 'son', w: kazRenk, m: o.skorM, r: o.skorK, n: neden });
  const golOf = rol => renkOf(o, rol) === 'mavi' ? o.skorM : o.skorK;
  sonucBildir({ mid: o.id, kazanan: kazRol, gol: { a: golOf('a'), b: golOf('b') }, neden: neden, sure: Date.now() - o.t0 });
  odaKapat(o, 2500);
}
function macBitirV2(o, kazRenk, neden) {
  if (o.bitti2) return;
  yayin(o, { k: 'son', w: kazRenk, m: o.skorM, r: o.skorK, n: neden });
  sonucBildir({ mid: o.id, mod: 'v' + o.T, kazanan: kazRenk, gol: { mavi: o.skorM, kirmizi: o.skorK }, neden: neden, sure: Date.now() - o.t0 });
  odaKapat(o, 2500);
}
function macIptal(o) {
  if (o.bitti2) return;
  yayin(o, { k: 'iptal' });
  odaKapat(o, 500);
}
function oyuncuAyrildi(o, rol) {
  if (o.bitti2) return;
  if (!o.basladi || Date.now() - o.t0 < MIN_MAC_MS) return macIptal(o);
  if (o.v2 && o.bot) {
    const oy = o.oy[rol]; if (oy) oy.ayrildi = true;
    if (o.roller.every(r => o.oy[r] && o.oy[r].ayrildi)) macIptal(o);
    return;
  }
  if (o.v2) {
    const oy = o.oy[rol]; if (oy) oy.ayrildi = true;
    const takimGitti = renk => o.roller.filter(r => o.oy[r] && o.oy[r].renk === renk).every(r => o.oy[r].ayrildi);
    const mg = takimGitti('mavi'), kg = takimGitti('kirmizi');
    if (mg && kg) return macIptal(o);
    if (mg) return macBitirV2(o, 'kirmizi', 'ayrildi');
    if (kg) return macBitirV2(o, 'mavi', 'ayrildi');
    return;
  }
  macBitir(o, digerRol(rol), 'ayrildi');
}

/* ---------------- Sonucu Hugging Face'e bildir ---------------- */
function sonucBildir(sonuc) {
  if (!HF_URL || !SECRET || typeof fetch !== 'function') { console.warn('[SONUC] HF_URL/MAC_SECRET yok, bildirilemedi:', sonuc.mid); return; }
  const govde = JSON.stringify(sonuc);
  const imza = crypto.createHmac('sha256', SECRET).update(govde).digest('hex');
  const bekleme = [1000, 3000, 8000, 20000, 45000, 90000, 180000, 300000];
  let deneme = 0;
  const dene = async () => {
    const ctl = new AbortController(), zt = setTimeout(() => ctl.abort(), 20000);
    try {
      const r = await fetch(HF_URL + '/internal/mac-sonuc', { method: 'POST', headers: { 'content-type': 'application/json', 'x-sig': imza }, body: govde, signal: ctl.signal });
      if (r.ok) { console.log('[SONUC] iletildi', sonuc.mid); return; }
      if (r.status >= 400 && r.status < 500 && r.status !== 429 && r.status !== 408) { console.error('[SONUC] reddedildi', r.status, sonuc.mid); return; }
      throw new Error('http ' + r.status);
    } catch (e) {
      if (deneme >= bekleme.length) { console.error('[SONUC] VAZGEÇİLDİ', sonuc.mid, e.message); return; }
      setTimeout(dene, bekleme[deneme++]);
    } finally { clearTimeout(zt); }
  };
  dene();
}

/* ---------------- Ana döngü: sabit 60 Hz ---------------- */
let dongu = null, sonHr = 0n, birikim = 0;
function donguBaslat() {
  if (dongu) return;
  sonHr = process.hrtime.bigint(); birikim = 0;
  dongu = setInterval(() => {
    const now = process.hrtime.bigint();
    birikim += Number(now - sonHr) / 1e6; sonHr = now;
    if (birikim > 250) birikim = 250;
    let n = 0;
    while (birikim >= STEP && n < 8) {
      birikim -= STEP; n++;
      for (const o of odalar.values()) if (o.basladi && !o.bitti2) { adim(o); if (!o.bitti2) goruntu(o); }
    }
    if (!odalar.size) { clearInterval(dongu); dongu = null; }
  }, 4);
}

/* ---------------- Bakım (1 sn) ---------------- */
setInterval(() => {
  const now = Date.now();
  for (const o of [...odalar.values()]) {
    if (o.bitti2) continue;
    if (!o.basladi) {
      if (now - o.olusma > ODA_BEKLEME_MS) macIptal(o);
      continue;
    }
    const gidenler = [];
    for (const r of o.roller) {
      const oy = o.oy[r];
      if (!oy || oy.ayrildi) continue;
      if (oy.bagli && now - oy.gor > SUSKUNLUK_MS) { try { oy.ws.terminate(); } catch (_) {} }
      if (!oy.bagli && oy.kopus && now - oy.kopus > KOPMA_TOLERANS) gidenler.push(r);
    }
    if (o.v2) { for (const r of gidenler) { if (o.bitti2) break; oyuncuAyrildi(o, r); } continue; }
    if (gidenler.length === 2) macIptal(o);
    else if (gidenler.length === 1) oyuncuAyrildi(o, gidenler[0]);
  }
  for (const [id, t] of bitenler) if (now - t > 4 * 3600e3) bitenler.delete(id);
}, 1000);

/* ---------------- HTTP ---------------- */
const CORS = { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Methods': 'GET,OPTIONS' };
const server = http.createServer((req, res) => {
  if (req.method === 'OPTIONS') { res.writeHead(204, CORS); return res.end(); }
  const yol = req.url.split('?')[0];
  if (yol === '/health' || yol === '/') {
    res.writeHead(200, Object.assign({ 'Content-Type': 'application/json', 'Cache-Control': 'no-store' }, CORS));
    return res.end(JSON.stringify({ ok: 1, odalar: odalar.size }));
  }
  res.writeHead(404, CORS); res.end();
});
server.on('connection', s => { try { s.setNoDelay(true); } catch (_) {} });

/* ---------------- WebSocket ---------------- */
const wss = new WebSocketServer({ server, maxPayload: 2048, perMessageDeflate: false });
const EMOJI_ID = /^[a-z0-9_]{1,24}$/;

function odayaAl(ws, p) {
  const T = (p.m === 2 || p.m === 3) ? p.m : 1, bot = T > 1 && p.bot === 1;
  if (bitenler.has(p.mid)) return gonder(ws, { k: 'iptal' }), ws.close();
  let o = odalar.get(p.mid);
  if (!o) { o = yeniOda(p.mid, T, bot, p.r === 'mavi' ? 'kirmizi' : 'mavi', bot ? (p.n | 0) : T); odalar.set(p.mid, o); donguBaslat(); }
  if (o.bitti2 || o.T !== T || o.bot !== bot) return gonder(ws, { k: 'iptal' }), ws.close();
  let oy = o.oy[p.p];
  if (T === 1) {
    const diger = o.oy[digerRol(p.p)];
    if (diger && diger.renk === p.r) return ws.close();
  }
  if (!oy) oy = o.oy[p.p] = { rol: p.p, renk: p.r, slot: T > 1 ? p.s : 0, ws: null, bagli: false, gor: 0, kopus: 0, gSeq: 0, emojiT: 0, ayrildi: false };
  else if (oy.renk !== p.r) return ws.close();
  if (oy.ws && oy.ws !== ws) { oy.ws.oy = null; try { oy.ws.close(); } catch (_) {} }
  oy.ws = ws; oy.bagli = true; oy.gor = Date.now(); oy.kopus = 0;
  ws.oy = oy; ws.oda = o;
  gonder(ws, { k: 'ok' });
  o.sSonAnahtar = '';
  if (o.basladi) gonder(ws, { k: 'go' });
  else if (o.roller.every(r => o.oy[r] && o.oy[r].bagli)) {
    o.basladi = true; o.t0 = Date.now();
    yayin(o, { k: 'go' });
  }
}

wss.on('connection', ws => {
  ws.canli = true; ws.oy = null; ws.oda = null; ws.msjSay = 0; ws.msjT = Date.now();
  const zt = setTimeout(() => { if (!ws.oy) ws.terminate(); }, 15000);
  ws.on('pong', () => { ws.canli = true; });
  ws.on('message', raw => {
    ws.canli = true;
    const now = Date.now();
    if (now - ws.msjT > 1000) { ws.msjT = now; ws.msjSay = 0; }
    if (++ws.msjSay > 200) return;
    let m; try { m = JSON.parse(raw); } catch (_) { return; }
    if (!m || typeof m !== 'object') return;
    if (m.k === 'hi') {
      if (ws.oy) return;
      const p = biletCoz(m.tk);
      if (!p) { gonder(ws, { k: 'iptal' }); return ws.close(); }
      return odayaAl(ws, p);
    }
    const oy = ws.oy, o = ws.oda;
    if (!oy || !o || o.bitti2) return;
    oy.gor = now;
    switch (m.k) {
      case 'pi': if (typeof m.t === 'number') gonder(ws, { k: 'po', t: m.t }); break;
      case 'i': {
        const x = +m.x, y = +m.y;
        if (!isFinite(x) || !isFinite(y) || !o.basladi) return;
        if (typeof m.n === 'number') { if (m.n <= oy.gSeq) return; oy.gSeq = m.n; }
        const d = diskOf(o, oy), r = d.r, G = o.G;
        d.hedefX = kisitla(x, G.sol + r, G.sag - r);
        d.hedefY = oy.renk === 'mavi' ? kisitla(y, G.mid + r, G.alt - r) : kisitla(y, G.ust + r, G.mid - r);
        break;
      }
      case 'e': {
        if (typeof m.id !== 'string' || !EMOJI_ID.test(m.id) || now - oy.emojiT < 500) return;
        oy.emojiT = now;
        for (const r of o.roller) {
          if (r === oy.rol) continue;
          const dg = o.oy[r];
          if (dg) gonder(dg.ws, o.v2 ? { k: 'e', id: m.id, c: oy.renk, s: oy.slot } : { k: 'e', id: m.id });
        }
        break;
      }
      case 'bye': ws.oy = null; oy.ws = null; oy.bagli = false; oyuncuAyrildi(o, oy.rol); break;
    }
  });
  ws.on('close', () => {
    clearTimeout(zt);
    const oy = ws.oy;
    if (oy && oy.ws === ws) { oy.ws = null; oy.bagli = false; oy.kopus = Date.now(); }
  });
  ws.on('error', () => {});
});
setInterval(() => {
  for (const ws of wss.clients) { if (!ws.canli) { try { ws.terminate(); } catch (_) {} continue; } ws.canli = false; try { ws.ping(); } catch (_) {} }
}, 20000);

['SIGTERM', 'SIGINT'].forEach(s => process.on(s, () => process.exit(0)));
server.listen(PORT, () => console.log('NOXBALL maç sunucusu v2.2 :' + PORT));
