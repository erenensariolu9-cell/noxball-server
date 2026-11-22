/* =====================================================================
   NOXBALL MAÇ SUNUCUSU  (Render)   v2.0
   - SADECE maçı yönetir: fizik, skor, geri sayım, gol, bitiş. Hesap/kupa/eşleşme YOKTUR (hepsi Hugging Face'te).
   - Hugging Face oyuncuları eşleyince her oyuncuya İMZALI BİR BİLET verir (HMAC, MAC_SECRET ile).
   - Maç bitince sonuç, imzalı bir HTTP isteğiyle Hugging Face'e bildirilir.
   YENİ (v2.0):
     - 3v3 modu + 2v2 / 3v3'te BÜYÜK SAHA (2v2: 1.3x, 3v3: 1.6x; kale de oranlı büyür)
     - Aynı takımdaki diskler artık birbirinin üstüne çıkamaz (diskler arası çarpışma)
     - Bot maçı düzeltildi: insanlar her zaman a,b,c rollerinde (kırmızı takım bilet hatası giderildi)
     - Ağ: TCP_NODELAY, permessage-deflate kapalı, daha hafif anlık görüntü
   Biletteki  m: 2|3  takım boyutu (2v2 / 3v3), s = takım içi sıra (0..m-1). m yoksa 1v1.
   Roller: 1v1 a,b | 2v2 mavi=a,b kırmızı=c,d | 3v3 mavi=a,b,c kırmızı=d,e,f | bot maçı: insanlar a,b,c...
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

// Saha büyütme katsayısı (takım boyutuna göre). oyun.html'deki TAKIM_ZOOM ile AYNI olmalı.
const ZOOM = { 1: 1, 2: 1.3, 3: 1.6 };
function geo(f) {
  const w = 320 * f, h = 530 * f, cx = 40 + w / 2;
  return { f, sol: 40, ust: 35, w, h, sag: 40 + w, alt: 35 + h, mid: 35 + h / 2, cx, kSol: cx - 70 * f, kSag: cx + 70 * f };
}
const GEO = { 1: geo(ZOOM[1]), 2: geo(ZOOM[2]), 3: geo(ZOOM[3]) };
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
function yeniDisk(p) { return { x: p.x, y: p.y, r: 24, vx: 0, vy: 0, hedefX: p.x, hedefY: p.y, ox0: p.x, oy0: p.y }; }
function yeniOda(id, T, bot, botRenk, insan) {
  const G = GEO[T];
  const o = {
    id, T, v2: T > 1, G, bot: !!bot, botRenk: botRenk || '', insan: Math.max(1, Math.min(T, insan || T)),
    olusma: Date.now(), t0: 0, basladi: false, bitti2: false,
    oy: {}, roller: [],
    top: { x: G.cx, y: G.mid, r: 14, vx: 0, vy: 0, surtunme: 0.986, aci: 0 },
    dk: { mavi: [], kirmizi: [] }, liste: [],
    gol: { aktif: false, kim: '', z: 0 },
    skorM: 0, skorK: 0, bitenKim: null, sonVuran: 'mavi', sayac: GERI_SAYIM, tick: 0,
    sSonAnahtar: '', sSonG: 0, sSonV: 0, sSonZaman: 0
  };
  for (const renk of ['mavi', 'kirmizi']) for (let s = 0; s < T; s++) { const d = yeniDisk(baslangic(G, T, renk, s)); o.dk[renk].push(d); o.liste.push([d, renk]); }
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
    if (hizli && oy.ws.bufferedAmount > 16384) continue;     // hat tıkandı: eski görüntüyü biriktirme
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
// Aynı takımdaki diskler birbirinin içine giremez (eşit itiş). Rakip diskler zaten ayrı yarı sahalarda.
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
  const t = o.top;
  const dx = t.x - disk.x, dy = t.y - disk.y, mesafe = Math.sqrt(dx * dx + dy * dy), minM = t.r + disk.r;
  if (mesafe < minM && mesafe > 0) {
    const ic = minM - mesafe, nx = dx / mesafe, ny = dy / mesafe;
    t.x += nx * ic; t.y += ny * ic;
    const vg = Math.sqrt(disk.vx * disk.vx + disk.vy * disk.vy);
    t.vx = nx * (vg * 0.95 + 4.2) + disk.vx * 0.35;
    t.vy = ny * (vg * 0.95 + 4.2) + disk.vy * 0.35;
    o.sonVuran = renk; olay(o, 1);
    const mh = Math.sqrt(t.vx * t.vx + t.vy * t.vy);
    if (mh > MAX_TOP_HIZI) { t.vx = (t.vx / mh) * MAX_TOP_HIZI; t.vy = (t.vy / mh) * MAX_TOP_HIZI; }
  }
}
function direkCarpismasi(o, px, py) {
  const t = o.top, dx = t.x - px, dy = t.y - py, dist = Math.sqrt(dx * dx + dy * dy), minD = t.r + DIREK_R;
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
  o.sonVuran = 'mavi';
}

/* ---- BOT ---- rol: 0 hücum, 1 savunma, 2 orta saha. alt: bu bot mavi mi (kendi kalesi altta). */
function botDisk(o, d, alt, rol) {
  const G = o.G, f = G.f, t = o.top, toplam = G.ust + G.alt;
  const P = y => alt ? toplam - y : y;                  // bot bakışı: kendi kalesi hep y küçük tarafta
  const bx = t.x, by = P(t.y), bvx = t.vx, bvy = alt ? -t.vy : t.vy;
  let tx, ty;
  if (rol === 0) {
    if (by < G.mid + 30 * f) { tx = bx + bvx * 3; ty = kisitla(by + bvy * 2 - 24, G.ust + 24, G.mid - 24); }
    else { tx = G.cx + (bx - G.cx) * 0.3; ty = G.ust + 135 * f; }
  } else if (rol === 1) {
    tx = kisitla(bx, G.cx - 50 * f, G.cx + 50 * f); ty = by < G.mid - 50 * f ? G.ust + 100 * f : G.ust + 50 * f;
  } else {
    tx = G.cx + (bx - G.cx) * 0.6; ty = Math.min(G.mid - 24, Math.max(G.ust + 120 * f, by - 90 * f));
  }
  const wy = alt ? toplam - ty : ty, dx = tx - d.x, dy = wy - d.y, dist = Math.hypot(dx, dy) || 1, k = Math.min(1, 10 * Math.sqrt(f) / dist);
  d.hedefX = kisitla(d.x + dx * k, G.sol + d.r, G.sag - d.r);
  d.hedefY = alt ? kisitla(d.y + dy * k, G.mid + d.r, G.alt - d.r) : kisitla(d.y + dy * k, G.ust + d.r, G.mid - d.r);
}
function botAdim(o) {
  const alt = o.botRenk === 'mavi';
  o.dk[o.botRenk].forEach((d, i) => botDisk(o, d, alt, i % 3));                         // rakip takımın tamamı bot
  const hr = alt ? 'kirmizi' : 'mavi';
  for (let s = o.insan; s < o.T; s++) botDisk(o, o.dk[hr][s], !alt, s === 1 ? 1 : 2);   // insan takımında boş kalan yerler bot
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

// Anlık görüntü. 1v1: k:'s'   Takım: k:'s2'  (m ve r dizileri 2*T sayı: [x0,y0,x1,y1,...])
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
  if (g === 0 && !durumDegisti && anahtar === o.sSonAnahtar && now - o.sSonZaman < 250) return;   // hiçbir şey kıpırdamıyor: bant genişliği harcama
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
function macBitir(o, kazRol, neden) {          // 1v1
  if (o.bitti2) return;
  const kazRenk = renkOf(o, kazRol);
  yayin(o, { k: 'son', w: kazRenk, m: o.skorM, r: o.skorK, n: neden });
  const golOf = rol => renkOf(o, rol) === 'mavi' ? o.skorM : o.skorK;
  sonucBildir({ mid: o.id, kazanan: kazRol, gol: { a: golOf('a'), b: golOf('b') }, neden: neden, sure: Date.now() - o.t0 });
  odaKapat(o, 2500);
}
function macBitirV2(o, kazRenk, neden) {       // 2v2 / 3v3: kazanan takım rengi
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
    if (o.roller.every(r => o.oy[r] && o.oy[r].ayrildi)) macIptal(o);   // bütün insanlar gitti
    return;
  }
  if (o.v2) {
    const oy = o.oy[rol]; if (oy) oy.ayrildi = true;
    const takimGitti = renk => o.roller.filter(r => o.oy[r] && o.oy[r].renk === renk).every(r => o.oy[r].ayrildi);
    const mg = takimGitti('mavi'), kg = takimGitti('kirmizi');
    if (mg && kg) return macIptal(o);
    if (mg) return macBitirV2(o, 'kirmizi', 'ayrildi');
    if (kg) return macBitirV2(o, 'mavi', 'ayrildi');
    return;                                   // takımdan biri gitti, diğerleri devam ediyor
  }
  macBitir(o, digerRol(rol), 'ayrildi');
}

/* ---------------- Sonucu Hugging Face'e bildir (imzalı, tekrar denemeli) ---------------- */
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

/* ---------------- Ana döngü: tüm odalar sabit 60 Hz ---------------- */
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
server.on('connection', s => { try { s.setNoDelay(true); } catch (_) {} });   // Nagle kapalı: düşük ping

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
    if (diger && diger.renk === p.r) return ws.close();            // aynı renk iki oyuncu: olmamalı
  }
  if (!oy) oy = o.oy[p.p] = { rol: p.p, renk: p.r, slot: T > 1 ? p.s : 0, ws: null, bagli: false, gor: 0, kopus: 0, gSeq: 0, emojiT: 0, ayrildi: false };
  else if (oy.renk !== p.r) return ws.close();
  if (oy.ws && oy.ws !== ws) { oy.ws.oy = null; try { oy.ws.close(); } catch (_) {} }
  oy.ws = ws; oy.bagli = true; oy.gor = Date.now(); oy.kopus = 0;
  ws.oy = oy; ws.oda = o;
  gonder(ws, { k: 'ok' });
  o.sSonAnahtar = '';
  if (o.basladi) gonder(ws, { k: 'go' });
  else if (o.roller.every(r => o.oy[r] && o.oy[r].bagli)) {          // herkes hazır: maç başlıyor
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
      case 'e': {                                                // emoji: diğer herkese ilet (takım modunda kimin gönderdiği de gider)
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
server.listen(PORT, () => console.log('NOXBALL maç sunucusu v2.0 :' + PORT));
