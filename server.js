/* =====================================================================
   NOXBALL MAÇ SUNUCUSU  (Render)
   - SADECE maçı yönetir: fizik, skor, geri sayım, gol, bitiş. Hesap/kupa/eşleşme YOKTUR (hepsi Hugging Face'te).
   - Hugging Face iki oyuncuyu eşleyince her oyuncuya İMZALI BİR BİLET verir (HMAC, MAC_SECRET ile).
     Oyuncu bu bileti buraya WebSocket ile getirir. Bilet geçerliyse oyuncu odaya alınır.
   - Maç bitince sonuç, imzalı bir HTTP isteğiyle Hugging Face'e bildirilir (kupa/görev orada işlenir).
   - Fizik, oyun.html'deki eski "host" fiziğinin BİREBİR kopyasıdır (istemci tahmini aynı kuralları kullanır).
   Ortam değişkenleri (Render > Environment):
        MAC_SECRET  (ZORUNLU)  Hugging Face'teki ile AYNI uzun rastgele metin
        HF_URL      (ZORUNLU)  örn. https://noxball-noxball-server.hf.space
        PORT        Render kendisi verir (varsayılan 10000)
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

/* ---------------- Oyun sabitleri (oyun.html ile aynı) ---------------- */
const STEP = 1000 / 60;
const SAHA = { sol: 40, sag: 360, ust: 35, alt: 565, koseR: 30 };
const KALE = { sol: 130, sag: 270, derinlik: 24, direkR: 5 };
const SEKME = 0.94;
const MAX_TOP_HIZI = 17;
const HEDEF_GOL = 3;
const GERI_SAYIM = 180;          // 3 sn
const GOL_KUTLAMA = 180;         // 3 sn
const MIN_MAC_MS = 15000;        // bundan kısa süren maçta ayrılan olursa maç İPTAL (sonuç yok)
const KOPMA_TOLERANS = 6000;     // bağlantısı kopan oyuncuya geri dönmesi için süre
const SUSKUNLUK_MS = 7000;       // bu kadar süre hiç mesaj gelmezse bağlantı ölü sayılır (istemci her sn ping atar)
const ODA_BEKLEME_MS = 80000;    // iki oyuncu bu sürede gelmezse oda iptal (Render uykudan kalkarken uzun tutuldu)

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
  if (!p || typeof p.mid !== 'string' || (p.p !== 'a' && p.p !== 'b') || (p.r !== 'mavi' && p.r !== 'kirmizi') || !(p.exp > Date.now())) return null;
  return p;
}

/* ---------------- Odalar ---------------- */
const odalar = new Map();    // mid -> oda
const bitenler = new Map();  // mid -> bitiş zamanı (aynı bilet ikinci kez oda açamasın)

function yeniOda(id) {
  return {
    id, olusma: Date.now(), t0: 0, basladi: false, bitti2: false,
    oy: { a: null, b: null },
    top: { x: 200, y: 300, r: 14, vx: 0, vy: 0, surtunme: 0.986, aci: 0 },
    mavi: { x: 200, y: 480, r: 24, vx: 0, vy: 0, hedefX: 200, hedefY: 480 },
    kirmizi: { x: 200, y: 120, r: 24, vx: 0, vy: 0, hedefX: 200, hedefY: 120 },
    gol: { aktif: false, kim: '', z: 0 },
    skorM: 0, skorK: 0, bitenKim: null, sonVuran: 'mavi', sayac: GERI_SAYIM, tick: 0,
    sSonAnahtar: '', sSonG: 0, sSonV: 0, sSonZaman: 0
  };
}
const zaman = o => Math.round(o.tick * STEP * 10) / 10;
function gonder(ws, obj) { if (ws && ws.readyState === 1) { try { ws.send(typeof obj === 'string' ? obj : JSON.stringify(obj)); } catch (_) {} } }
function yayin(o, obj, hizli) {
  const s = JSON.stringify(obj);
  for (const r of ['a', 'b']) {
    const oy = o.oy[r];
    if (!oy || !oy.ws || oy.ws.readyState !== 1) continue;
    if (hizli && oy.ws.bufferedAmount > 16384) continue;   // tıkanmış hat: eski görüntüyü biriktirme
    try { oy.ws.send(s); } catch (_) {}
  }
}
const diskOf = (o, oy) => oy.renk === 'mavi' ? o.mavi : o.kirmizi;

/* ---------------- FİZİK (oyun.html fizikGuncelle birebir) ---------------- */
function diskHareket(d) {
  const ex = d.x, ey = d.y;
  d.x += (d.hedefX - d.x) * 0.35;
  d.y += (d.hedefY - d.y) * 0.35;
  d.vx = d.x - ex; d.vy = d.y - ey;
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
  const t = o.top, dx = t.x - px, dy = t.y - py, dist = Math.sqrt(dx * dx + dy * dy), minD = t.r + KALE.direkR;
  if (dist < minD && dist > 0) {
    const nx = dx / dist, ny = dy / dist;
    t.x = px + nx * minD; t.y = py + ny * minD;
    const dot = t.vx * nx + t.vy * ny;
    if (dot < 0) { t.vx = (t.vx - 2 * dot * nx) * SEKME; t.vy = (t.vy - 2 * dot * ny) * SEKME; olay(o, 2); }
  }
}
function koseCarpismasi(o, cx, cy) {
  const t = o.top, dx = t.x - cx, dy = t.y - cy, dist = Math.sqrt(dx * dx + dy * dy), maxD = SAHA.koseR - t.r;
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
  if (o.skorM >= HEDEF_GOL || o.skorK >= HEDEF_GOL) o.bitenKim = kim;   // ilk 3 gol: kutlamadan sonra maç biter
  t.vx *= 0.2; t.vy *= 0.2;
}
function santraSifirla(o) {
  const t = o.top;
  o.gol.aktif = false;
  t.x = 200; t.y = 300; t.vx = 0; t.vy = 0;
  Object.assign(o.mavi, { x: 200, y: 480, hedefX: 200, hedefY: 480, vx: 0, vy: 0 });
  Object.assign(o.kirmizi, { x: 200, y: 120, hedefX: 200, hedefY: 120, vx: 0, vy: 0 });
  o.sonVuran = 'mavi';
}

function adim(o) {
  const t = o.top;
  if (o.sayac > 0) { o.sayac--; diskHareket(o.mavi); diskHareket(o.kirmizi); return; }   // maç başı geri sayım: top durur, diskler hareket eder

  if (o.gol.aktif) {
    o.gol.z--;
    t.x += t.vx; t.y += t.vy; t.vx *= 0.85; t.vy *= 0.85;
    if (o.gol.z <= 0) {
      if (o.bitenKim) macBitir(o, o.bitenKim === 'mavi' ? rolOf(o, 'mavi') : rolOf(o, 'kirmizi'), 'bitti');
      else santraSifirla(o);
    }
    return;
  }

  diskHareket(o.mavi); diskHareket(o.kirmizi);

  let gh = Math.sqrt(t.vx * t.vx + t.vy * t.vy);
  if (gh > MAX_TOP_HIZI) { t.vx = (t.vx / gh) * MAX_TOP_HIZI; t.vy = (t.vy / gh) * MAX_TOP_HIZI; }
  t.x += t.vx; t.y += t.vy;
  t.aci += (t.vx + t.vy) * 0.035;
  t.vx *= t.surtunme; t.vy *= t.surtunme;
  if (Math.abs(t.vx) < 0.05) t.vx = 0;
  if (Math.abs(t.vy) < 0.05) t.vy = 0;

  direkCarpismasi(o, KALE.sol, SAHA.ust); direkCarpismasi(o, KALE.sag, SAHA.ust);
  direkCarpismasi(o, KALE.sol, SAHA.alt); direkCarpismasi(o, KALE.sag, SAHA.alt);

  if (t.x < SAHA.sol + SAHA.koseR && t.y < SAHA.ust + SAHA.koseR) koseCarpismasi(o, SAHA.sol + SAHA.koseR, SAHA.ust + SAHA.koseR);
  else if (t.x > SAHA.sag - SAHA.koseR && t.y < SAHA.ust + SAHA.koseR) koseCarpismasi(o, SAHA.sag - SAHA.koseR, SAHA.ust + SAHA.koseR);
  else if (t.x < SAHA.sol + SAHA.koseR && t.y > SAHA.alt - SAHA.koseR) koseCarpismasi(o, SAHA.sol + SAHA.koseR, SAHA.alt - SAHA.koseR);
  else if (t.x > SAHA.sag - SAHA.koseR && t.y > SAHA.alt - SAHA.koseR) koseCarpismasi(o, SAHA.sag - SAHA.koseR, SAHA.alt - SAHA.koseR);
  else {
    if (t.x - t.r < SAHA.sol) { t.x = SAHA.sol + t.r; t.vx *= -SEKME; }
    else if (t.x + t.r > SAHA.sag) { t.x = SAHA.sag - t.r; t.vx *= -SEKME; }

    if (t.x > KALE.sol && t.x < KALE.sag) {
      if (t.y + t.r < SAHA.ust) golBaslat(o, 'mavi');
    } else if (t.y - t.r < SAHA.ust) { t.y = SAHA.ust + t.r; t.vy *= -SEKME; }

    if (t.x > KALE.sol && t.x < KALE.sag) {
      if (t.y - t.r > SAHA.alt) golBaslat(o, 'kirmizi');
    } else if (t.y + t.r > SAHA.alt) { t.y = SAHA.alt - t.r; t.vy *= -SEKME; }
  }
  carpismayiCoz(o, o.mavi, 'mavi');
  carpismayiCoz(o, o.kirmizi, 'kirmizi');
}

// Anlık görüntü: değişmediyse (ve 250 ms dolmadıysa) gönderilmez; yüksek ping/bant için tasarruf
function goruntu(o) {
  o.tick++;
  const t = o.top;
  const g = o.gol.aktif ? (o.gol.kim === 'mavi' ? 1 : 2) : 0, v = o.sonVuran === 'kirmizi' ? 1 : 0;
  const durumDegisti = g !== o.sSonG || v !== o.sSonV;
  const r = q => Math.round(q * 10) / 10;
  const b = [r(t.x), r(t.y), r(t.vx), r(t.vy), Math.round(t.aci * 100) / 100];
  const m = [r(o.mavi.x), r(o.mavi.y)], rk = [r(o.kirmizi.x), r(o.kirmizi.y)];
  const now = Date.now();
  const anahtar = b.join() + '|' + m.join() + '|' + rk.join() + '|' + g + v + '|' + Math.ceil(o.sayac / 60);
  if (g === 0 && !durumDegisti && anahtar === o.sSonAnahtar && now - o.sSonZaman < 250) return;
  o.sSonAnahtar = anahtar; o.sSonZaman = now; o.sSonG = g; o.sSonV = v;
  yayin(o, { k: 's', t: zaman(o), b: b, m: m, r: rk, g: g, z: o.gol.z, v: v, c: o.sayac }, true);
}

/* ---------------- Maç yaşam döngüsü ---------------- */
const rolOf = (o, renk) => (o.oy.a && o.oy.a.renk === renk) ? 'a' : 'b';
const digerRol = r => r === 'a' ? 'b' : 'a';
const renkOf = (o, rol) => o.oy[rol] ? o.oy[rol].renk : null;

function odaKapat(o, gecikme) {
  o.bitti2 = true;
  bitenler.set(o.id, Date.now());
  setTimeout(() => {
    for (const r of ['a', 'b']) { const oy = o.oy[r]; if (oy && oy.ws) { oy.ws.oy = null; try { oy.ws.close(); } catch (_) {} } }
    odalar.delete(o.id);
  }, gecikme || 0);
}
// kazRol: 'a' | 'b'.  Sonuç Hugging Face'e gider, oyunculara bitiş mesajı gider.
function macBitir(o, kazRol, neden) {
  if (o.bitti2) return;
  const kazRenk = renkOf(o, kazRol);
  yayin(o, { k: 'son', w: kazRenk, m: o.skorM, r: o.skorK, n: neden });
  const golOf = rol => renkOf(o, rol) === 'mavi' ? o.skorM : o.skorK;
  sonucBildir({ mid: o.id, kazanan: kazRol, gol: { a: golOf('a'), b: golOf('b') }, neden: neden, sure: Date.now() - o.t0 });
  odaKapat(o, 2500);
}
// Sonuçsuz iptal: kalan oyuncu istemcide yeniden eşleşmeye döner
function macIptal(o) {
  if (o.bitti2) return;
  yayin(o, { k: 'iptal' });
  odaKapat(o, 500);
}
// Bir oyuncu gitti: maç yeterince sürdüyse diğeri kazanır, yoksa iptal
function oyuncuAyrildi(o, rol) {
  if (o.bitti2) return;
  if (!o.basladi || Date.now() - o.t0 < MIN_MAC_MS) return macIptal(o);
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
    if (birikim > 250) birikim = 250;   // uzun takılmadan sonra hızlı sarma yapma
    let n = 0;
    while (birikim >= STEP && n < 8) {
      birikim -= STEP; n++;
      for (const o of odalar.values()) if (o.basladi && !o.bitti2) { adim(o); if (!o.bitti2) goruntu(o); }
    }
    if (!odalar.size) { clearInterval(dongu); dongu = null; }
  }, 5);
}

/* ---------------- Bakım (1 sn): kopma / sessizlik / bekleme zaman aşımı ---------------- */
setInterval(() => {
  const now = Date.now();
  for (const o of [...odalar.values()]) {
    if (o.bitti2) continue;
    if (!o.basladi) {
      if (now - o.olusma > ODA_BEKLEME_MS) macIptal(o);
      continue;
    }
    const gidenler = [];
    for (const r of ['a', 'b']) {
      const oy = o.oy[r];
      if (!oy) continue;
      if (oy.bagli && now - oy.gor > SUSKUNLUK_MS) { try { oy.ws.terminate(); } catch (_) {} }   // ölü bağlantı: close olayı kopmayı işler
      if (!oy.bagli && oy.kopus && now - oy.kopus > KOPMA_TOLERANS) gidenler.push(r);
    }
    if (gidenler.length === 2) macIptal(o);                       // ikisi de gitti: sonuçsuz
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

/* ---------------- WebSocket ---------------- */
const wss = new WebSocketServer({ server, maxPayload: 2048 });
const EMOJI_ID = /^[a-z0-9_]{1,24}$/;
const kisitla = (v, a, b) => Math.max(a, Math.min(b, v));

function odayaAl(ws, p) {
  if (bitenler.has(p.mid)) return gonder(ws, { k: 'iptal' }), ws.close();
  let o = odalar.get(p.mid);
  if (!o) { o = yeniOda(p.mid); odalar.set(p.mid, o); donguBaslat(); }
  if (o.bitti2) return gonder(ws, { k: 'iptal' }), ws.close();
  let oy = o.oy[p.p];
  const diger = o.oy[digerRol(p.p)];
  if (diger && diger.renk === p.r) return ws.close();            // aynı renk iki oyuncu: imzalı biletlerde olmaması gerekir
  if (!oy) oy = o.oy[p.p] = { rol: p.p, renk: p.r, ws: null, bagli: false, gor: 0, kopus: 0, gSeq: 0, emojiT: 0 };
  else if (oy.renk !== p.r) return ws.close();
  if (oy.ws && oy.ws !== ws) { oy.ws.oy = null; try { oy.ws.close(); } catch (_) {} }   // aynı biletle yeni bağlantı: eskisi düşer
  oy.ws = ws; oy.bagli = true; oy.gor = Date.now(); oy.kopus = 0;
  ws.oy = oy; ws.oda = o;
  gonder(ws, { k: 'ok' });
  o.sSonAnahtar = '';                                            // yeni bağlanan hemen güncel görüntü alsın
  if (o.basladi) gonder(ws, { k: 'go' });                        // yeniden bağlanma
  else if (o.oy.a && o.oy.b && o.oy.a.bagli && o.oy.b.bagli) {   // iki oyuncu da hazır: maç başlıyor
    o.basladi = true; o.t0 = Date.now();
    yayin(o, { k: 'go' });
  }
}

wss.on('connection', ws => {
  ws.canli = true; ws.oy = null; ws.oda = null; ws.msjSay = 0; ws.msjT = Date.now();
  const zt = setTimeout(() => { if (!ws.oy) ws.terminate(); }, 15000);   // bilet göstermeyen bağlantıyı at
  ws.on('pong', () => { ws.canli = true; });
  ws.on('message', raw => {
    ws.canli = true;
    const now = Date.now();
    if (now - ws.msjT > 1000) { ws.msjT = now; ws.msjSay = 0; }
    if (++ws.msjSay > 200) return;                               // saniyede en fazla 200 mesaj
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
      case 'i': {                                                // hedef konum (dünya koordinatı)
        const x = +m.x, y = +m.y;
        if (!isFinite(x) || !isFinite(y) || !o.basladi) return;
        if (typeof m.n === 'number') { if (m.n <= oy.gSeq) return; oy.gSeq = m.n; }
        const d = diskOf(o, oy), r = d.r;
        d.hedefX = kisitla(x, SAHA.sol + r, SAHA.sag - r);
        d.hedefY = oy.renk === 'mavi' ? kisitla(y, 300 + r, SAHA.alt - r) : kisitla(y, SAHA.ust + r, 300 - r);
        break;
      }
      case 'e': {                                                // emoji: rakibe ilet
        if (typeof m.id !== 'string' || !EMOJI_ID.test(m.id) || now - oy.emojiT < 500) return;
        oy.emojiT = now;
        const dg = o.oy[digerRol(oy.rol)];
        if (dg) gonder(dg.ws, { k: 'e', id: m.id });
        break;
      }
      case 'bye': ws.oy = null; oy.ws = null; oy.bagli = false; oyuncuAyrildi(o, oy.rol); break;   // oyuncu bilerek ayrıldı
    }
  });
  ws.on('close', () => {
    clearTimeout(zt);
    const oy = ws.oy;
    if (oy && oy.ws === ws) { oy.ws = null; oy.bagli = false; oy.kopus = Date.now(); }   // tolerans süresi içinde aynı biletle dönebilir
  });
  ws.on('error', () => {});
});
setInterval(() => {
  for (const ws of wss.clients) { if (!ws.canli) { try { ws.terminate(); } catch (_) {} continue; } ws.canli = false; try { ws.ping(); } catch (_) {} }
}, 20000);

['SIGTERM', 'SIGINT'].forEach(s => process.on(s, () => process.exit(0)));
server.listen(PORT, () => console.log('NOXBALL maç sunucusu :' + PORT));
