/* =====================================================================
   NOXBALL SERVER  (Hugging Face Space - Docker)
   - Hesap / kupa / görev / envanter / KLAN verisi RAM'de (Map) tutulur: okuma-yazma anlık.
   - KALICILIK (3 katman):
       1) Yerel disk (DATA_DIR/db.json)            -> ~2 sn'de bir, yeniden başlatmaya karşı
       2) HF Dataset yedeği (db.json.gz, özel repo) -> yeni sürüm / rebuild / Space silinse bile veri kalır
       3) Açılışta bulut yedeği otomatik geri yüklenir
   - Ortam değişkenleri (Space > Settings > Variables and secrets):
        ADMIN_KEY   (SECRET)  admin paneli şifresi. ZORUNLU.
        HF_TOKEN    (SECRET)  "Write" yetkili Hugging Face token  -> bulut yedeği için ZORUNLU
        HF_DATASET  (opsiyonel) varsayılan: <hesapadın>/noxball-data  (özel dataset, yoksa otomatik oluşturulur)
        METERED_APP / METERED_KEY (SECRET) Metered Open Relay TURN (kredi kartsız, 20 GB/ay)
        CF_TURN_KEY_ID / CF_TURN_TOKEN (SECRET) Cloudflare Realtime TURN (kart ister) Cloudflare Realtime TURN (ücretsiz) -> ping/ışınlanma sorununa en iyi çözüm
        TURN_URLS / TURN_USER / TURN_PASS (opsiyonel) Cloudflare yerine kendi TURN sunucun
        DATA_DIR    (opsiyonel) varsayılan /data, yoksa ./data
   ===================================================================== */
const http = require('http');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = +process.env.PORT || 7860;
const ADMIN_KEY = process.env.ADMIN_KEY || '';
const BASLANGIC = { altin: 275, elmas: 50 };
const NICK_UCRET = 100;
const KUPA_KAZAN = 20, KUPA_KAYIP = 5, KAZAN_ALTIN = 25;
const MIN_MAC_MS = 15000;
const KLAN_MAX_UYE = 30;          // bir klandaki en fazla oyuncu
const CEVRIMICI_MS = 15000;       // bu süre içinde sunucuyla konuşan oyuncu "çevrimiçi" sayılır (oyun 3 sn'de bir konuşur)

/* ---------------- Yerel disk ---------------- */
function veriKlasoru() {
  const adaylar = [process.env.DATA_DIR, '/data', path.join(__dirname, 'data')].filter(Boolean);
  for (const d of adaylar) {
    try { fs.mkdirSync(d, { recursive: true }); fs.accessSync(d, fs.constants.W_OK); return d; } catch (_) {}
  }
  return null;
}
const DATA_DIR = veriKlasoru();
const DB_DOSYA = DATA_DIR ? path.join(DATA_DIR, 'db.json') : null;

/* ---------------- RAM veritabanı ---------------- */
const users = new Map();      // anahtar: küçük harf kullanıcı adı
const nickIndex = new Map();  // küçük harf görünen ad -> kullanıcı anahtarı
const tokens = new Map();     // token -> { key, son }
const klanlar = new Map();    // klan id -> { id, ad, et, lider(key), olusturma, sayac, msj:[{i,k,a,m,t}] }
let kirli = false, yazimTimer = null, siraCache = { t: 0, liste: [] }, klanCache = { t: 0, liste: [] };
const dbHam = () => JSON.stringify({ users: [...users.values()], tokens: [...tokens.entries()], klanlar: [...klanlar.values()] });

/* ---------------- Bulut yedeği (Hugging Face Dataset) ---------------- */
const HF_TOKEN = process.env.HF_TOKEN || '';
const HF_ENDPOINT = (process.env.HF_ENDPOINT || 'https://huggingface.co').replace(/\/+$/, '');
const HF_REPO = process.env.HF_DATASET || (process.env.SPACE_AUTHOR_NAME ? process.env.SPACE_AUTHOR_NAME + '/noxball-data' : '');
const BULUT = !!(HF_TOKEN && HF_REPO && typeof fetch === 'function');
const BULUT_ARALIK = 120000;          // değişiklik varsa en sık 2 dk'da bir commit (commit geçmişi şişmesin)
const BULUT_DOSYA = 'db.json.gz';
const bulut = { hazir: false, sonYedek: 0, sonHata: '', yazim: false, sonHash: '', deneme: 0 };

function hfBaslik(ekstra) { return Object.assign({ Authorization: 'Bearer ' + HF_TOKEN }, ekstra || {}); }
async function hfZamanli(url, opt, ms) {
  const ctl = new AbortController(), t = setTimeout(() => ctl.abort(), ms || 15000);
  try { return await fetch(url, Object.assign({ signal: ctl.signal }, opt)); } finally { clearTimeout(t); }
}
async function bulutRepoOlustur() {
  const [ns, ad] = HF_REPO.split('/');
  const r = await hfZamanli(HF_ENDPOINT + '/api/repos/create', { method: 'POST', headers: hfBaslik({ 'content-type': 'application/json' }),
    body: JSON.stringify({ name: ad, organization: ns, type: 'dataset', private: true }) });
  if (!r.ok && r.status !== 409) throw new Error('repo oluşturulamadı (' + r.status + ') ' + (await r.text()).slice(0, 120));
}
// döner: JSON nesnesi | null (bulutta henüz yedek yok). Ağ/yetki hatasında FIRLATIR (boş veriyle üzerine yazmayalım diye)
async function bulutOku() {
  const url = HF_ENDPOINT + '/datasets/' + HF_REPO + '/resolve/main/' + BULUT_DOSYA;
  let r = await hfZamanli(url, { headers: hfBaslik() }, 20000);
  if (r.status === 404 || r.status === 401) {          // repo ya da dosya yok -> repo'yu garantiye al
    await bulutRepoOlustur();
    r = await hfZamanli(url, { headers: hfBaslik() }, 20000);
    if (r.status === 404 || r.status === 401) return null;
  }
  if (!r.ok) throw new Error('okuma ' + r.status);
  const buf = Buffer.from(await r.arrayBuffer());
  return JSON.parse(zlib.gunzipSync(buf).toString('utf8'));
}
function bulutBirlestir(j) {
  let eklenen = 0;
  for (const u of j.users || []) {
    const eski = users.get(u.key);
    if (eski) { nickIndex.delete(eski.ad.toLowerCase()); for (const [t, v] of tokens) if (v.key === u.key) tokens.delete(t); }   // çakışmada bulut kazanır
    users.set(u.key, u); nickIndex.set(u.ad.toLowerCase(), u.key); eklenen++;
  }
  for (const [t, v] of j.tokens || []) if (users.has(v.key)) tokens.set(t, v);
  for (const k of j.klanlar || []) klanlar.set(k.id, k);
  return eklenen;
}
async function bulutYukle() {
  if (!BULUT) return;
  try {
    const j = await bulutOku();
    if (j) { const n = bulutBirlestir(j); console.log('[BULUT] Geri yüklendi:', n, 'hesap,', klanlar.size, 'klan  (' + HF_REPO + ')'); }
    else console.log('[BULUT] Bulutta yedek yok, yeni başlanıyor (' + HF_REPO + ')');
    bulut.hazir = true; bulut.sonHata = ''; kirli = true; siraCache.t = 0; klanCache.t = 0;
  } catch (e) {
    bulut.hazir = false; bulut.sonHata = e.message; bulut.deneme++;
    console.error('[BULUT] Yükleme başarısız (yedek yazılmayacak, tekrar denenecek):', e.message);
    setTimeout(bulutYukle, Math.min(60000, 5000 * bulut.deneme));
  }
}
async function bulutYaz(zorla) {
  if (!BULUT || !bulut.hazir || bulut.yazim) return false;
  const ham = dbHam();
  const hash = crypto.createHash('sha1').update(ham).digest('hex');
  if (!zorla && hash === bulut.sonHash) return true;
  bulut.yazim = true;
  try {
    const icerik = zlib.gzipSync(Buffer.from(ham, 'utf8')).toString('base64');
    const govde = JSON.stringify({ key: 'header', value: { summary: 'yedek ' + new Date().toISOString() + ' (' + users.size + ' hesap)' } }) + '\n' +
                  JSON.stringify({ key: 'file', value: { content: icerik, path: BULUT_DOSYA, encoding: 'base64' } }) + '\n';
    const r = await hfZamanli(HF_ENDPOINT + '/api/datasets/' + HF_REPO + '/commit/main',
      { method: 'POST', headers: hfBaslik({ 'content-type': 'application/x-ndjson' }), body: govde }, 25000);
    if (!r.ok) throw new Error('commit ' + r.status + ' ' + (await r.text()).slice(0, 120));
    bulut.sonHash = hash; bulut.sonYedek = Date.now(); bulut.sonHata = '';
    return true;
  } catch (e) { bulut.sonHata = e.message; console.error('[BULUT] Yedek hatası:', e.message); return false; }
  finally { bulut.yazim = false; }
}
setInterval(() => { if (bulut.hazir) bulutYaz(false); }, BULUT_ARALIK);

function yukle() {
  if (!DB_DOSYA) { console.warn('[DB] Yazılabilir klasör yok: yerel disk yedeği kapalı.'); return; }
  try {
    const j = JSON.parse(fs.readFileSync(DB_DOSYA, 'utf8'));
    for (const u of j.users || []) { users.set(u.key, u); nickIndex.set(u.ad.toLowerCase(), u.key); }
    for (const [t, v] of j.tokens || []) tokens.set(t, v);
    for (const k of j.klanlar || []) klanlar.set(k.id, k);
    console.log('[DB] Yerel yedek yüklendi:', users.size, 'hesap,', klanlar.size, 'klan  (' + DB_DOSYA + ')');
  } catch (e) { if (e.code !== 'ENOENT') console.error('[DB] Okuma hatası:', e.message); else console.log('[DB] Yerel yedek yok.'); }
}
function diskeYaz() {
  if (!DB_DOSYA) { kirli = false; return; }
  const tmp = DB_DOSYA + '.tmp';
  try {
    fs.writeFileSync(tmp, dbHam());
    fs.renameSync(tmp, DB_DOSYA);   // yarım yazılmış dosya olmasın
    kirli = false;
  } catch (e) { console.error('[DB] Yazma hatası:', e.message); }
}
function degisti() {
  kirli = true; siraCache.t = 0; klanCache.t = 0;
  if (yazimTimer) return;
  yazimTimer = setTimeout(() => { yazimTimer = null; if (kirli) diskeYaz(); }, 2000);
}
let kapaniyor = false;
async function kapat() {
  if (kapaniyor) return; kapaniyor = true;
  try { diskeYaz(); await Promise.race([bulutYaz(true), new Promise(r => setTimeout(r, 8000))]); } finally { process.exit(0); }
}
['SIGTERM', 'SIGINT'].forEach(s => process.on(s, kapat));
setInterval(() => { if (kirli) diskeYaz(); }, 30000);

/* ---------------- Yardımcılar ---------------- */
const simdi = () => Date.now();
function sifreHash(sifre, tuz) {
  tuz = tuz || crypto.randomBytes(16).toString('hex');
  return tuz + ':' + crypto.scryptSync(sifre, tuz, 32).toString('hex');
}
function sifreDogru(sifre, kayit) {
  const [tuz, h] = String(kayit).split(':');
  const a = Buffer.from(h, 'hex'), b = crypto.scryptSync(sifre, tuz, 32);
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
const adGecerli = s => typeof s === 'string' && /^[A-Za-z0-9._-]{3,16}$/.test(s);
const nickRenkGecerli = s => s === '' || s === 'rainbow' || /^#[0-9a-fA-F]{6}$/.test(s);
const kostumGecerli = s => (typeof s === 'string' && /^[a-z0-9_]{1,24}$/.test(s)) ? s : '';
function gunAnahtari() { return new Date(Date.now() + 3 * 3600e3).toISOString().slice(0, 10); }   // Türkiye saati (UTC+3)
const cevrimiciMi = u => (u.gor || 0) > simdi() - CEVRIMICI_MS || baglilar.has(u.key);

/* ---------------- Görevler (her gün yenilenir) ---------------- */
const GOREV_TANIM = [
  { id: 'mac3',   ad: '3 maç oyna',        hedef: 3, ikon: '⚽', odul: { altin: 60 },  alan: 'mac' },
  { id: 'galib1', ad: '1 maç kazan',       hedef: 1, ikon: '🏆', odul: { altin: 80 },  alan: 'gal' },
  { id: 'gol5',   ad: '5 gol at',          hedef: 5, ikon: '🥅', odul: { altin: 50, elmas: 2 }, alan: 'gol' },
  { id: 'galib3', ad: '3 maç kazan',       hedef: 3, ikon: '🔥', odul: { elmas: 5 },   alan: 'gal' },
  { id: 'mac8',   ad: '8 maç oyna',        hedef: 8, ikon: '💪', odul: { altin: 150, elmas: 3 }, alan: 'mac' }
];
function gorevYenile(u) {
  const g = gunAnahtari();
  if (!u.gorev || u.gorev.gun !== g) u.gorev = { gun: g, ilerleme: {}, alindi: {} };
}
function gorevIlerlet(u, alan, miktar) {
  gorevYenile(u);
  for (const t of GOREV_TANIM) if (t.alan === alan) u.gorev.ilerleme[t.id] = Math.min(t.hedef, (u.gorev.ilerleme[t.id] || 0) + miktar);
}
function gorevListesi(u) {
  gorevYenile(u);
  return GOREV_TANIM.map(t => ({ id: t.id, ad: t.ad, ikon: t.ikon, alan: t.alan, hedef: t.hedef, odul: t.odul,
    ilerleme: u.gorev.ilerleme[t.id] || 0, alindi: !!u.gorev.alindi[t.id] }));
}

/* ---------------- Klanlar ---------------- */
const klanAdGecerli = s => typeof s === 'string' && /^[A-Za-z0-9ÇçĞğİıÖöŞşÜü._ -]{3,20}$/.test(s) && s === s.trim();
const klanEtiketGecerli = s => typeof s === 'string' && /^[A-Za-z0-9]{2,4}$/.test(s);
// klan sıralaması: üyelerin kupa toplamı (banlılar sayılmaz)
function klanSiralama() {
  const n = simdi();
  if (n - klanCache.t < 2000) return klanCache.liste;
  const m = new Map();
  for (const u of users.values()) {
    if (u.ban || !u.klan || !klanlar.has(u.klan)) continue;
    const x = m.get(u.klan) || { k: klanlar.get(u.klan), puan: 0, say: 0 };
    x.puan += u.kupa; x.say++; m.set(u.klan, x);
  }
  klanCache.liste = [...m.values()].sort((a, b) => b.puan - a.puan || b.say - a.say || a.k.olusturma - b.k.olusturma);
  klanCache.t = n;
  return klanCache.liste;
}
function klanDetay(u) {
  const k = u.klan && klanlar.get(u.klan);
  if (!k) { if (u.klan) { u.klan = null; degisti(); } return null; }
  const uy = [...users.values()].filter(x => x.klan === k.id && !x.ban).sort((a, b) => b.kupa - a.kupa);
  const sira = klanSiralama().findIndex(x => x.k.id === k.id) + 1;
  return { id: k.id, ad: k.ad, et: k.et, puan: uy.reduce((s, x) => s + x.kupa, 0), sira, benLider: k.lider === u.key,
    uyeler: uy.map(x => ({ ad: x.ad, nr: x.nr || (x.admin ? 'rainbow' : ''), adm: !!x.admin, kupa: x.kupa, lider: x.key === k.lider, cevrimici: cevrimiciMi(x) })) };
}
function klanCikar(u) {
  const id = u.klan; u.klan = null;
  const k = klanlar.get(id); if (!k) return;
  const kalan = [...users.values()].filter(x => x.klan === id);
  if (!kalan.length) { klanlar.delete(id); return; }
  if (k.lider === u.key) { kalan.sort((a, b) => b.kupa - a.kupa); k.lider = kalan[0].key; }   // lider ayrılırsa en çok kupalı üye lider olur
}
function msjCoz(m) {
  const u = users.get(m.k);
  return { i: m.i, t: m.t, m: m.m, ad: u ? u.ad : m.a, nr: u ? (u.nr || (u.admin ? 'rainbow' : '')) : '', adm: !!(u && u.admin) };   // renk her seferinde güncel okunur: admin rengi değiştirince sohbette de değişir
}

/* ---------------- Hesap işlemleri ---------------- */
function profil(u) {
  return { ad: u.ad, nr: u.nr || '', kupa: u.kupa, mac: u.mac, gal: u.gal, mag: u.mag, gol: u.gol, nd: !!u.nd, adm: !!u.admin,
           altin: u.altin, elmas: u.elmas, envanter: u.envanter || null, gorevler: gorevListesi(u) };
}
function kullaniciOlustur(ad, sifre) {
  const u = { key: ad.toLowerCase(), ad: ad, pass: sifreHash(sifre), olusturma: simdi(), sonGiris: simdi(),
    altin: BASLANGIC.altin, elmas: BASLANGIC.elmas, envanter: null, nr: '',
    kupa: 0, mac: 0, gal: 0, mag: 0, gol: 0, nd: false, ban: null, gorev: null, klan: null, admin: false, bekle: [] };
  users.set(u.key, u); nickIndex.set(u.ad.toLowerCase(), u.key);
  degisti();
  return u;
}
function tokenVer(key) {
  const t = crypto.randomBytes(24).toString('hex');
  tokens.set(t, { key, son: simdi() });
  degisti();
  return t;
}
function tokenKullanici(t) {
  const k = tokens.get(t);
  if (!k) return null;
  const u = users.get(k.key);
  if (!u) { tokens.delete(t); return null; }
  k.son = simdi(); u.gor = simdi();      // son görülme: admin panelindeki "çevrimiçi" sayısı bundan hesaplanır
  return u;
}
function hesapSil(key) {
  const u = users.get(key);
  if (!u) return false;
  if (u.klan) klanCikar(u);
  users.delete(key); nickIndex.delete(u.ad.toLowerCase());
  for (const [t, v] of tokens) if (v.key === key) tokens.delete(t);
  oyuncuAt(key, 'silindi');
  degisti();
  return true;
}
// Giriş adı = nick: hesabı yeni anahtara taşı (ban/silme/giriş hep aynı adla çalışsın). Oyuncu ve admin değişimi ortak kullanır.
function nickTasi(u, ad) {
  const eskiKey = u.key, yeniKey = ad.toLowerCase();
  users.delete(eskiKey); nickIndex.delete(u.ad.toLowerCase()); nickIndex.delete(eskiKey);
  u.ad = ad; u.key = yeniKey;
  users.set(yeniKey, u); nickIndex.set(yeniKey, yeniKey);
  for (const v of tokens.values()) if (v.key === eskiKey) v.key = yeniKey;
  const ws = baglilar.get(eskiKey); if (ws) { baglilar.delete(eskiKey); ws.key = yeniKey; baglilar.set(yeniKey, ws); }
  for (const m of maclar.values()) { if (m.a === eskiKey) m.a = yeniKey; if (m.b === eskiKey) m.b = yeniKey; if (m.rapor.delete(eskiKey)) m.rapor.add(yeniKey); }
  for (const k of klanlar.values()) { if (k.lider === eskiKey) k.lider = yeniKey; for (const m of k.msj) if (m.k === eskiKey) { m.k = yeniKey; m.a = ad; } }
  degisti();
}

/* ---------------- Brute-force koruması ---------------- */
const denemeler = new Map();
function denemeKontrol(ip) {
  const d = denemeler.get(ip), n = simdi();
  if (d && d.kilit > n) return false;
  return true;
}
function denemeKaydet(ip, basari) {
  const n = simdi();
  if (basari) { denemeler.delete(ip); return; }
  const d = denemeler.get(ip) || { say: 0, kilit: 0 };
  d.say++; if (d.say >= 8) { d.kilit = n + 60000; d.say = 0; }
  denemeler.set(ip, d);
}
setInterval(() => { const n = simdi(); for (const [k, v] of denemeler) if (v.kilit < n && !v.say) denemeler.delete(k); }, 300000);
const adminDenemeler = new Map();   // admin anahtarı tahmin korumasi
function adminKilitli(ip) { const d = adminDenemeler.get(ip); return !!(d && d.kilit > simdi()); }
function adminBasarisiz(ip) {
  const d = adminDenemeler.get(ip) || { say: 0, kilit: 0 };
  d.say++; if (d.say >= 10) { d.kilit = simdi() + 300000; d.say = 0; }
  adminDenemeler.set(ip, d);
}

/* ---------------- Sıralama (RAM, 2 sn önbellek) ---------------- */
function siralama() {
  const n = simdi();
  if (n - siraCache.t < 2000) return siraCache.liste;
  siraCache.liste = [...users.values()].filter(u => !u.ban).sort((a, b) => b.kupa - a.kupa || a.olusturma - b.olusturma);
  siraCache.t = n;
  return siraCache.liste;
}

/* ---------------- Eşleşme ---------------- */
const baglilar = new Map();   // kullanıcı key -> ws (sadece maç arayan / maçtaki oyuncular)
let bekleyen = null;          // { ws, key, ad, nr, iz, sv, ge, ko }
const maclar = new Map();     // matchId -> { a, b, t, rapor: Set }
let macSayac = 0;

function gonder(ws, o) { if (ws && ws.readyState === 1) { try { ws.send(JSON.stringify(o)); } catch (_) {} } }
function oyuncuAt(key, neden) {
  const ws = baglilar.get(key);
  if (ws) { gonder(ws, { t: 'kick', neden }); try { ws.close(); } catch (_) {} }
}
function sidIdsiz(ws) { if (bekleyen && bekleyen.ws === ws) bekleyen = null; }
function esle(a, b) {
  const aHost = Math.random() < 0.5, aMavi = Math.random() < 0.5;
  const id = String(++macSayac) + '-' + crypto.randomBytes(4).toString('hex');
  maclar.set(id, { a: a.key, b: b.key, t: simdi(), rapor: new Set() });
  a.ws.rakip = b.ws; b.ws.rakip = a.ws; a.ws.macId = b.ws.macId = id;
  const paket = (x, y, host, mavi) => ({ t: 'm', id, host, renk: mavi ? 'mavi' : 'kirmizi',
    rk: { ad: y.ad, nr: y.nr, iz: y.iz, sv: y.sv, ge: y.ge, ko: y.ko } });
  gonder(a.ws, paket(a, b, aHost, aMavi));
  gonder(b.ws, paket(b, a, !aHost, !aMavi));
}
setInterval(() => { const n = simdi(); for (const [id, m] of maclar) if (n - m.t > 3600e3) maclar.delete(id); }, 600000);

/* ---------------- HTTP / REST ---------------- */
const CORS = { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'content-type,x-admin-key', 'Access-Control-Allow-Methods': 'GET,POST,OPTIONS' };
function yanit(res, kod, obj) { res.writeHead(kod, Object.assign({ 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }, CORS)); res.end(JSON.stringify(obj)); }
function govdeOku(req) {
  return new Promise(ok => {
    let s = '';
    req.on('data', c => { s += c; if (s.length > 20000) req.destroy(); });
    req.on('end', () => { try { ok(JSON.parse(s || '{}')); } catch (_) { ok({}); } });
    req.on('error', () => ok({}));
  });
}
const ipAl = req => String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
function adminMi(req) {
  const ip = ipAl(req);
  if (adminKilitli(ip)) return false;
  const k = String(req.headers['x-admin-key'] || '');
  const ok = !!ADMIN_KEY && k.length === ADMIN_KEY.length && crypto.timingSafeEqual(Buffer.from(k), Buffer.from(ADMIN_KEY));
  if (!ok && k) adminBasarisiz(ip);
  return ok;
}
function envGecerli(e) {
  if (!e || typeof e !== 'object') return null;
  try { const s = JSON.stringify(e); if (s.length > 12000) return null; return JSON.parse(s); } catch (_) { return null; }
}
// oturum doğrula: geçersizse yanıtı kendisi yazar, null döner
function kul(res, b) {
  const u = tokenKullanici(b.token);
  if (!u || u.ban) { yanit(res, 401, { hata: 'oturum' }); return null; }
  return u;
}

/* ---------------- TURN (ping / bağlantı sorununun asıl çözümü) ----------------
   1) Cloudflare Realtime TURN (ücretsiz, dünya çapında anycast): CF_TURN_KEY_ID + CF_TURN_TOKEN
   2) Kendi TURN sunucun: TURN_URLS / TURN_USER / TURN_PASS
   Kısa ömürlü kimlik bilgileri sunucuda üretilir, oyuncuya yalnızca geçici olanı gider. */
const CF_ID = process.env.CF_TURN_KEY_ID || '', CF_TOKEN = process.env.CF_TURN_TOKEN || '';
const MT_APP = String(process.env.METERED_APP || '').trim().replace(/^https?:\/\//, '').replace(/\.metered\.live.*$/, ''), MT_KEY = process.env.METERED_KEY || '';   // Metered Open Relay (kredi kartsız, 20 GB/ay)
let turnOnbellek = { t: 0, ice: null, hata: '' };
const turnVarMi = () => !!((CF_ID && CF_TOKEN) || (MT_APP && MT_KEY) || String(process.env.TURN_URLS || '').trim());
async function turnSunuculari() {
  if (CF_ID && CF_TOKEN && typeof fetch === 'function') {
    if (turnOnbellek.ice && simdi() - turnOnbellek.t < 6 * 3600e3) return turnOnbellek.ice;   // 24 saat geçerli, 6 saatte bir yenilenir
    try {
      const r = await hfZamanli('https://rtc.live.cloudflare.com/v1/turn/keys/' + encodeURIComponent(CF_ID) + '/credentials/generate-ice-servers',
        { method: 'POST', headers: { Authorization: 'Bearer ' + CF_TOKEN, 'content-type': 'application/json' }, body: JSON.stringify({ ttl: 86400 }) }, 8000);
      if (!r.ok) throw new Error('cloudflare ' + r.status + ' ' + (await r.text()).slice(0, 100));
      const j = await r.json();
      let l = j.iceServers; l = Array.isArray(l) ? l : (l ? [l] : []);
      l = l.map(s => Object.assign({}, s, { urls: [].concat(s.urls || []).filter(u => !/:53(\?|$)/.test(u)) })).filter(s => s.urls.length);   // :53 tarayıcılarda engelli
      if (!l.length) throw new Error('bos yanit');
      turnOnbellek = { t: simdi(), ice: l, hata: '' };
      return l;
    } catch (e) { turnOnbellek.hata = e.message; console.error('[TURN]', e.message); if (turnOnbellek.ice) return turnOnbellek.ice; }
  }
  if (MT_APP && MT_KEY && typeof fetch === 'function') {
    if (turnOnbellek.ice && simdi() - turnOnbellek.t < 6 * 3600e3) return turnOnbellek.ice;
    try {
      const r = await hfZamanli('https://' + encodeURIComponent(MT_APP) + '.metered.live/api/v1/turn/credentials?apiKey=' + encodeURIComponent(MT_KEY), {}, 8000);
      if (!r.ok) throw new Error('metered ' + r.status);
      const l = await r.json();
      if (!Array.isArray(l) || !l.length) throw new Error('bos yanit');
      turnOnbellek = { t: simdi(), ice: l, hata: '' };
      return l;
    } catch (e) { turnOnbellek.hata = e.message; console.error('[TURN]', e.message); if (turnOnbellek.ice) return turnOnbellek.ice; }
  }
  const urls = String(process.env.TURN_URLS || '').split(',').map(s => s.trim()).filter(Boolean);
  if (!urls.length) return null;
  return [{ urls: ['stun:stun.l.google.com:19302', 'stun:stun1.l.google.com:19302'] },
          { urls, username: process.env.TURN_USER || '', credential: process.env.TURN_PASS || '' }];
}

const ROUTES = {
  async 'POST /api/auth'(req, res, b) {
    const ip = ipAl(req);
    if (!denemeKontrol(ip)) return yanit(res, 429, { hata: 'cok_deneme' });
    const ad = String(b.ad || '').trim(), sifre = String(b.sifre || '');
    if (!adGecerli(ad)) return yanit(res, 400, { hata: 'ad_gecersiz' });
    if (sifre.length < 6 || sifre.length > 64) return yanit(res, 400, { hata: 'sifre_kisa' });
    let u = users.get(ad.toLowerCase());
    if (!u) {
      if (nickIndex.has(ad.toLowerCase())) return yanit(res, 409, { hata: 'ad_alinmis' });
      u = kullaniciOlustur(ad, sifre);
    } else if (!sifreDogru(sifre, u.pass)) { denemeKaydet(ip, false); return yanit(res, 401, { hata: 'sifre_yanlis' }); }
    denemeKaydet(ip, true);
    if (u.ban) return yanit(res, 403, { hata: 'banli', sebep: u.ban.sebep || '' });
    u.sonGiris = simdi(); u.gor = simdi();
    yanit(res, 200, { token: tokenVer(u.key), profil: profil(u) });
  },
  async 'POST /api/me'(req, res, b) {
    const u = tokenKullanici(b.token);
    if (!u) return yanit(res, 401, { hata: 'oturum' });
    if (u.ban) return yanit(res, 403, { hata: 'banli', sebep: u.ban.sebep || '' });
    yanit(res, 200, { profil: profil(u) });
  },
  async 'POST /api/ice'(req, res, b) {   // WebRTC ICE/TURN sunucuları
    const u = tokenKullanici(b.token);
    if (!u) return yanit(res, 401, { hata: 'oturum' });
    yanit(res, 200, { ice: await turnSunuculari() });
  },
  async 'POST /api/logout'(req, res, b) { if (tokens.delete(b.token)) degisti(); yanit(res, 200, { ok: 1 }); },
  async 'POST /api/hesap-sil'(req, res, b) {
    const u = tokenKullanici(b.token);
    if (!u) return yanit(res, 401, { hata: 'oturum' });
    hesapSil(u.key);
    yanit(res, 200, { ok: 1 });
  },
  /* altın / elmas / envanter eşitleme + ADMIN DEĞİŞİKLİĞİ TESLİMİ.
     Oyun bunu ~3 sn'de bir çağırır. Admin kupa/altın/elmas değiştirdiyse (u.bekle dolu) istemcinin eski altın/elmas
     değeri KABUL EDİLMEZ; yerine yeni profil + değişiklik bildirimi gider, böylece admin değişikliği ezilmez ve oyuncu görür. */
  async 'POST /api/kaydet'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    const bekle = Array.isArray(u.bekle) && u.bekle.length > 0;
    let ch = false;
    if (!bekle) {
      const a = Math.floor(+b.altin), e = Math.floor(+b.elmas);
      if (Number.isFinite(a) && Number.isFinite(e) && a >= 0 && e >= 0 && a < 1e9 && e < 1e9 && (u.altin !== a || u.elmas !== e)) { u.altin = a; u.elmas = e; ch = true; }
    }
    const env = envGecerli(b.envanter); if (env) { u.envanter = env; ch = true; }
    const o = { ok: 1 };
    if (bekle) { o.bildirim = u.bekle; o.profil = profil(u); u.bekle = []; ch = true; }
    if (ch) degisti();
    yanit(res, 200, o);
  },
  async 'POST /api/mac'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    const n = simdi();
    if (b.bot) {
      if (n - (u.sonBot || 0) < 30000) return yanit(res, 429, { hata: 'cok_sik', profil: profil(u) });
      u.sonBot = n;
    } else {
      const m = maclar.get(String(b.mid));
      if (!m || (m.a !== u.key && m.b !== u.key) || m.rapor.has(u.key)) return yanit(res, 400, { hata: 'mac_gecersiz', profil: profil(u) });
      if (n - m.t < MIN_MAC_MS) return yanit(res, 400, { hata: 'cok_kisa', profil: profil(u) });
      m.rapor.add(u.key);
    }
    const kazandi = !!b.galibiyet, gol = Math.max(0, Math.min(3, b.gol | 0));
    u.mac++; if (kazandi) { u.gal++; u.kupa += KUPA_KAZAN; u.altin += KAZAN_ALTIN; } else { u.mag++; u.kupa -= Math.min(KUPA_KAYIP, u.kupa); }
    u.gol += gol;
    gorevIlerlet(u, 'mac', 1); if (kazandi) gorevIlerlet(u, 'gal', 1); gorevIlerlet(u, 'gol', gol);
    degisti();
    yanit(res, 200, { profil: profil(u) });
  },
  async 'POST /api/gorevler'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    yanit(res, 200, { gorevler: gorevListesi(u) });
  },
  async 'POST /api/gorev-al'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    gorevYenile(u);
    const t = GOREV_TANIM.find(x => x.id === b.id);
    if (!t) return yanit(res, 400, { hata: 'gorev_yok' });
    if (u.gorev.alindi[t.id]) return yanit(res, 400, { hata: 'alindi' });
    if ((u.gorev.ilerleme[t.id] || 0) < t.hedef) return yanit(res, 400, { hata: 'tamam_degil' });
    u.gorev.alindi[t.id] = 1;
    u.altin += t.odul.altin || 0; u.elmas += t.odul.elmas || 0;
    degisti();
    yanit(res, 200, { odul: t.odul, profil: profil(u) });
  },
  async 'POST /api/nick'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    const ad = String(b.ad || '').trim();
    if (!adGecerli(ad)) return yanit(res, 400, { hata: 'karakter' });
    if (ad === u.ad) return yanit(res, 400, { hata: 'ayni' });
    const sahip = nickIndex.get(ad.toLowerCase());
    if (sahip && sahip !== u.key) return yanit(res, 409, { hata: 'ad_alinmis' });
    if (u.nd && u.altin < NICK_UCRET) return yanit(res, 400, { hata: 'altin' });
    if (u.nd) u.altin -= NICK_UCRET;
    nickTasi(u, ad); u.nd = true; degisti();
    yanit(res, 200, { profil: profil(u) });
  },
  async 'POST /api/siralama'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    const liste = siralama();
    const ilk = liste.slice(0, 50).map((x, i) => ({ sira: i + 1, ad: x.ad, nr: x.nr || '', kupa: x.kupa, ben: x.key === u.key }));
    let benim = null;
    if (!ilk.some(x => x.ben)) benim = liste.indexOf(u) + 1;
    yanit(res, 200, { liste: ilk, benim });
  },

  /* ---------- KLAN ---------- */
  async 'POST /api/klan-ben'(req, res, b) {          // benim klanım (yoksa null)
    const u = kul(res, b); if (!u) return;
    yanit(res, 200, { klan: klanDetay(u) });
  },
  async 'POST /api/klan-liste'(req, res, b) {        // klan sıralaması (kupa toplamına göre) + arama
    const u = kul(res, b); if (!u) return;
    const q = String(b.q || '').trim().toLowerCase().slice(0, 20);
    const tum = klanSiralama().map((x, i) => ({ sira: i + 1, id: x.k.id, ad: x.k.ad, et: x.k.et, puan: x.puan, say: x.say, dolu: x.say >= KLAN_MAX_UYE }));
    const liste = (q ? tum.filter(x => x.ad.toLowerCase().includes(q) || x.et.toLowerCase() === q) : tum).slice(0, 50);
    yanit(res, 200, { liste, benim: u.klan || null, max: KLAN_MAX_UYE });
  },
  async 'POST /api/klan-olustur'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    if (u.klan && klanlar.has(u.klan)) return yanit(res, 400, { hata: 'klanda' });
    const ad = String(b.ad || '').trim(), et = String(b.et || '').trim().toUpperCase();
    if (!klanAdGecerli(ad)) return yanit(res, 400, { hata: 'klan_ad' });
    if (!klanEtiketGecerli(et)) return yanit(res, 400, { hata: 'klan_etiket' });
    for (const k of klanlar.values()) if (k.ad.toLowerCase() === ad.toLowerCase()) return yanit(res, 409, { hata: 'klan_alinmis' });
    const id = 'k' + crypto.randomBytes(5).toString('hex');
    klanlar.set(id, { id, ad, et, lider: u.key, olusturma: simdi(), sayac: 0, msj: [] });
    u.klan = id; degisti();
    yanit(res, 200, { klan: klanDetay(u) });
  },
  async 'POST /api/klan-katil'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    if (u.klan && klanlar.has(u.klan)) return yanit(res, 400, { hata: 'klanda' });
    const k = klanlar.get(String(b.id));
    if (!k) return yanit(res, 404, { hata: 'klan_yok' });
    let say = 0; for (const x of users.values()) if (x.klan === k.id) say++;
    if (say >= KLAN_MAX_UYE) return yanit(res, 400, { hata: 'klan_dolu' });
    u.klan = k.id; degisti();
    yanit(res, 200, { klan: klanDetay(u) });
  },
  async 'POST /api/klan-ayril'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    if (u.klan) klanCikar(u);
    degisti();
    yanit(res, 200, { ok: 1 });
  },
  async 'POST /api/klan-at'(req, res, b) {           // sadece klan lideri
    const u = kul(res, b); if (!u) return;
    const k = u.klan && klanlar.get(u.klan);
    if (!k || k.lider !== u.key) return yanit(res, 403, { hata: 'yetki' });
    const h = users.get(String(b.ad || '').toLowerCase());
    if (!h || h.klan !== k.id || h.key === u.key) return yanit(res, 400, { hata: 'uye_yok' });
    h.klan = null; degisti();
    yanit(res, 200, { klan: klanDetay(u) });
  },
  async 'POST /api/klan-sohbet'(req, res, b) {       // son = en son gördüğün mesaj no; yalnızca yenileri döner
    const u = kul(res, b); if (!u) return;
    const k = u.klan && klanlar.get(u.klan);
    if (!k) return yanit(res, 400, { hata: 'klanda_degil' });
    const son = +b.son || 0;
    yanit(res, 200, { msj: k.msj.filter(m => m.i > son).slice(-60).map(msjCoz) });
  },
  async 'POST /api/klan-yaz'(req, res, b) {
    const u = kul(res, b); if (!u) return;
    const k = u.klan && klanlar.get(u.klan);
    if (!k) return yanit(res, 400, { hata: 'klanda_degil' });
    const n = simdi();
    if (n - (u.sonMsj || 0) < 800) return yanit(res, 429, { hata: 'cok_sik' });
    const m = String(b.m || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, 200);
    if (!m) return yanit(res, 400, { hata: 'bos' });
    u.sonMsj = n;
    k.msj.push({ i: ++k.sayac, k: u.key, a: u.ad, m, t: n });
    if (k.msj.length > 100) k.msj.splice(0, k.msj.length - 100);
    degisti();
    const son = +b.son || 0;
    yanit(res, 200, { msj: k.msj.filter(x => x.i > son).slice(-60).map(msjCoz) });
  },

  /* ---------- ADMIN ---------- */
  async 'GET /admin/stats'(req, res) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    let banli = 0, bugun = 0, online = 0; const g = simdi() - 86400e3;
    for (const u of users.values()) { if (u.ban) banli++; if (u.sonGiris > g) bugun++; if (cevrimiciMi(u)) online++; }
    const aktifMac = [...baglilar.values()].filter(w => w.rakip).length / 2;
    yanit(res, 200, { toplam: users.size, cevrimici: online, banli, son24saat: bugun, bekleyen: bekleyen ? 1 : 0,
      aramada: baglilar.size - aktifMac * 2, aktifMac, klan: klanlar.size, disk: !!DB_DOSYA, bellekMB: Math.round(process.memoryUsage().rss / 1048576),
      bulut: !BULUT ? 'YOK' : bulut.hazir ? 'AÇIK' : 'BAĞLANAMADI', bulutSon: bulut.sonYedek, bulutHata: bulut.sonHata,
      turn: turnVarMi(), turnTip: (CF_ID && CF_TOKEN) ? 'Cloudflare' : (MT_APP && MT_KEY) ? 'Metered' : turnVarMi() ? 'Özel' : '', turnHata: turnOnbellek.hata });
  },
  async 'GET /admin/users'(req, res) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const q = (new URL(req.url, 'http://x').searchParams.get('q') || '').toLowerCase();
    const liste = [...users.values()].filter(u => !q || u.key.includes(q) || u.ad.toLowerCase().includes(q))
      .sort((a, b) => b.kupa - a.kupa).slice(0, 200)
      .map(u => { const k = u.klan && klanlar.get(u.klan);
        return { ad: u.ad, nr: u.nr || '', adm: !!u.admin, klan: k ? k.et : '', kupa: u.kupa, mac: u.mac, altin: u.altin, elmas: u.elmas, olusturma: u.olusturma, sonGiris: u.sonGiris, ban: u.ban, cevrimici: cevrimiciMi(u) }; });
    yanit(res, 200, { liste });
  },
  async 'POST /admin/ban'(req, res, b) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    u.ban = { sebep: String(b.sebep || '').slice(0, 120), t: simdi() };
    for (const [t, v] of tokens) if (v.key === u.key) tokens.delete(t);
    oyuncuAt(u.key, 'banli'); degisti();
    yanit(res, 200, { ok: 1 });
  },
  async 'POST /admin/unban'(req, res, b) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    u.ban = null; degisti();
    yanit(res, 200, { ok: 1 });
  },
  async 'POST /admin/sil'(req, res, b) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const ok = hesapSil(String(b.ad || '').toLowerCase());
    yanit(res, ok ? 200 : 404, ok ? { ok: 1 } : { hata: 'yok' });
  },
  async 'POST /admin/duzenle'(req, res, b) {   // kupa / altın / elmas düzelt -> oyuncuya ANINDA yansır + "admin şunu değiştirdi" bildirimi gider
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    const fark = [];
    for (const k of ['kupa', 'altin', 'elmas']) {
      if (b[k] === undefined || b[k] === '' || b[k] === null) continue;
      if (!(Number.isFinite(+b[k]) && +b[k] >= 0 && +b[k] < 1e9)) continue;
      const yeni = Math.floor(+b[k]);
      if (u[k] !== yeni) { fark.push({ a: k, e: u[k], y: yeni }); u[k] = yeni; }
    }
    if (fark.length) u.bekle = (Array.isArray(u.bekle) ? u.bekle : []).concat([{ t: simdi(), d: fark }]).slice(-10);
    degisti();
    yanit(res, 200, { ok: 1, degisen: fark.length });
  },
  async 'POST /admin/renk'(req, res, b) {      // nick rengi: '#rrggbb' | 'rainbow' | '' (kaldır)
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    const r = String(b.renk || '');
    if (!nickRenkGecerli(r)) return yanit(res, 400, { hata: 'renk' });
    u.nr = r; degisti();
    yanit(res, 200, { ok: 1 });
  },
  async 'POST /admin/yetkili'(req, res, b) {   // oyuncuyu "Admin" rozetli yap / kaldır (klan sohbetinde 👑 + renkli isim)
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    u.admin = !!b.admin; degisti();
    yanit(res, 200, { ok: 1, admin: u.admin });
  },
  async 'GET /admin/klanlar'(req, res) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    yanit(res, 200, { liste: klanSiralama().map((x, i) => ({ sira: i + 1, id: x.k.id, ad: x.k.ad, et: x.k.et, puan: x.puan, say: x.say, lider: (users.get(x.k.lider) || {}).ad || '-' })) });
  },
  async 'POST /admin/klan-sil'(req, res, b) {
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const k = klanlar.get(String(b.id || ''));
    if (!k) return yanit(res, 404, { hata: 'yok' });
    for (const u of users.values()) if (u.klan === k.id) u.klan = null;
    klanlar.delete(k.id); degisti();
    yanit(res, 200, { ok: 1 });
  },
  async 'POST /admin/nick'(req, res, b) {      // admin: oyuncunun nickini (ve giriş adını) değiştir, ücretsiz
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    const yeni = String(b.yeni || '').trim();
    if (!adGecerli(yeni)) return yanit(res, 400, { hata: 'karakter' });
    const sahip = nickIndex.get(yeni.toLowerCase());
    if (sahip && sahip !== u.key) return yanit(res, 409, { hata: 'ad_alinmis' });
    nickTasi(u, yeni);
    yanit(res, 200, { ok: 1, ad: u.ad });
  },
  async 'POST /admin/sifre'(req, res, b) {     // şifreler tek yönlü hash'lidir (görülemez); admin yeni şifre belirleyebilir
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    const u = users.get(String(b.ad || '').toLowerCase());
    if (!u) return yanit(res, 404, { hata: 'yok' });
    let s = String(b.sifre || '');
    if (!s) s = crypto.randomBytes(6).toString('base64').replace(/[^A-Za-z0-9]/g, 'x').slice(0, 8);
    if (s.length < 6 || s.length > 64) return yanit(res, 400, { hata: 'sifre_kisa' });
    u.pass = sifreHash(s);
    for (const [t, v] of tokens) if (v.key === u.key) tokens.delete(t);   // eski oturumlar düşer
    oyuncuAt(u.key, 'oturum'); degisti();
    yanit(res, 200, { ok: 1, sifre: s });
  },
  async 'POST /admin/yedekle'(req, res) {      // bulut yedeğini hemen al
    if (!adminMi(req)) return yanit(res, 401, { hata: 'yetkisiz' });
    diskeYaz();
    const ok = await bulutYaz(true);
    yanit(res, 200, { ok: ok ? 1 : 0, bulut: !BULUT ? 'YOK' : bulut.hazir ? 'AÇIK' : 'BAĞLANAMADI', hata: bulut.sonHata });
  }
};

const server = http.createServer(async (req, res) => {
  if (req.method === 'OPTIONS') { res.writeHead(204, CORS); return res.end(); }
  const yol = req.url.split('?')[0];
  if (yol === '/health' || yol === '/') { res.writeHead(200, Object.assign({ 'Content-Type': 'text/plain' }, CORS)); return res.end('ok'); }
  if (yol === '/admin' || yol === '/admin/') {
    try { res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' }); return res.end(fs.readFileSync(path.join(__dirname, 'admin.html'))); }
    catch (_) { res.writeHead(500); return res.end('admin.html yok'); }
  }
  const h = ROUTES[req.method + ' ' + yol];
  if (!h) return yanit(res, 404, { hata: 'yok' });
  try { const body = req.method === 'POST' ? await govdeOku(req) : {}; await h(req, res, body); }
  catch (e) { console.error(e); yanit(res, 500, { hata: 'sunucu' }); }
});

/* ---------------- WebSocket: eşleşme + sinyal ---------------- */
const wss = new WebSocketServer({ server, maxPayload: 16384 });
wss.on('connection', ws => {
  ws.canli = true; ws.key = null; ws.rakip = null;
  ws.on('pong', () => { ws.canli = true; });
  ws.on('message', raw => {
    ws.canli = true;
    let m; try { m = JSON.parse(raw); } catch (_) { return; }
    if (!m || typeof m !== 'object') return;
    if (m.t === 'p') return;
    if (m.t === 'q') {
      const u = tokenKullanici(m.tok);
      if (!u) return gonder(ws, { t: 'kick', neden: 'oturum' });
      if (u.ban) return gonder(ws, { t: 'kick', neden: 'banli' });
      if (ws.key) return;
      const eski = baglilar.get(u.key);
      if (eski && eski !== ws) { sidIdsiz(eski); try { eski.close(); } catch (_) {} }
      ws.key = u.key; baglilar.set(u.key, ws);
      const o = { ws, key: u.key, ad: u.ad, nr: u.nr || (u.admin ? 'rainbow' : ''), iz: String(m.iz || '').slice(0, 40), sv: String(m.sv || '').slice(0, 40), ge: String(m.ge || '').slice(0, 40), ko: kostumGecerli(m.ko) };
      if (bekleyen && bekleyen.ws.readyState === 1 && bekleyen.key !== o.key) { const b = bekleyen; bekleyen = null; esle(b, o); }
      else bekleyen = o;
      return;
    }
    if (m.t === 'sig') { if (ws.rakip) gonder(ws.rakip, { t: 'sig', d: m.d }); return; }
    if (m.t === 'x') { ayril(ws); return; }
  });
  ws.on('close', () => ayril(ws));
  ws.on('error', () => {});
});
function ayril(ws) {
  sidIdsiz(ws);
  if (ws.key && baglilar.get(ws.key) === ws) baglilar.delete(ws.key);
  const r = ws.rakip; ws.rakip = null;
  if (r && r.rakip === ws) { r.rakip = null; gonder(r, { t: 'l' }); }
}
setInterval(() => {
  for (const ws of wss.clients) { if (!ws.canli) { try { ws.terminate(); } catch (_) {} continue; } ws.canli = false; try { ws.ping(); } catch (_) {} }
}, 30000);

/* ---------------- Başlat ---------------- */
(async () => {
  yukle();                                                  // 1) yerel disk
  if (BULUT) await Promise.race([bulutYukle(), new Promise(r => setTimeout(r, 12000))]);   // 2) bulut yedeği (en fazla 12 sn bekle, arka planda sürer)
  else console.warn('[BULUT] Kapalı: HF_TOKEN (Write) secret\'ı eklenmemiş. Yeni sürümde veri SİLİNİR!');
  server.listen(PORT, () => console.log('NOXBALL sunucu :' + PORT + (ADMIN_KEY ? '' : '  (UYARI: ADMIN_KEY ayarlı değil, admin kapalı)')));
})();