/* Route video ("filmik z trasy"): the camera flies along the line over a satellite or street map,
   a red line grows behind it, a stop sign pops up at every stop and its announcement plays.
   The same 1080x1920 canvas is shown as the preview and recorded to a video file. */
(function () {
  'use strict';
  const W = 1080, H = 1920, FPS = 30;
  const SPEEDS = { slow: 110, normal: 200, fast: 380 };           // metres per second of travel
  const STYLES = {
    sat: {
      version: 8,
      glyphs: 'https://tiles.openfreemap.org/fonts/{fontstack}/{range}.pbf',
      sources: {
        img: { type: 'raster', tileSize: 256, maxzoom: 19,
          tiles: ['https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}'] },
        lbl: { type: 'raster', tileSize: 256, maxzoom: 19,
          tiles: ['https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Boundaries_and_Places/MapServer/tile/{z}/{y}/{x}'] },
        rd: { type: 'raster', tileSize: 256, maxzoom: 19,
          tiles: ['https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Transportation/MapServer/tile/{z}/{y}/{x}'] }
      },
      layers: [{ id: 'img', type: 'raster', source: 'img' },
               { id: 'rd', type: 'raster', source: 'rd', paint: { 'raster-opacity': 0.55 } },
               { id: 'lbl', type: 'raster', source: 'lbl' }]
    },
    map: 'https://tiles.openfreemap.org/styles/liberty'
  };
  const ATTR = { sat: 'Zdjęcia: Esri, Maxar, Earthstar Geographics', map: '© OpenStreetMap · OpenFreeMap' };

  let ui = null, run = null;
  // user's own name font (e.g. Museo Sans): picked from their computer, kept only in this browser
  function idb() { return new Promise((res, rej) => { const r = indexedDB.open('film', 1); r.onupgradeneeded = () => r.result.createObjectStore('kv'); r.onsuccess = () => res(r.result); r.onerror = rej; }); }
  async function kvGet(k) { try { const db = await idb(); return await new Promise(r => { const q = db.transaction('kv').objectStore('kv').get(k); q.onsuccess = () => r(q.result); q.onerror = () => r(null); }); } catch (e) { return null; } }
  async function kvSet(k, v) { try { const db = await idb(); db.transaction('kv', 'readwrite').objectStore('kv').put(v, k); } catch (e) {} }
  async function useNameFont(buf) { const f = new FontFace('Museo', buf); await f.load(); document.fonts.add(f); return true; }
  // destination text for the LED display; the LED font draws these characters as symbols
  function ledText(line, dest) {
    let t = dest;
    if (/Dworzec Główny (Zachód|Wschód)/.test(dest)) t += ',';   // train
    if (/^8/.test(line)) t += "'";                                // cemetery line
    if (/Kraków Airport/.test(dest)) t += '{';                    // plane
    return t;
  }

  // ---------- geometry helpers ----------
  const R = 6371000, rad = Math.PI / 180;
  function hav(a, b) {
    const dla = (b[0] - a[0]) * rad, dlo = (b[1] - a[1]) * rad;
    const h = Math.sin(dla / 2) ** 2 + Math.cos(a[0] * rad) * Math.cos(b[0] * rad) * Math.sin(dlo / 2) ** 2;
    return 2 * R * Math.asin(Math.sqrt(h));
  }
  // ---------- route corrections: segment i (stop i -> stop i+1) replaced by points clicked on the map ----------
  async function loadFixes() {
    let base = {};
    try { base = await (await fetch('geo/fixes.json', { cache: 'no-cache' })).json(); } catch (e) {}
    let mine = {};
    try { mine = JSON.parse(localStorage.getItem('routeFixes') || '{}'); } catch (e) {}
    const out = JSON.parse(JSON.stringify(base));
    for (const k in mine) out[k] = Object.assign(out[k] || {}, mine[k]);
    return out;
  }
  function saveMine(key, segs) {
    let mine = {};
    try { mine = JSON.parse(localStorage.getItem('routeFixes') || '{}'); } catch (e) {}
    if (segs && Object.keys(segs).length) mine[key] = segs; else delete mine[key];
    try { localStorage.setItem('routeFixes', JSON.stringify(mine)); } catch (e) {}
    return mine;
  }
  // segs: { "<i>": [[lat,lon],...] waypoints of segment i, "p<i>": [lat,lon] moved position of stop i }
  function proj(G, q, lo, hi) {             // distance along G of the point nearest to q, limited to [lo,hi]
    let best = 1e18, bd = lo;
    const kx = Math.cos(q[0] * rad);
    for (let i = 1; i < G.pts.length; i++) {
      if (G.cum[i] < lo || G.cum[i - 1] > hi) continue;
      const a = G.pts[i - 1], b = G.pts[i];
      const ax = (a[1] - q[1]) * kx, ay = a[0] - q[0], bx = (b[1] - q[1]) * kx, by = b[0] - q[0];
      const dx = bx - ax, dy = by - ay, L = dx * dx + dy * dy;
      let u = L ? -(ax * dx + ay * dy) / L : 0; u = Math.max(0, Math.min(1, u));
      const ex = ax + dx * u, ey = ay + dy * u, dd = ex * ex + ey * ey;
      const dist = G.cum[i - 1] + (G.cum[i] - G.cum[i - 1]) * u;
      if (dd < best && dist >= lo - 1 && dist <= hi + 1) { best = dd; bd = Math.max(lo, Math.min(hi, dist)); }
    }
    return bd;
  }
  function applyFix(g, segs) {
    if (!segs || !Object.keys(segs).length) return g;
    const G0 = prep(g), pts = [], cuts = [], S = g.s, n = S.length;
    const between = (a, b) => { const o = []; for (let i = 0; i < G0.pts.length; i++) if (G0.cum[i] > a && G0.cum[i] < b) o.push(G0.pts[i]); return o; };
    const D = [], P = [];
    for (let i = 0; i < n; i++) {
      const mv = segs['p' + i];
      if (mv) { D.push(proj(G0, mv, i ? D[i - 1] : 0, i < n - 1 ? S[i + 1][2] : G0.len)); P.push(mv); }
      else { D.push(Math.max(S[i][2], i ? D[i - 1] : 0)); P.push(at(G0, S[i][2]).p); }
    }
    if (!segs.p0) pts.push(at(G0, 0).p);
    for (let i = 0; i < n; i++) {
      pts.push(P[i]); cuts.push(pts.length - 1);
      if (i === n - 1) break;
      const fx = segs[i];
      if (fx && fx.length) fx.forEach(q => pts.push(q));
      else between(D[i], D[i + 1]).forEach(q => pts.push(q));
    }
    if (!segs['p' + (n - 1)]) between(D[n - 1], G0.len + 1).forEach(q => pts.push(q));
    const cum = [0]; for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + hav(pts[i - 1], pts[i]));
    return { p: pts, s: S.map((st, i) => [P[i][0], P[i][1], cum[cuts[i]]]), len: cum[cum.length - 1] };
  }

  function prep(g) {
    const cum = [0];
    for (let i = 1; i < g.p.length; i++) cum.push(cum[i - 1] + hav(g.p[i - 1], g.p[i]));
    return { pts: g.p, cum, len: cum[cum.length - 1], stops: g.s };
  }
  function at(G, d) {                       // [lat,lon] and segment index at distance d
    d = Math.max(0, Math.min(G.len, d));
    let lo = 0, hi = G.cum.length - 1;
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (G.cum[m] <= d) lo = m; else hi = m; }
    const a = G.pts[lo], b = G.pts[hi], s = G.cum[hi] - G.cum[lo] || 1, u = (d - G.cum[lo]) / s;
    return { p: [a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u], i: lo };
  }
  function bearing(a, b) {
    const y = Math.sin((b[1] - a[1]) * rad) * Math.cos(b[0] * rad);
    const x = Math.cos(a[0] * rad) * Math.sin(b[0] * rad) - Math.sin(a[0] * rad) * Math.cos(b[0] * rad) * Math.cos((b[1] - a[1]) * rad);
    return Math.atan2(y, x) / rad;
  }
  function travelled(G, d) {                // coordinates [lon,lat] of the route up to distance d
    const e = at(G, d), out = [];
    for (let i = 0; i <= e.i; i++) out.push([G.pts[i][1], G.pts[i][0]]);
    out.push([e.p[1], e.p[0]]);
    return out;
  }
  const ease = u => u < 0.5 ? 2 * u * u : 1 - (-2 * u + 2) ** 2 / 2;
  const angDiff = (a, b) => ((b - a + 540) % 360) - 180;
  const sleep = ms => new Promise(r => setTimeout(r, ms));

  // ---------- drawing ----------
  function rr(c, x, y, w, h, r) { c.beginPath(); c.roundRect(x, y, w, h, r); }

  // negative line number on the dot matrix: every dot of the block lit except the digits' dots
  // (the LED font has 24 dots per em: pitch = fs/24, dots centred ~0.45 / 0.55 pitch from the cell origin)
  let negCache = null;
  function negNumber(c, num, fs, nx, base, nw, y0, bh) {
    const p = fs / 24, key = num + '|' + fs;
    if (!negCache || negCache.key !== key) {
      const cv = document.createElement('canvas'), w = Math.ceil(nw + 4 * p), h = Math.ceil(fs * 1.3);
      cv.width = w; cv.height = h; const g = cv.getContext('2d');
      g.font = `${fs}px Linia, monospace`; g.textBaseline = 'alphabetic'; g.fillStyle = '#fff';
      const ox = 2 * p, ob = fs * 0.95; g.fillText(num, ox, ob);
      const d = g.getImageData(0, 0, w, h).data, dots = [];
      const top = ob - fs * 0.875;
      for (let r = -2; r < 30; r++) {
        const yy = top + (r + 0.55) * p; if (yy < 0 || yy >= h) continue;
        for (let k = -2; ; k++) {
          const xx = ox + (k + 0.45) * p; if (xx >= w) break; if (xx < 0) continue;
          dots.push([xx - ox, yy - ob, d[(Math.round(yy) * w + Math.round(xx)) * 4 + 3] > 100]);
        }
      }
      negCache = { key, dots };
    }
    const r = p * 0.36;
    c.save(); c.beginPath(); c.rect(nx - 2 * p, y0 + 6, nw + 4 * p, bh - 12); c.clip();
    c.fillStyle = '#2a1a05'; c.beginPath();
    for (const [x, y, on] of negCache.dots) if (on) { c.moveTo(nx + x + r, base + y); c.arc(nx + x, base + y, r, 0, 7); }
    c.fill();
    c.shadowColor = '#ff9a1a'; c.shadowBlur = 10; c.fillStyle = '#ffb02e'; c.beginPath();
    for (const [x, y, on] of negCache.dots) if (!on) { c.moveTo(nx + x + r, base + y); c.arc(nx + x, base + y, r, 0, 7); }
    c.fill(); c.restore();
  }

  // LED destination display in the user's LED font: line number fixed, direction text scrolls
  function drawLED(c, num, text, neg, t) {
    const y0 = 110, bh = 150, fs = 118, base = y0 + bh / 2 + fs * 0.33;
    c.fillStyle = '#050505'; c.fillRect(0, y0, W, bh);
    c.save(); c.beginPath(); c.rect(0, y0, W, bh); c.clip();
    c.font = `${fs}px Linia, monospace`; c.textBaseline = 'alphabetic'; c.textAlign = 'left';
    const nw = c.measureText(num).width, nx = 24;
    if (neg) negNumber(c, num, fs, nx, base, nw, y0, bh);
    else { c.shadowColor = '#ff9a1a'; c.shadowBlur = 12; c.fillStyle = '#ffb02e'; c.fillText(num, nx, base); }
    const x0 = nx + nw + 48, avail = W - x0 - 16, tw = c.measureText(text).width;
    c.beginPath(); c.rect(x0, y0, W - x0, bh); c.clip();
    c.shadowColor = '#ff9a1a'; c.shadowBlur = 12; c.fillStyle = '#ffb02e';
    if (tw <= avail) c.fillText(text, x0 + (avail - tw) / 2, base);
    else {
      const gap = 260, per = tw + gap, off = (t * 150) % per;
      c.fillText(text, x0 - off, base); c.fillText(text, x0 - off + per, base);
    }
    c.restore();
  }

  function pictogram(c, x, y, w, tram) {   // black bus / tram side view, w = width
    const h = w * 0.42; c.fillStyle = '#000';
    if (tram) {
      c.fillRect(x + w * 0.38, y - h * 0.32, w * 0.24, h * 0.06);          // pantograph
      c.beginPath(); c.moveTo(x + w * 0.42, y - h * 0.27); c.lineTo(x + w * 0.5, y - h * 0.05); c.lineTo(x + w * 0.58, y - h * 0.27);
      c.lineWidth = w * 0.025; c.strokeStyle = '#000'; c.stroke();
    }
    rr(c, x, y, w, h, h * 0.18); c.fill();
    c.fillStyle = '#fff';
    const wy = y + h * 0.16, wh = h * 0.36, n = tram ? 5 : 4, ww = (w * 0.82) / n;
    for (let i = 0; i < n; i++) { rr(c, x + w * 0.06 + i * ww, wy, ww * 0.8, wh, 4); c.fill(); }
    c.fillStyle = '#000';
    const wr = h * 0.17, cy = y + h * 1.0;
    const wx = tram ? [0.18, 0.32, 0.68, 0.82] : [0.2, 0.78];
    for (const f of wx) { c.beginPath(); c.arc(x + w * f, cy, wr, 0, 7); c.fill(); c.fillStyle = '#fff';
      c.beginPath(); c.arc(x + w * f, cy, wr * 0.35, 0, 7); c.fill(); c.fillStyle = '#000'; }
  }
  // stop sign: the user's D-15 / D-17 sign image on a white card with the stop name, centred
  const IMG = {};
  const NAMEFONT = 'Museo, "Museo Sans", Arial, Helvetica, sans-serif';
  function loadImg(k, src) { return new Promise(r => { const i = new Image(); i.onload = () => { IMG[k] = i; r(); }; i.onerror = r; i.src = src; }); }
  // stop name: one line at full size, else the best split into two lines, shrinking only if still too wide
  function nameLayout(c, text, maxW) {
    const fit = (fs, lines) => { c.font = `500 ${fs}px ${NAMEFONT}`; return Math.max(...lines.map(l => c.measureText(l).width)) <= maxW; };
    const words = text.split(' ');
    const splits = [];
    for (let i = 1; i < words.length; i++) splits.push([words.slice(0, i).join(' '), words.slice(i).join(' ')]);
    for (let fs = 60; fs >= 30; fs -= 2) {
      if (fit(fs, [text])) return { fs, lines: [text] };
      let best = null, bw = 1e9;
      for (const sp of splits) { c.font = `500 ${fs}px ${NAMEFONT}`; const w = Math.max(...sp.map(l => c.measureText(l).width)); if (w < bw) { bw = w; best = sp; } }
      if (best && bw <= maxW) return { fs, lines: best };
    }
    return { fs: 30, lines: [text] };
  }
  function drawSign(c, name, tram, req, k, zone) {
    if (k <= 0) return;
    const img = IMG[tram ? 'tram' : 'bus'];
    const iw = 560, ih = img ? iw * img.height / img.width : 700;
    const L = nameLayout(c, name + (req ? '\u00a0\u00a0N/Ż' : ''), iw + 30);
    const zfs = 40, zh = zone ? zfs * 1.4 : 0;                      // "(Granica Strefy Biletowej)" under the name
    const cw = iw + 80, ch = ih + 160 + (L.lines.length - 1) * L.fs * 1.15 + zh, x = (W - cw) / 2, y = (H - ch) / 2 - 60;
    c.save();
    c.globalAlpha = Math.min(1, k * 1.4);
    const sc = 0.85 + 0.15 * ease(Math.min(1, k));
    c.translate(W / 2, y + ch / 2); c.scale(sc, sc); c.translate(-W / 2, -(y + ch / 2));
    c.shadowColor = 'rgba(0,0,0,.35)'; c.shadowBlur = 30; c.fillStyle = 'rgba(255,255,255,.95)';
    rr(c, x, y, cw, ch, 34); c.fill(); c.shadowBlur = 0;
    const ix = x + 40, iy = y + 40;
    if (img) c.drawImage(img, ix, iy, iw, ih);
    if (req) {                                              // on-request stop: like the real plate under the sign
      c.fillStyle = '#f7a81b'; c.textAlign = 'center'; c.textBaseline = 'middle';
      c.font = `700 62px ${NAMEFONT}`;
      c.fillText('NA ŻĄDANIE', W / 2, iy + ih * (tram ? 0.865 : 0.84));
    }
    c.fillStyle = '#111'; c.textAlign = 'center'; c.textBaseline = 'middle';
    c.font = `500 ${L.fs}px ${NAMEFONT}`;
    const lh = L.fs * 1.15, mid = (iy + ih + y + ch) / 2 - zh / 2;  // centre of the white area under the sign
    L.lines.forEach((ln, i) => c.fillText(ln, W / 2, mid + (i - (L.lines.length - 1) / 2) * lh));
    if (zone) { c.font = `500 ${zfs}px ${NAMEFONT}`; c.fillStyle = '#444'; c.fillText('(Granica Strefy Biletowej)', W / 2, mid + (L.lines.length - 1) / 2 * lh + L.fs * 0.55 + zfs * 0.75); }
    c.restore();
  }
  function drawKm(c, pt, km) {
    const txt = km.toFixed(1).replace('.', ',') + ' km';
    c.font = 'bold 40px Arial, Helvetica, sans-serif';
    const tw = c.measureText(txt).width + 30, x = pt.x - tw / 2, y = pt.y - 100;
    c.fillStyle = '#e0141e'; rr(c, x, y, tw, 58, 12); c.fill();
    c.fillStyle = '#fff'; c.textAlign = 'center'; c.textBaseline = 'middle'; c.fillText(txt, pt.x, y + 30);
    c.fillStyle = '#e0141e'; c.beginPath(); c.arc(pt.x, pt.y, 16, 0, 7); c.fill();
    c.lineWidth = 5; c.strokeStyle = '#fff'; c.stroke();
  }

  // ---------- audio ----------
  async function decodeAll(ac, recs) {
    const out = [];
    for (const r of recs) {
      if (!r) { out.push(null); continue; }
      try { const b = await getBlob(r, 'mp3'); out.push(await ac.decodeAudioData(await b.arrayBuffer())); }
      catch (e) { out.push(null); }
    }
    return out;
  }
  function playBuf(st, buf) {
    if (!buf) return Promise.resolve();
    return new Promise(res => {
      const s = st.ac.createBufferSource(); s.buffer = buf; s.connect(st.gain); s.onended = res; s.start();
      st.sources.push(s);
    });
  }

  // ---------- UI ----------
  function css() {
    if (document.getElementById('filmcss')) return;
    const s = document.createElement('style'); s.id = 'filmcss';
    s.textContent = `#film{position:fixed;inset:0;z-index:50;background:#0b0d12;display:flex;flex-direction:column;align-items:center;gap:10px;padding:12px;overflow:auto}
#film .fv{height:min(70vh,150vw);aspect-ratio:9/16;background:#000;border-radius:14px;overflow:hidden}
#film canvas.out{width:100%;height:100%;display:block}
#film .fc{display:flex;flex-wrap:wrap;gap:8px;justify-content:center;max-width:560px}
#film .st{color:#9aa3b2;font-size:13px;text-align:center;min-height:18px;max-width:560px}
#film .fin{background:#141922;border:1px solid #2a3240;color:#e8ecf2;border-radius:10px;padding:8px 10px;font:inherit}
#fed{position:fixed;inset:0;z-index:60;background:#0b0d12;display:flex;flex-direction:column}
#fed .fet{padding:10px;display:flex;flex-direction:column;gap:8px;align-items:center}
#fed select{max-width:100%;background:#141922;color:#e8ecf2;border:1px solid #2a3240;border-radius:10px;padding:8px}
#fed #emap{flex:1;min-height:300px}
#filmmap{position:fixed;left:-20000px;top:0;width:540px;height:960px}`;
    document.head.appendChild(s);
  }
  async function loadLib() {
    if (window.maplibregl) return;
    await new Promise((res, rej) => {
      const l = document.createElement('link'); l.rel = 'stylesheet'; l.href = 'lib/maplibre-gl.css'; document.head.appendChild(l);
      const s = document.createElement('script'); s.src = 'lib/maplibre-gl.js'; s.onload = res; s.onerror = rej; document.head.appendChild(s);
    });
  }

  async function open(opts) {
    // opts: {line, dir, vi, variant, items, tram}
    css(); close();
    const box = document.createElement('div'); box.id = 'film';
    box.innerHTML = `<div class="fv"><canvas class="out" width="${W}" height="${H}"></canvas></div>
      <div class="st" id="fst">Ładowanie mapy…</div>
      <div class="fc"><button class="chip on" data-s="sat">Satelita</button><button class="chip" data-s="map">Mapa</button>
        <span style="width:10px"></span>
        <button class="chip" data-v="slow">Wolno</button><button class="chip on" data-v="normal">Normalnie</button><button class="chip" data-v="fast">Szybko</button></div>
      <div class="fc"><input id="fnum" class="fin" style="width:72px" aria-label="Numer na tablicy"><input id="ftxt" class="fin" style="flex:1;min-width:180px" aria-label="Napis na tablicy">
        <button class="chip" id="fchg">Trasa zmieniona</button>
        <label class="chip" id="ffontl" style="cursor:pointer">Wczytaj czcionkę nazw<input type="file" id="ffont" accept=".otf,.ttf,.woff,.woff2" hidden></label></div>
      <div class="fc"><button class="btn" id="fedit">✏️ Popraw trasę</button></div>
      <div class="fc"><button class="btn pri" id="fplay">▶ Odtwórz</button><button class="btn" id="frec">● Nagraj wideo</button><button class="btn" id="fx">Zamknij</button></div>`;
    document.body.appendChild(box);
    const md = document.createElement('div'); md.id = 'filmmap'; document.body.appendChild(md);
    ui = { box, md, out: box.querySelector('canvas.out'), opts, style: 'sat', speed: 'normal' };
    ui.ctx = ui.out.getContext('2d');
    const st = t => { box.querySelector('#fst').textContent = t; };
    ui.status = st;
    box.querySelector('#fx').onclick = close;
    box.querySelectorAll('[data-s]').forEach(b => b.onclick = () => {
      if (run) return; ui.style = b.dataset.s;
      box.querySelectorAll('[data-s]').forEach(x => x.classList.toggle('on', x === b)); makeMap();
    });
    box.querySelectorAll('[data-v]').forEach(b => b.onclick = () => {
      if (run) return; ui.speed = b.dataset.v;
      box.querySelectorAll('[data-v]').forEach(x => x.classList.toggle('on', x === b));
    });
    box.querySelector('#ffont').onchange = async e => {
      const f = e.target.files[0]; if (!f) return;
      try { const buf = await f.arrayBuffer(); await useNameFont(buf); await kvSet('namefont', { name: f.name, buf });
        box.querySelector('#ffontl').firstChild.textContent = 'Czcionka: ' + f.name; st('Czcionka wczytana i zapamiętana w tej przeglądarce.'); }
      catch (err) { st('Nie udało się wczytać tej czcionki.'); }
    };
    kvGet('namefont').then(async v => { if (v && v.buf) { try { await useNameFont(v.buf); box.querySelector('#ffontl').firstChild.textContent = 'Czcionka: ' + v.name; } catch (e) {} } });
    box.querySelector('#fchg').onclick = e => { if (run) return; ui.changed = !ui.changed; e.target.classList.toggle('on', ui.changed); };
    box.querySelector('#fplay').onclick = () => start(false);
    box.querySelector('#fedit').onclick = () => { if (!run && ui.G) editor(); };
    box.querySelector('#frec').onclick = () => start(true);
    try {
      await Promise.all([loadLib(), loadImg('tram', 'lib/sign_tram.png'), loadImg('bus', 'lib/sign_bus.png'),
        (async () => { try { const f = new FontFace('Linia', 'url(lib/linia.ttf)'); await f.load(); document.fonts.add(f); } catch (e) {} })()]);
      const fn = opts.line.replace(/[^0-9A-Za-z_-]/g, '_');
      const geo = await (await fetch('geo/' + fn + '.json', { cache: 'no-cache' })).json();
      const g = geo[opts.dir + '/' + opts.vi];
      if (!g) { st('Brak przebiegu tej trasy w rozkładzie.'); return; }
      ui.raw = g; ui.fixKey = opts.line + '|' + opts.dir + '/' + opts.vi;
      ui.fixes = await loadFixes();
      ui.G = prep(applyFix(g, ui.fixes[ui.fixKey]));
    } catch (e) { st('Nie udało się wczytać mapy.'); return; }
    ui.num = opts.line; ui.text = ledText(opts.line, opts.variant.stops[opts.variant.stops.length - 1]);
    box.querySelector('#fnum').value = ui.num; box.querySelector('#ftxt').value = ui.text;
    box.querySelector('#fnum').oninput = e => { ui.num = e.target.value; };
    box.querySelector('#ftxt').oninput = e => { ui.text = e.target.value; };
    makeMap();
    loop();
  }

  function makeMap() {
    if (ui.map) { ui.map.remove(); ui.map = null; }
    const G = ui.G, b = new maplibregl.LngLatBounds();
    G.pts.forEach(p => b.extend([p[1], p[0]]));
    ui.bounds = b;
    const m = new maplibregl.Map({
      container: ui.md, style: (window.Film && Film.styleOverride) || STYLES[ui.style], interactive: false,
      attributionControl: false, pixelRatio: 2, fadeDuration: 0,
      canvasContextAttributes: { preserveDrawingBuffer: true, antialias: true },
      bounds: b, fitBoundsOptions: { padding: { top: 380, bottom: 120, left: 60, right: 60 } }
    });
    ui.map = m; ui.ready = false;
    m.on('load', () => {
      m.addSource('route', { type: 'geojson', data: { type: 'Feature', geometry: { type: 'LineString', coordinates: [] } } });
      m.addSource('full', { type: 'geojson', data: { type: 'Feature', geometry: { type: 'LineString', coordinates: G.pts.map(p => [p[1], p[0]]) } } });
      m.addSource('stops', { type: 'geojson', data: { type: 'FeatureCollection', features: G.stops.map(s => ({ type: 'Feature', geometry: { type: 'Point', coordinates: [s[1], s[0]] } })) } });
      m.addLayer({ id: 'full', type: 'line', source: 'full', paint: { 'line-color': '#ffffff', 'line-opacity': 0.35, 'line-width': 3, 'line-dasharray': [2, 2] } });
      m.addLayer({ id: 'route-c', type: 'line', source: 'route', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': '#5a0000', 'line-width': 10 } });
      m.addLayer({ id: 'route', type: 'line', source: 'route', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': '#ee1c25', 'line-width': 6 } });
      m.addLayer({ id: 'stops', type: 'circle', source: 'stops', paint: { 'circle-radius': 5, 'circle-color': '#fff', 'circle-stroke-color': '#123b96', 'circle-stroke-width': 2.5 } });
      ui.ready = true; ui.status('Gotowe. Wybierz mapę i prędkość, potem Odtwórz albo Nagraj wideo.');
    });
    m.on('error', () => {});
  }

  // one frame of the composite: map + overlays
  function loop() {
    if (!ui) return;
    const c = ui.ctx, t = performance.now() / 1000;
    c.fillStyle = '#10151d'; c.fillRect(0, 0, W, H);
    if (ui.map) { try { c.drawImage(ui.map.getCanvas(), 0, 0, W, H); } catch (e) {} }
    const S = ui.scene || {};
    if (S.head && ui.map) { const p = ui.map.project([S.head[1], S.head[0]]); drawKm(c, { x: p.x * 2, y: p.y * 2 }, S.km || 0); }
    drawLED(c, ui.num, ui.text, ui.changed, t);
    if (S.sign) drawSign(c, S.sign.name, ui.opts.tram, S.sign.req, Math.min(1, (t - S.sign.t0) / 0.25) * (S.sign.out ? Math.max(0, 1 - (t - S.sign.out) / 0.25) : 1), S.sign.zone);
    c.font = '24px Arial, Helvetica, sans-serif'; c.fillStyle = 'rgba(255,255,255,.75)'; c.textAlign = 'right'; c.textBaseline = 'alphabetic';
    c.fillText(ATTR[ui.style], W - 20, H - 20);
    ui.raf = requestAnimationFrame(loop);
  }

  function setRoute(d) {
    const src = ui.map.getSource('route');
    if (src) src.setData({ type: 'Feature', geometry: { type: 'LineString', coordinates: travelled(ui.G, d) } });
  }
  function camAt(d, zoom, bear) {
    const G = ui.G, p = at(G, d).p;
    const a = at(G, Math.max(0, d - 60)).p, b = at(G, Math.min(G.len, d + 220)).p;
    let target = hav(a, b) > 5 ? bearing(a, b) : bear;
    const nb = bear + angDiff(bear, target) * 0.08;
    ui.map.jumpTo({ center: [p[1], p[0]], zoom, pitch: 55, bearing: nb });
    return { p, bear: nb };
  }
  function moveEnd(m) { return new Promise(r => m.once('moveend', r)); }

  async function start(record) {
    if (run || !ui || !ui.ready) return;
    const o = ui.opts, G = ui.G, m = ui.map;
    const ac = new (window.AudioContext || window.webkitAudioContext)();
    await ac.resume();
    const gain = ac.createGain(); gain.connect(ac.destination);
    const aud = { ac, gain, sources: [] };
    run = { stop: false, aud };
    const alive = () => ui && run && !run.stop;
    ui.status('Przygotowanie zapowiedzi…');
    const introBuf = (await decodeAll(ac, [o.intro]))[0];
    let chgBuf = null;
    if (ui.changed) { try { chgBuf = await ac.decodeAudioData(await (await fetch('lib/trasa_zmieniona.mp3')).arrayBuffer()); } catch (e) {} }
    const stopBufs = await decodeAll(ac, o.items.map(x => x.rec));
    const zoneBufs = await decodeAll(ac, o.items.map(x => x.zone || null));
    let rec = null, chunks = [], mime = '';
    if (record) {
      const dest = ac.createMediaStreamDestination(); gain.connect(dest);
      const vs = ui.out.captureStream(FPS);
      const stream = new MediaStream([...vs.getVideoTracks(), ...dest.stream.getAudioTracks()]);
      for (const t of ['video/mp4;codecs=avc1.42E01E,mp4a.40.2', 'video/mp4', 'video/webm;codecs=vp9,opus', 'video/webm'])
        if (window.MediaRecorder && MediaRecorder.isTypeSupported(t)) { mime = t; break; }
      if (!mime) { ui.status('Ta przeglądarka nie umie nagrywać wideo.'); run = null; return; }
      rec = new MediaRecorder(stream, { mimeType: mime, videoBitsPerSecond: 8e6 });
      rec.ondataavailable = e => e.data.size && chunks.push(e.data);
      rec.start(1000);
    }
    const now = () => performance.now() / 1000;
    const speed = SPEEDS[ui.speed];
    ui.scene = {};
    ui.status(record ? 'Nagrywanie… nie przełączaj karty.' : 'Odtwarzanie…');
    try {
      // 1. overview with the line announcement
      m.fitBounds(ui.bounds, { padding: { top: 380, bottom: 120, left: 60, right: 60 }, pitch: 0, bearing: 0, duration: 0 });
      setRoute(0);
      await sleep(600);
      const t0 = now();
      await playBuf(aud, introBuf);
      if (chgBuf) { await sleep(250); await playBuf(aud, chgBuf); }
      await sleep(Math.max(0, 2500 - (now() - t0) * 1000));
      // 2. fly in to the first stop
      let bear = bearing(G.pts[0], at(G, 250).p);
      const s0 = G.stops[0];
      m.flyTo({ center: [s0[1], s0[0]], zoom: 16, pitch: 55, bearing: bear, duration: 2800, essential: true });
      await moveEnd(m);
      ui.scene.head = [s0[0], s0[1]]; ui.scene.km = 0;
      // 3. stop by stop
      for (let i = 0; i < G.stops.length && !run.stop; i++) {
        const name = o.items[i] ? o.items[i].name : '';
        ui.scene.sign = { name, req: o.items[i] && o.items[i].req, zone: !!(o.items[i] && o.items[i].zone), t0: now() };
        const ts = now();
        await playBuf(aud, stopBufs[i]);
        if (zoneBufs[i]) { await sleep(300); await playBuf(aud, zoneBufs[i]); }   // last stop in this ticket zone
        await sleep(Math.max(0, 1300 - (now() - ts) * 1000) + 250);
        ui.scene.sign.out = now();
        if (i === G.stops.length - 1) break;
        const d0 = G.stops[i][2], d1 = Math.max(d0, G.stops[i + 1][2]), L = d1 - d0;
        const dur = Math.max(1.4, L / speed), zoom = L > 2500 ? 14.6 : L > 1200 ? 15.3 : 16;
        const z0 = m.getZoom(), tm = now();
        await new Promise(res => {
          const step = () => {
            if (!ui || run.stop) return res();
            const u = Math.min(1, (now() - tm) / dur), d = d0 + L * ease(u);
            const zz = z0 + (zoom - z0) * Math.min(1, u * 3) + (u > 0.7 ? (16 - zoom) * (u - 0.7) / 0.3 : 0);
            const r = camAt(d, zz, bear); bear = r.bear;
            setRoute(d); ui.scene.head = r.p; ui.scene.km = d / 1000;
            if (ui.scene.sign && now() - ui.scene.sign.out > 0.3) ui.scene.sign = null;
            u < 1 ? requestAnimationFrame(step) : res();
          };
          step();
        });
      }
      // 4. finish: zoom back out over the whole route
      await sleep(900); ui.scene.sign = null; ui.scene.head = null;
      if (!run.stop) { m.fitBounds(ui.bounds, { padding: { top: 380, bottom: 120, left: 60, right: 60 }, pitch: 0, bearing: 0, duration: 2500 }); await moveEnd(m); await sleep(1500); }
    } catch (e) { console.error(e); }
    aud.sources.forEach(s => { try { s.stop(); } catch (e) {} });
    if (rec) {
      const done = new Promise(r => rec.onstop = r); rec.stop(); await done;
      const ext = mime.includes('mp4') ? 'mp4' : 'webm';
      const blob = new Blob(chunks, { type: mime.split(';')[0] });
      const fname = safe(`Linia ${o.line} - ${o.variant.stops[o.variant.stops.length - 1]}`) + '.' + ext;
      await saveFile(fname, blob);
      ui && ui.status(ext === 'mp4' ? 'Gotowe – wideo MP4 zapisane.' : 'Gotowe – zapisano jako WebM (ta przeglądarka nie nagrywa MP4).');
    } else ui && ui.status('Koniec. Możesz odtworzyć jeszcze raz albo nagrać wideo.');
    ac.close(); run = null; if (ui) ui.scene = {};
  }

  // route editor: pick a segment between two stops, click the real path on the map, save
  function editor() {
    const o = ui.opts, S = ui.raw.s, names = o.variant.stops;
    let segs = Object.assign({}, (ui.fixes[ui.fixKey] || {})), cur = 0, wps = (segs[0] || []).slice();
    const ed = document.createElement('div'); ed.id = 'fed';
    ed.innerHTML = `<div class="fet"><select id="eseg">${S.slice(0, -1).map((x, i) => `<option value="${i}">${i + 1}. ${esc(names[i])} → ${esc(names[i + 1])}${segs[i] || segs['p' + i] || segs['p' + (i + 1)] ? ' ✓' : ''}</option>`).join('')}</select>
      <div class="fc"><button class="chip" id="eundo">Cofnij punkt</button><button class="chip" id="eclr">Wyczyść odcinek</button><button class="chip" id="eprs">Przywróć przystanki</button>
      <button class="btn pri" id="esave">Zapisz odcinek</button><button class="btn" id="eexp">Wyślij poprawki</button><button class="btn" id="ex">Gotowe</button></div>
      <div class="st" id="est">Wybierz odcinek, potem klikaj na mapie po kolei punkty, którędy naprawdę jedzie pojazd. Żółte kółka przystanków możesz przeciągnąć w inne miejsce.</div></div><div id="emap"></div>`;
    document.body.appendChild(ed);
    const em = new maplibregl.Map({ container: ed.querySelector('#emap'), style: (window.Film && Film.styleOverride) || STYLES[ui.style], attributionControl: { compact: true } });
    const fc = pts => ({ type: 'Feature', geometry: { type: 'LineString', coordinates: pts.map(p => [p[1], p[0]]) } });
    const pos = i => segs['p' + i] || [S[i][0], S[i][1]];
    const mk = [0, 1].map(k => {
      const el = document.createElement('div');
      el.style.cssText = 'width:22px;height:22px;border-radius:50%;background:#ffd400;border:3px solid #000;cursor:grab;box-shadow:0 0 0 2px #fff';
      el.addEventListener('click', e => e.stopPropagation());
      const m = new maplibregl.Marker({ element: el, draggable: true });
      m.on('dragend', () => {
        const i = cur + k, ll = m.getLngLat();
        segs['p' + i] = [+ll.lat.toFixed(6), +ll.lng.toFixed(6)]; saveMine(ui.fixKey, segs); draw();
        est(`Przesunięto przystanek „${names[i]}”. Zapisane – trasa jest przycinana do nowego miejsca.`);
      });
      return m;
    });
    const draw = () => {
      if (!em.getSource('r')) return;
      const G = prep(applyFix(ui.raw, segs));
      em.getSource('r').setData(fc(G.pts));
      em.getSource('w').setData(fc([pos(cur), ...wps, pos(cur + 1)]));
      em.getSource('wp').setData({ type: 'FeatureCollection', features: wps.map(p => ({ type: 'Feature', geometry: { type: 'Point', coordinates: [p[1], p[0]] } })) });
      em.getSource('st').setData({ type: 'FeatureCollection', features: S.map((x, i) => ({ type: 'Feature', geometry: { type: 'Point', coordinates: [pos(i)[1], pos(i)[0]] } })) });
      mk.forEach((m, k) => m.setLngLat([pos(cur + k)[1], pos(cur + k)[0]]));
    };
    const focus = () => { const a = pos(cur), c = pos(cur + 1), b = new maplibregl.LngLatBounds([a[1], a[0]], [a[1], a[0]]); b.extend([c[1], c[0]]); wps.forEach(p => b.extend([p[1], p[0]])); em.fitBounds(b, { padding: 80, maxZoom: 17, duration: 0 }); };
    em.on('load', () => {
      em.addSource('r', { type: 'geojson', data: fc([]) }); em.addSource('w', { type: 'geojson', data: fc([]) });
      em.addSource('wp', { type: 'geojson', data: { type: 'FeatureCollection', features: [] } });
      em.addSource('ss', { type: 'geojson', data: { type: 'FeatureCollection', features: [] } });
      em.addSource('st', { type: 'geojson', data: { type: 'FeatureCollection', features: S.map(p => ({ type: 'Feature', geometry: { type: 'Point', coordinates: [p[1], p[0]] } })) } });
      em.addLayer({ id: 'r', type: 'line', source: 'r', paint: { 'line-color': '#ee1c25', 'line-width': 4, 'line-opacity': 0.8 } });
      em.addLayer({ id: 'w', type: 'line', source: 'w', paint: { 'line-color': '#ffd400', 'line-width': 5 } });
      em.addLayer({ id: 'st', type: 'circle', source: 'st', paint: { 'circle-radius': 5, 'circle-color': '#fff', 'circle-stroke-color': '#123b96', 'circle-stroke-width': 2 } });
      em.addLayer({ id: 'wp', type: 'circle', source: 'wp', paint: { 'circle-radius': 5, 'circle-color': '#ffd400', 'circle-stroke-color': '#000', 'circle-stroke-width': 1.5 } });
      mk.forEach(m => m.setLngLat([0, 0]).addTo(em));
      draw(); focus();
    });
    const est = t => { ed.querySelector('#est').textContent = t; };
    em.on('click', e => { wps.push([+e.lngLat.lat.toFixed(6), +e.lngLat.lng.toFixed(6)]); draw(); est(`Punktów na tym odcinku: ${wps.length}. Kliknij „Zapisz odcinek”, gdy skończysz.`); });
    const sel = ed.querySelector('#eseg');
    sel.onchange = () => { cur = +sel.value; wps = (segs[cur] || []).slice(); draw(); focus(); est(segs[cur] ? 'Ten odcinek ma już poprawkę – możesz ją zmienić.' : 'Klikaj na mapie punkty trasy między żółtymi przystankami.'); };
    ed.querySelector('#eundo').onclick = () => { wps.pop(); draw(); };
    ed.querySelector('#eclr').onclick = () => { wps = []; delete segs[cur]; saveMine(ui.fixKey, segs); sel.options[cur].text = sel.options[cur].text.replace(' ✓', ''); draw(); est('Odcinek przywrócony do przebiegu z rozkładu.'); };
    ed.querySelector('#eprs').onclick = () => { delete segs['p' + cur]; delete segs['p' + (cur + 1)]; saveMine(ui.fixKey, segs); draw(); focus(); est('Przystanki tego odcinka wróciły na miejsce z rozkładu.'); };
    ed.querySelector('#esave').onclick = () => {
      if (!wps.length) { est('Najpierw kliknij na mapie punkty trasy.'); return; }
      segs[cur] = wps.slice(); saveMine(ui.fixKey, segs);
      if (!sel.options[cur].text.endsWith(' ✓')) sel.options[cur].text += ' ✓';
      draw(); est('Zapisano w tej przeglądarce. Filmik już jedzie poprawioną trasą.');
    };
    ed.querySelector('#eexp').onclick = async () => {
      let mine = {}; try { mine = JSON.parse(localStorage.getItem('routeFixes') || '{}'); } catch (e) {}
      if (!Object.keys(mine).length) { est('Nie masz jeszcze żadnych zapisanych poprawek.'); return; }
      const blob = new Blob([JSON.stringify(mine)], { type: 'application/json' });
      await saveFile('poprawki-tras.json', blob);
      est('Zapisano plik poprawki-tras.json – wyślij go w czacie, a wbuduję poprawki na stałe.');
    };
    ed.querySelector('#ex').onclick = async () => {
      em.remove(); ed.remove();
      ui.fixes = await loadFixes(); ui.G = prep(applyFix(ui.raw, ui.fixes[ui.fixKey])); makeMap();
    };
  }

  function close() {
    const fe = document.getElementById('fed'); if (fe) fe.remove();
    if (run) { run.stop = true; run.aud.sources.forEach(x => { try { x.stop(); } catch (e) {} }); }
    if (!ui) { const b = document.getElementById('film'); if (b) b.remove(); return; }
    cancelAnimationFrame(ui.raf);
    if (ui.map) ui.map.remove();
    ui.md.remove(); ui.box.remove(); ui = null;
  }

  window.Film = { open, close, _ledText: ledText, _drawSign: drawSign, _loadImg: loadImg, _drawLED: drawLED };
})();
