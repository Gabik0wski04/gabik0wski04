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
    if (/Dworzec Główny (Zachód|Wschód)/.test(dest)) t += ' ,';   // train
    if (/^8/.test(line)) t += " '";                                // cemetery line
    if (/Kraków Airport/.test(dest)) t += ' {';                    // plane
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
    if (!S.length) return g;
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
    const out = [], G1 = { pts, cum, len: cum[cum.length - 1] };
    for (let i = 0; i < n; i++) {
      out.push([P[i][0], P[i][1], cum[cuts[i]]]);
      const add = i < n - 1 && segs['a' + i];
      if (add && add.length) {              // stops added by the user inside segment i, ordered along the route
        const lo = cum[cuts[i]], hi = cum[cuts[i + 1]];
        add.map(a => [a.q[0], a.q[1], proj(G1, a.q, lo, hi), { n: a.n, r: a.r ? 1 : 0 }])
          .sort((x, y) => x[2] - y[2]).forEach(x => out.push(x));
      }
    }
    return { p: pts, s: out, len: G1.len };
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
    c.shadowColor = '#ff9a1a'; c.shadowBlur = 12; c.fillStyle = '#ffb02e';
    if (tw <= avail) { c.beginPath(); c.rect(x0, y0, W - x0, bh); c.clip(); c.fillText(text, x0 + (avail - tw) / 2, base); }
    else {
      // extra symbols at the end (train / cemetery / plane) stay still at the right edge, only the direction scrolls
      const m = text.match(/^(.*?)((?:\s+[,'{])+)\s*$/);
      const body = m ? m[1] : text, sym = m ? m[2].trim() : '';
      const sw = sym ? c.measureText(sym).width : 0, x1 = W - 16 - sw;
      if (sym) c.fillText(sym, x1, base);
      const right = sym ? x1 - 24 : W, bw = c.measureText(body).width;
      c.beginPath(); c.rect(x0, y0, right - x0, bh); c.clip();
      const gap = 260, per = bw + gap, off = (t * 150) % per;
      c.fillText(body, x0 - off, base); c.fillText(body, x0 - off + per, base);
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
    if (!ui.opts.tram) return;               // buses are drawn as a 3D model on the map
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
#fed input[type=text]{background:#141922;color:#e8ecf2;border:1px solid #2a3240;border-radius:10px;padding:8px;min-width:0;flex:1}
#fed .fadd{display:flex;gap:6px;align-items:center;flex-wrap:wrap;justify-content:center;width:100%;max-width:640px}
#fed .fadded{display:flex;gap:6px;flex-wrap:wrap;justify-content:center}
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
      <div class="fc" id="fveh"><button class="chip on" data-b="art">Przegubowy 18 m</button><button class="chip" data-b="solo">Zwykły 12 m</button></div>
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
    ui.bus = 'art';
    if (opts.tram) box.querySelector('#fveh').style.display = 'none';
    box.querySelectorAll('[data-b]').forEach(b => b.onclick = () => {
      if (run) return; ui.bus = b.dataset.b; ui.lastBus = null;
      box.querySelectorAll('[data-b]').forEach(x => x.classList.toggle('on', x === b));
      if (ui.map && ui.ready) setBus(ui.busD || 0);
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
    ui.map = m; ui.ready = false; ui.lastD = null;
    // share of the line's length (as the map measures it) at every route point, for the growing red line
    { const f = [0]; for (let i = 1; i < G.pts.length; i++) { const a = G.pts[i - 1], b = G.pts[i];
        f.push(f[i - 1] + hav(a, b) / Math.cos((a[0] + b[0]) / 2 * rad)); }
      const tot = f[f.length - 1] || 1; ui.frac = f.map(x => x / tot); }
    m.on('load', () => {
      m.addSource('route', { type: 'geojson', lineMetrics: true, data: { type: 'Feature', geometry: { type: 'LineString', coordinates: G.pts.map(p => [p[1], p[0]]) } } });
      m.addSource('full', { type: 'geojson', data: { type: 'Feature', geometry: { type: 'LineString', coordinates: G.pts.map(p => [p[1], p[0]]) } } });
      m.addSource('stops', { type: 'geojson', data: { type: 'FeatureCollection', features: G.stops.map(s => ({ type: 'Feature', geometry: { type: 'Point', coordinates: [s[1], s[0]] } })) } });
      m.addLayer({ id: 'full', type: 'line', source: 'full', paint: { 'line-color': '#ffffff', 'line-opacity': 0.35, 'line-width': 3, 'line-dasharray': [2, 2] } });
      m.addLayer({ id: 'route-c', type: 'line', source: 'route', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-width': 10, 'line-gradient': grad('#5a0000', 0) } });
      m.addLayer({ id: 'route', type: 'line', source: 'route', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-width': 6, 'line-gradient': grad('#ee1c25', 0) } });
      m.addLayer({ id: 'stops', type: 'circle', source: 'stops', paint: { 'circle-radius': 5, 'circle-color': '#fff', 'circle-stroke-color': '#123b96', 'circle-stroke-width': 2.5 } });
      m.addSource('bus', { type: 'geojson', data: { type: 'FeatureCollection', features: [] } });
      m.addLayer({ id: 'bus', type: 'fill-extrusion', source: 'bus', paint: { 'fill-extrusion-color': ['get', 'c'], 'fill-extrusion-height': ['get', 'h'], 'fill-extrusion-base': ['get', 'b'], 'fill-extrusion-opacity': 1 } });
      ui.ready = true; ui.lastBus = null; setBus(0); ui.status('Gotowe. Wybierz mapę i prędkość, potem Odtwórz albo Nagraj wideo.');
    });
    m.on('error', () => {});
  }

  // one frame of the composite: map + overlays. t = film time (seconds) while a film runs, else wall time
  function compose(t) {
    const c = ui.ctx;
    c.fillStyle = '#10151d'; c.fillRect(0, 0, W, H);
    if (ui.map) { try { c.drawImage(ui.map.getCanvas(), 0, 0, W, H); } catch (e) {} }
    const S = ui.scene || {};
    if (S.head && ui.map) { const p = ui.map.project([S.head[1], S.head[0]]); drawKm(c, { x: p.x * 2, y: p.y * 2 }, S.km || 0); }
    drawLED(c, ui.num, ui.text, ui.changed, t);
    if (S.sign) drawSign(c, S.sign.name, ui.opts.tram, S.sign.req, Math.min(1, (t - S.sign.t0) / 0.25) * Math.max(0, Math.min(1, 1 - (t - S.sign.out) / 0.25)), S.sign.zone);
    c.font = '24px Arial, Helvetica, sans-serif'; c.fillStyle = 'rgba(255,255,255,.75)'; c.textAlign = 'right'; c.textBaseline = 'alphabetic';
    c.fillText(ATTR[ui.style], W - 20, H - 20);
  }
  function loop() {
    if (!ui) return;
    if (!ui.offline) {                      // while an offline render runs it draws the frames itself
      let t = performance.now() / 1000;
      if (run && run.live) { t = run.aud.ac.currentTime - run.base; applyState(run.plan, t); }
      compose(t);
    }
    ui.raf = requestAnimationFrame(loop);
  }

  // the red line grows by moving a colour step along the whole route (no geometry update, so it is instant)
  function grad(col, p) { return ['step', ['line-progress'], col, Math.max(1e-6, Math.min(1, p)), 'rgba(0,0,0,0)']; }
  function setRoute(d) {
    if (ui.lastD === d) return; ui.lastD = d;
    const G = ui.G, e = at(G, d), i = e.i, seg = (G.cum[i + 1] - G.cum[i]) || 1;
    const fr = ui.frac, p = fr[i] + ((fr[i + 1] !== undefined ? fr[i + 1] : fr[i]) - fr[i]) * Math.min(1, (d - G.cum[i]) / seg);
    const m = ui.map; if (!m.getLayer('route')) return;
    m.setPaintProperty('route', 'line-gradient', grad('#ee1c25', d >= G.len ? 1 : p));
    m.setPaintProperty('route-c', 'line-gradient', grad('#5a0000', d >= G.len ? 1 : p));
  }
  // ---------- 3D bus (generic low-floor city bus, 12 m or 18 m articulated), drawn as stacked extrusions ----------
  const BUS_SCALE = 4;                    // models are enlarged so they read well from the film camera
  const BUS = {
    solo: [[0, 12]],                        // sections: [front, rear] metres behind the front bumper
    art: [[0, 10.4], [11.0, 18.0]]
  };
  function posAt(G, x) {                    // point on the route at distance x, extended straight beyond both ends
    if (x >= 0 && x <= G.len) return at(G, x).p;
    const a = x < 0 ? G.pts[0] : G.pts[G.pts.length - 1], b = x < 0 ? at(G, Math.min(G.len, 15)).p : at(G, Math.max(0, G.len - 15)).p;
    const L = hav(a, b) || 1, k = (x < 0 ? -x : x - G.len) / L;
    return [a[0] + (a[0] - b[0]) * k, a[1] + (a[1] - b[1]) * k];
  }
  function boxPoly(f, r, w) {               // rectangle from point f (front) to r (rear), w metres wide
    const ky = 111320, kx = 111320 * Math.cos(f[0] * rad);
    let dx = (f[1] - r[1]) * kx, dy = (f[0] - r[0]) * ky; const L = Math.hypot(dx, dy) || 1; dx /= L; dy /= L;
    const px = -dy * w / 2, py = dx * w / 2;
    const c = (p, sx, sy) => [p[1] + sx / kx, p[0] + sy / ky];
    const ring = [c(f, px, py), c(f, -px, -py), c(r, -px, -py), c(r, px, py)]; ring.push(ring[0]);
    return ring;
  }
  function busFeatures(G, d, type) {
    const k = BUS_SCALE, W2 = 2.55 * k, out = [];
    const feat = (ring, b, h, c) => out.push({ type: 'Feature', properties: { b: b * k, h: h * k, c }, geometry: { type: 'Polygon', coordinates: [ring] } });
    BUS[type].forEach(([a, z], si) => {
      const f = posAt(G, d - a * k), r = posAt(G, d - z * k);
      const body = boxPoly(f, r, W2), NAVY = '#163a8c', WHITE = '#f4f6f9', GLASS = '#0f1c3a';
      feat(body, 0.3, 0.75, WHITE);                           // white skirt (Kraków colours)
      feat(body, 0.75, 1.0, NAVY);                            // navy side
      feat(boxPoly(f, r, W2 * 0.99), 1.0, 2.5, GLASS);        // tinted windows on navy
      feat(body, 2.5, 2.85, NAVY);
      feat(boxPoly(f, r, W2 * 0.96), 2.85, 3.0, WHITE);       // white roof
      feat(boxPoly(posAt(G, d - (a + 1.5) * k), posAt(G, d - (a + 5.5) * k), W2 * 0.7), 3.0, 3.3, '#dfe3e8'); // roof equipment
      // wheels: a pair of dark blocks per axle, sticking out a little at the sides
      const axles = type === 'solo' ? [2.7, 8.7] : si === 0 ? [2.7, 8.6] : [16.0];
      axles.forEach(x => { if (x > a && x < z) feat(boxPoly(posAt(G, d - (x - 0.5) * k), posAt(G, d - (x + 0.5) * k), W2 * 1.02), 0, 0.55, '#15171b'); });
      if (si === 0) {                                          // front: windscreen and destination display
        const f2 = posAt(G, d - 0.35 * k);
        feat(boxPoly(f, f2, W2 * 0.96), 0.3, 0.75, '#f4f6f9');   // white bumper
        feat(boxPoly(f, f2, W2 * 0.94), 0.75, 2.6, '#0b1118');    // black front with windscreen
        feat(boxPoly(f, f2, W2 * 0.7), 2.55, 2.8, '#ffb02e');     // destination display
      }
      if (si === 1) {                                          // articulation bellows
        const j1 = posAt(G, d - 10.4 * k), j2 = posAt(G, d - 11.0 * k);
        feat(boxPoly(j1, j2, W2 * 0.92), 0.4, 3.0, '#20242b');
      }
    });
    return out;
  }
  function setBus(d) {
    if (!ui.map || ui.opts.tram) return null;
    const type = ui.bus || 'art';
    if (ui.lastBus === type + ':' + d) return null;
    ui.lastBus = type + ':' + d; ui.busD = d;
    const m = ui.map, src = m.getSource('bus'); if (!src) return null;
    const done = new Promise(r => {
      const f = e => { if (e.sourceId === 'bus' && m.isSourceLoaded('bus')) { m.off('sourcedata', f); r(); } };
      m.on('sourcedata', f); setTimeout(() => { m.off('sourcedata', f); r(); }, 600);
    });
    src.setData({ type: 'FeatureCollection', features: busFeatures(ui.G, d, type) });
    return done;
  }
  function moveEnd(m) { return new Promise(r => m.once('moveend', r)); }

  // ---------- the film as a fixed timeline: every frame and every announcement has an exact time ----------
  const PAD = { top: 380, bottom: 120, left: 60, right: 60 };
  function makePlan(G, introDur, chgDur, stopDurs, zoneDurs, speed) {
    const segs = [], audio = [], signs = [];
    let t = 0.6;
    audio.push({ t, k: 'intro' });
    let ovEnd = t + introDur;
    if (chgDur) { audio.push({ t: ovEnd + 0.25, k: 'chg' }); ovEnd += 0.25 + chgDur; }
    ovEnd = Math.max(ovEnd, 0.6 + 2.5);
    segs.push({ k: 'ov', t0: 0, t1: ovEnd });
    segs.push({ k: 'fly', t0: ovEnd, t1: ovEnd + 2.8 });
    t = ovEnd + 2.8;
    const n = G.stops.length;
    for (let i = 0; i < n; i++) {
      const a = stopDurs[i] || 0, z = zoneDurs[i] || 0;
      audio.push({ t, k: 's' + i });
      if (z) audio.push({ t: t + a + 0.3, k: 'z' + i });
      const hold = Math.max(1.3, a + (z ? 0.3 + z : 0)) + 0.25;
      signs.push({ i, t0: t, out: t + hold });
      segs.push({ k: 'stop', i, t0: t, t1: t + hold });
      t += hold;
      if (i === n - 1) break;
      const d0 = G.stops[i][2], d1 = Math.max(d0, G.stops[i + 1][2]), L = d1 - d0;
      const dur = Math.max(1.4, L / speed), zoom = L > 2500 ? 14.6 : L > 1200 ? 15.3 : 16;
      segs.push({ k: 'trav', i, t0: t, t1: t + dur, d0, L, zoom });
      t += dur;
    }
    segs.push({ k: 'tail', t0: t, t1: t + 0.9 }); t += 0.9;
    segs.push({ k: 'back', t0: t, t1: t + 2.5 }); t += 2.5;
    segs.push({ k: 'end', t0: t, t1: t + 1.5 }); t += 1.5;
    const P = { segs, audio, signs, T: t, G };
    // camera bearing, simulated frame by frame so that preview and recording are identical
    const N = Math.ceil(t * FPS) + 2, bears = new Float32Array(N);
    let bear = bearing(G.pts[0], at(G, 250).p); P.bear0 = bear;
    for (let f = 0; f < N; f++) {
      const sg = segAt(P, f / FPS);
      if (sg.k === 'trav') {
        const u = Math.min(1, (f / FPS - sg.t0) / (sg.t1 - sg.t0)), d = sg.d0 + sg.L * ease(u);
        const a = at(G, Math.max(0, d - 60)).p, b = at(G, Math.min(G.len, d + 220)).p;
        if (hav(a, b) > 5) bear += angDiff(bear, bearing(a, b)) * 0.15;
      }
      bears[f] = bear;
    }
    P.bears = bears;
    return P;
  }
  function segAt(P, t) {
    const S = P.segs;
    let lo = 0, hi = S.length - 1;
    while (lo < hi) { const m = (lo + hi + 1) >> 1; if (S[m].t0 <= t) lo = m; else hi = m - 1; }
    return S[lo];
  }
  function lerp(a, b, u) { return a + (b - a) * u; }
  function stateAt(P, t) {
    const G = P.G, sg = segAt(P, Math.max(0, Math.min(P.T, t)));
    const bear = P.bears[Math.max(0, Math.min(P.bears.length - 1, Math.round(t * FPS)))];
    const u = Math.max(0, Math.min(1, (t - sg.t0) / ((sg.t1 - sg.t0) || 1)));
    const ov = P.cam0, last = G.stops[G.stops.length - 1];
    const camAtD = (d, zoom, b) => { const p = at(G, d).p; return { center: [p[1], p[0]], zoom, pitch: 55, bearing: b }; };
    let cam, d = 0, head = null;
    if (sg.k === 'ov') cam = ov;
    else if (sg.k === 'fly') {
      const e = ease(u), p = at(G, G.stops[0][2]).p;
      cam = { center: [lerp(ov.center[0], p[1], e), lerp(ov.center[1], p[0], e)], zoom: lerp(ov.zoom, 16, e), pitch: 55 * e, bearing: P.bear0 * e };
    } else if (sg.k === 'stop') { d = G.stops[sg.i][2]; cam = camAtD(d, 16, bear); head = at(G, d).p; }
    else if (sg.k === 'trav') {
      d = sg.d0 + sg.L * ease(u);
      const zz = 16 + (sg.zoom - 16) * Math.min(1, u * 3) + (u > 0.7 ? (16 - sg.zoom) * (u - 0.7) / 0.3 : 0);
      cam = camAtD(d, zz, bear); head = at(G, d).p;
    } else if (sg.k === 'tail') { d = last[2]; cam = camAtD(d, 16, bear); }
    else if (sg.k === 'back') {
      d = last[2]; const e = ease(u), p = at(G, d).p, b0 = P.bears[Math.round(sg.t0 * FPS)] || 0;
      cam = { center: [lerp(p[1], ov.center[0], e), lerp(p[0], ov.center[1], e)], zoom: lerp(16, ov.zoom, e), pitch: 55 * (1 - e), bearing: b0 + angDiff(b0, 0) * e };
    } else { d = last[2]; cam = ov; }
    let sign = null;
    for (const s of P.signs) if (s.t0 <= t && t < s.out + 0.3) sign = s;
    return { cam, d, head, km: d / 1000, sign };
  }
  function applyState(P, t) {
    const st = stateAt(P, t), m = ui.map;
    m.jumpTo(st.cam);
    setRoute(st.d);
    const busDone = setBus(st.d);
    const it = st.sign && P.items[st.sign.i];
    ui.scene = { head: st.head, km: st.km,
      sign: st.sign ? { name: it ? it.name : '', req: it && it.req, zone: !!(it && it.zone), t0: st.sign.t0, out: st.sign.out } : null };
    return busDone;
  }
  function waitRendered(m) {
    return new Promise(r => {
      let done = false; const f = () => { if (!done) { done = true; r(); } };
      m.once('idle', f); m.triggerRepaint(); setTimeout(f, 5000);
    });
  }

  async function prepare(o) {
    const ac = new (window.AudioContext || window.webkitAudioContext)();
    const introBuf = (await decodeAll(ac, [o.intro]))[0];
    let chgBuf = null;
    if (ui.changed) { try { chgBuf = await ac.decodeAudioData(await (await fetch('lib/trasa_zmieniona.mp3')).arrayBuffer()); } catch (e) {} }
    const items = [];
    { let k = 0; ui.G.stops.forEach(st => {
        if (st[3]) items.push({ name: st[3].n, req: st[3].r, rec: (window.recFor ? window.recFor(st[3].n, st[3].r) : null), zone: null });
        else items.push(o.items[k++] || { name: '' });
      }); }
    const stopBufs = await decodeAll(ac, items.map(x => x.rec));
    const zoneBufs = await decodeAll(ac, items.map(x => x.zone || null));
    const P = makePlan(ui.G, introBuf ? introBuf.duration : 0, chgBuf ? chgBuf.duration : 0,
      stopBufs.map(b => b ? b.duration : 0), zoneBufs.map(b => b ? b.duration : 0), SPEEDS[ui.speed]);
    P.items = items;
    const cam = ui.map.cameraForBounds(ui.bounds, { padding: PAD });
    P.cam0 = { center: [cam.center.lng, cam.center.lat], zoom: cam.zoom, pitch: 0, bearing: 0 };
    const buf = k => k === 'intro' ? introBuf : k === 'chg' ? chgBuf : k[0] === 's' ? stopBufs[+k.slice(1)] : zoneBufs[+k.slice(1)];
    P.audio.forEach(a => a.buf = buf(a.k));
    return { ac, P };
  }

  async function start(record) {
    if (run || !ui || !ui.ready) return;
    const o = ui.opts;
    ui.status('Przygotowanie zapowiedzi…');
    run = { stop: false };
    let prep;
    try { prep = await prepare(o); } catch (e) { console.error(e); ui.status('Nie udało się przygotować filmiku.'); run = null; return; }
    const { ac, P } = prep;
    if (record && window.VideoEncoder && window.AudioEncoder && window.OfflineAudioContext && window.Mp4Muxer !== false) {
      try { await renderOffline(P, o); } catch (e) { console.error(e); ui && ui.status('Nie udało się zapisać wideo: ' + (e && e.message || e)); }
      ac.close(); run = null; if (ui) { ui.offline = false; ui.scene = {}; }
      return;
    }
    // live: audio clock drives the picture, so sound and image cannot drift apart
    await ac.resume();
    const gain = ac.createGain(); gain.connect(ac.destination);
    run.aud = { ac, gain, sources: [] };
    let rec = null, chunks = [], mime = '';
    if (record) {   // fallback for browsers without WebCodecs: record the live playback
      const dest = ac.createMediaStreamDestination(); gain.connect(dest);
      const vs = ui.out.captureStream(FPS);
      const stream = new MediaStream([...vs.getVideoTracks(), ...dest.stream.getAudioTracks()]);
      for (const t of ['video/mp4;codecs=avc1.42E01E,mp4a.40.2', 'video/mp4', 'video/webm;codecs=vp9,opus', 'video/webm'])
        if (window.MediaRecorder && MediaRecorder.isTypeSupported(t)) { mime = t; break; }
      if (!mime) { ui.status('Ta przeglądarka nie umie nagrywać wideo.'); ac.close(); run = null; return; }
      rec = new MediaRecorder(stream, { mimeType: mime, videoBitsPerSecond: 8e6 });
      rec.ondataavailable = e => e.data.size && chunks.push(e.data);
      rec.start(1000);
    }
    run.base = ac.currentTime + 0.15; run.plan = P;
    for (const a of P.audio) if (a.buf) {
      const s = ac.createBufferSource(); s.buffer = a.buf; s.connect(gain); s.start(run.base + a.t); run.aud.sources.push(s);
    }
    run.live = true;
    ui.status(record ? 'Nagrywanie… nie przełączaj karty.' : 'Odtwarzanie…');
    while (ui && run && !run.stop && ac.currentTime - run.base < P.T) await sleep(100);
    if (run) run.live = false;
    if (run && run.aud) run.aud.sources.forEach(s => { try { s.stop(); } catch (e) {} });
    if (rec) {
      const done = new Promise(r => rec.onstop = r); rec.stop(); await done;
      const ext = mime.includes('mp4') ? 'mp4' : 'webm';
      const blob = new Blob(chunks, { type: mime.split(';')[0] });
      await saveFile(safe(`Linia ${o.line} - ${o.variant.stops[o.variant.stops.length - 1]}`) + '.' + ext, blob);
      ui && ui.status('Gotowe – wideo zapisane.');
    } else ui && ui.status('Koniec. Możesz odtworzyć jeszcze raz albo nagrać wideo.');
    ac.close(); run = null; if (ui) { ui.scene = {}; ui.lastD = null; }
  }

  async function loadMuxer() {
    if (window.Mp4Muxer) return;
    await new Promise((res, rej) => { const s = document.createElement('script'); s.src = 'lib/mp4-muxer.js'; s.onload = res; s.onerror = rej; document.head.appendChild(s); });
  }

  // offline render: frame by frame (as fast as the computer can), audio mixed exactly at its times, saved as MP4
  async function renderOffline(P, o) {
    await loadMuxer();
    const SR = 48000;
    // audio codec: AAC where the browser has it, else Opus (both fine in MP4)
    let acodec = null;
    for (const [c, mc] of [['mp4a.40.2', 'aac'], ['opus', 'opus']]) {
      try { const r = await AudioEncoder.isConfigSupported({ codec: c, sampleRate: SR, numberOfChannels: 1, bitrate: 128000 }); if (r.supported) { acodec = [c, mc]; break; } } catch (e) {}
    }
    let vcfg = null;
    for (const c of ['avc1.640028', 'avc1.4d0028', 'avc1.420028']) {
      for (const hw of ['prefer-hardware', 'no-preference']) {
        const cfg = { codec: c, width: W, height: H, bitrate: 8e6, framerate: FPS, hardwareAcceleration: hw, avc: { format: 'avc' } };
        try { const r = await VideoEncoder.isConfigSupported(cfg); if (r.supported) { vcfg = cfg; break; } } catch (e) {}
      }
      if (vcfg) break;
    }
    if (!vcfg) throw new Error('przeglądarka nie ma kodera H.264');
    const muxer = new Mp4Muxer.Muxer({
      target: new Mp4Muxer.ArrayBufferTarget(), fastStart: 'in-memory', firstTimestampBehavior: 'offset',
      video: { codec: 'avc', width: W, height: H, frameRate: FPS },
      audio: acodec ? { codec: acodec[1], sampleRate: SR, numberOfChannels: 1 } : undefined
    });
    let err = null;
    const venc = new VideoEncoder({ output: (ch, meta) => muxer.addVideoChunk(ch, meta), error: e => err = e });
    venc.configure(vcfg);
    // audio: mix everything on an offline context, then encode
    if (acodec) {
      ui.status('Miksowanie dźwięku…');
      const len = Math.ceil(P.T * SR), oc = new OfflineAudioContext(1, len, SR);
      for (const a of P.audio) if (a.buf) { const s = oc.createBufferSource(); s.buffer = a.buf; s.connect(oc.destination); s.start(a.t); }
      const mix = await oc.startRendering(), data = mix.getChannelData(0);
      const aenc = new AudioEncoder({ output: (ch, meta) => muxer.addAudioChunk(ch, meta), error: e => err = e });
      aenc.configure({ codec: acodec[0], sampleRate: SR, numberOfChannels: 1, bitrate: 128000 });
      const CH = 4800;
      for (let i = 0; i < len; i += CH) {
        const part = data.slice(i, Math.min(len, i + CH));
        const ad = new AudioData({ format: 'f32-planar', sampleRate: SR, numberOfFrames: part.length, numberOfChannels: 1, timestamp: Math.round(i / SR * 1e6), data: part });
        aenc.encode(ad); ad.close();
      }
      await aenc.flush(); aenc.close();
    }
    // video: step the timeline one frame at a time and wait until the map has drawn it
    ui.offline = true;
    const m = ui.map, N = Math.ceil(P.T * FPS), t0 = performance.now();
    for (let f = 0; f < N; f++) {
      if (!ui || run.stop) throw new Error('przerwano');
      if (err) throw err;
      const t = f / FPS;
      const bd = applyState(P, t);
      if (bd) await bd;                              // the bus model moved: wait until the map has its new shape
      m.redraw();                                   // draw this frame now; wait only if map tiles are still loading
      if (!m.areTilesLoaded()) { await waitRendered(m); m.redraw(); }
      compose(t);
      const vf = new VideoFrame(ui.out, { timestamp: Math.round(t * 1e6), duration: Math.round(1e6 / FPS) });
      venc.encode(vf, { keyFrame: f % (FPS * 2) === 0 }); vf.close();
      while (venc.encodeQueueSize > 4) await new Promise(r => venc.addEventListener('dequeue', r, { once: true }));
      if (f % 15 === 0) {
        const el = (performance.now() - t0) / 1000, left = f ? el / f * (N - f) : 0;
        ui.status(`Renderowanie wideo… ${Math.round(f / N * 100)}% (zostało ok. ${Math.ceil(left)} s). Nie przełączaj karty.`);
      }
    }
    await venc.flush(); venc.close();
    if (err) throw err;
    muxer.finalize();
    const blob = new Blob([muxer.target.buffer], { type: 'video/mp4' });
    ui.offline = false;
    await saveFile(safe(`Linia ${o.line} - ${o.variant.stops[o.variant.stops.length - 1]}`) + '.mp4', blob);
    ui.status(`Gotowe – wideo MP4 zapisane (${Math.round((performance.now() - t0) / 1000)} s renderowania).`);
  }

  // route editor: pick a segment between two stops, click the real path on the map, save
  function editor() {
    const o = ui.opts, S = ui.raw.s, names = o.variant.stops;
    let segs = Object.assign({}, (ui.fixes[ui.fixKey] || {})), cur = 0, wps = (segs[0] || []).slice();
    const ed = document.createElement('div'); ed.id = 'fed';
    ed.innerHTML = `<div class="fet"><select id="eseg">${S.slice(0, -1).map((x, i) => `<option value="${i}">${i + 1}. ${esc(names[i])} → ${esc(names[i + 1])}${segs[i] || segs['p' + i] || segs['p' + (i + 1)] || segs['a' + i] ? ' ✓' : ''}</option>`).join('')}</select>
      <div class="fc"><button class="chip" id="eundo">Cofnij punkt</button><button class="chip" id="eclr">Wyczyść odcinek</button><button class="chip" id="eprs">Przywróć przystanki</button>
      <button class="btn pri" id="esave">Zapisz odcinek</button><button class="btn" id="eexp">Wyślij poprawki</button><button class="btn" id="ex">Gotowe</button></div>
      <div class="fadd"><input type="text" id="ename" list="enames" placeholder="Nazwa nowego przystanku"><datalist id="enames"></datalist>
        <label class="chip"><input type="checkbox" id="ereq"> N/Ż</label><button class="chip" id="eadd">➕ Dodaj przystanek</button></div>
      <div class="fadded" id="eadded"></div>
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
      em.getSource('st').setData({ type: 'FeatureCollection', features: S.map((x, i) => ({ type: 'Feature', geometry: { type: 'Point', coordinates: [pos(i)[1], pos(i)[0]] } }))
        .concat(Object.keys(segs).filter(k => k[0] === 'a').flatMap(k => segs[k]).map(a => ({ type: 'Feature', properties: { add: 1 }, geometry: { type: 'Point', coordinates: [a.q[1], a.q[0]] } }))) });
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
      em.addLayer({ id: 'st', type: 'circle', source: 'st', paint: { 'circle-radius': ['case', ['has', 'add'], 7, 5], 'circle-color': ['case', ['has', 'add'], '#3ddc84', '#fff'], 'circle-stroke-color': '#123b96', 'circle-stroke-width': 2 } });
      em.addLayer({ id: 'wp', type: 'circle', source: 'wp', paint: { 'circle-radius': 5, 'circle-color': '#ffd400', 'circle-stroke-color': '#000', 'circle-stroke-width': 1.5 } });
      mk.forEach(m => m.setLngLat([0, 0]).addTo(em));
      draw(); focus(); listAdded();
    });
    const est = t => { ed.querySelector('#est').textContent = t; };
    try { const D0 = typeof DATA !== 'undefined' ? DATA : null;
      const all = [...new Set(Object.keys((D0 && D0.stops) || {}).concat(Object.keys((D0 && D0.archive) || {})))];
      ed.querySelector('#enames').innerHTML = all.sort((a, b) => a.localeCompare(b, 'pl')).map(x => `<option value="${esc(x)}">`).join(''); } catch (e) {}
    let adding = false;
    const listAdded = () => {
      const a = segs['a' + cur] || [];
      ed.querySelector('#eadded').innerHTML = a.map((x, j) => `<button class="chip" data-del="${j}">✕ ${esc(x.n)}${x.r ? ' N/Ż' : ''}</button>`).join('');
      ed.querySelectorAll('[data-del]').forEach(b => b.onclick = () => {
        a.splice(+b.dataset.del, 1); if (!a.length) delete segs['a' + cur];
        saveMine(ui.fixKey, segs); draw(); listAdded(); est('Usunięto dodany przystanek.');
      });
    };
    ed.querySelector('#eadd').onclick = () => {
      const nm = ed.querySelector('#ename').value.trim();
      if (!nm) { est('Najpierw wpisz nazwę przystanku.'); return; }
      adding = true; est(`Kliknij na mapie miejsce przystanku „${nm}” (między żółtymi przystankami).`);
    };
    em.on('click', e => {
      if (adding) {
        adding = false;
        const nm = ed.querySelector('#ename').value.trim(), r = ed.querySelector('#ereq').checked;
        (segs['a' + cur] = segs['a' + cur] || []).push({ n: nm, q: [+e.lngLat.lat.toFixed(6), +e.lngLat.lng.toFixed(6)], r: r ? 1 : 0 });
        saveMine(ui.fixKey, segs); draw(); listAdded();
        const has = window.recFor && window.recFor(nm, r);
        est(`Dodano „${nm}”.` + (has ? '' : ' Uwaga: nie mam nagrania tego przystanku – w filmiku będzie sam znak bez zapowiedzi.'));
        return;
      }
      wps.push([+e.lngLat.lat.toFixed(6), +e.lngLat.lng.toFixed(6)]); draw(); est(`Punktów na tym odcinku: ${wps.length}. Kliknij „Zapisz odcinek”, gdy skończysz.`); });
    const sel = ed.querySelector('#eseg');
    sel.onchange = () => { cur = +sel.value; adding = false; wps = (segs[cur] || []).slice(); draw(); focus(); listAdded(); est(segs[cur] ? 'Ten odcinek ma już poprawkę – możesz ją zmienić.' : 'Klikaj na mapie punkty trasy między żółtymi przystankami.'); };
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
    if (run) { run.stop = true; run.live = false; if (run.aud) run.aud.sources.forEach(x => { try { x.stop(); } catch (e) {} }); }
    if (!ui) { const b = document.getElementById('film'); if (b) b.remove(); return; }
    cancelAnimationFrame(ui.raf);
    if (ui.map) ui.map.remove();
    ui.md.remove(); ui.box.remove(); ui = null;
  }

  window.Film = { open, close, _ledText: ledText, _drawSign: drawSign, _loadImg: loadImg, _drawLED: drawLED };
})();
