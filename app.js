// node map — a small dataflow canvas for laying out media.
// State is a plain object; it autosaves to localStorage and exports as JSON.
//
// Everything visible is eased: `state` holds targets, `rview`/`rpos` hold the
// rendered values that chase them each frame. Nothing writes layout directly.

// Set by config.js in a published copy; absent when running against serve.py.
// One app either way — a shared build differs only in where media comes from
// and in having no server to write back to.
const CONF = window.NODEMAP || {};
const STATIC = !!CONF.static;                  // no server: nothing to POST to
const MEDIA_BASE = CONF.mediaBase || '';       // e.g. an R2 bucket URL
const BUILD = CONF.v || '';               // cache-buster stamped by the build
const DETAIL_AT = 200;                         // on-screen px before the real file loads

const STORE = 'nodebasedpres.graph';
const NS = 'http://www.w3.org/2000/svg';
const PORT_Y = 16;      // vertical offset of ports, from the node's top edge
const NODE_W = 220;     // notes
const MEDIA_W = 360;    // a frame worth actually looking at; 1:1 goes to native

// A map of a few hundred nodes spreads over tens of thousands of units, so the
// floor has to be low enough to take all of it in at once.
const ZOOM_MIN = 0.02;
const ZOOM_MAX = 2.5;

const EASE_VIEW = 0.20; // how fast the camera catches its target
const EASE_NODE = 0.28; // how fast a node catches the cursor — this is the drag lag
const FRICTION  = 0.92; // pan inertia decay per frame

let state = { nodes: [], edges: [], view: { x: 0, y: 0, k: 1 }, seq: 1 };
let sel = { nodes: new Set(), edges: new Set() };
let drag = null;        // active pointer gesture

let armed = [];         // ports clicked and waiting for a partner: [{id, side}]

const clearSel = () => { sel.nodes.clear(); sel.edges.clear(); };
const pickNode = id => { clearSel(); sel.nodes.add(id); };
const pickEdge = id => { clearSel(); sel.edges.add(id); };

const rview = { x: 0, y: 0, k: 1 };   // rendered camera
const rpos = new Map();               // id -> rendered {x,y}
const els = new Map();                // id -> node element
const vel = { x: 0, y: 0 };           // pan inertia

const canvas = document.getElementById('canvas');
const world = document.getElementById('world');
const wiresSvg = document.getElementById('wires');
const wires = document.getElementById('wires-world');
const status = document.getElementById('status');

/* ---------- model ---------- */

const uid = () => 'n' + (state.seq++);
const node = id => state.nodes.find(n => n.id === id);

function addNode(props) {
  const n = Object.assign({
    id: uid(), x: 0, y: 0, w: NODE_W,
    title: 'untitled', kind: 'note', src: '', text: '',
    nw: 0, nh: 0, fps: 0,          // intrinsic dimensions and measured frame rate
  }, props);
  state.nodes.push(n);
  render();
  return n;
}

// Does this edge hang off `id` on the given side? 'out' is what leaves the
// node, 'in' is what arrives, 'both' is everything touching it.
function attaches(e, id, side) {
  if (side === 'out') return e.from === id;
  if (side === 'in') return e.to === id;
  return e.from === id || e.to === id;
}

function addEdge(from, to) {
  if (from === to) return;
  if (state.edges.some(e => e.from === from && e.to === to)) return;
  state.edges.push({ id: uid(), from, to });
  render();
}

function removeSel() {
  if (!sel.nodes.size && !sel.edges.size) return;
  armed = armed.filter(p => !sel.nodes.has(p.id));   // drop ports going away with their node
  state.nodes = state.nodes.filter(n => !sel.nodes.has(n.id));
  state.edges = state.edges.filter(e =>
    !sel.edges.has(e.id) && !sel.nodes.has(e.from) && !sel.nodes.has(e.to));
  clearSel();
  render();
}

/* ---------- media ---------- */

// Images split in two: what a browser decodes itself, and what only opens
// because serve.py renders a PNG proxy for it. Both are 'image' here — the
// difference is which file the <img> actually points at.
const NATIVE_IMAGES = [
  'png', 'apng', 'jpg', 'jpeg', 'jfif', 'pjpeg', 'pjp',
  'gif', 'webp', 'avif', 'svg', 'bmp', 'ico', 'cur',
];

const PROXY_IMAGES = [
  'psd', 'psb', 'tif', 'tiff', 'heic', 'heif', 'heics', 'avci',
  'exr', 'tga', 'jp2', 'jxl', 'dds', 'icns', 'pict', 'pic', 'sgi',
  'pbm', 'ppm', 'pgm', 'astc', 'ktx', 'pvr', 'mpo', 'dcm', 'axr',
  'dng', 'cr2', 'cr3', 'crw', 'nef', 'nefx', 'nrw', 'arw', 'sr2', 'srf',
  'orf', 'rw2', 'raf', 'raw', 'rwl', 'srw', 'pef', '3fr', 'fff', 'erf',
  'dcr', 'mos', 'mrw', 'iiq', 'dxo', 'x3f',
];

const KINDS = {
  image: [...NATIVE_IMAGES, ...PROXY_IMAGES],
  video: ['mp4', 'webm', 'mov', 'm4v', 'ogv', 'mkv', 'avi', 'mpg', 'mpeg', 'mts', 'm2ts'],
  audio: ['mp3', 'wav', 'aac', 'ogg', 'oga', 'm4a', 'flac', 'opus', 'aiff', 'aif', 'caf'],
};

function kindOf(name) {
  const ext = name.split('.').pop().toLowerCase();
  for (const [kind, exts] of Object.entries(KINDS)) if (exts.includes(ext)) return kind;
  return 'file';
}

// Spaces, #, ? and friends are all legal in filenames and all break a raw URL.
const urlFor = p => /^https?:\/\//.test(p)
  ? p                                   // already absolute (a big file off-site)
  : MEDIA_BASE + p.split('/').map(encodeURIComponent).join('/');

function noteEl(msg) {
  const d = document.createElement('div');
  d.className = 'missing';
  d.textContent = msg;
  return d;
}

// A media element reports the same code 4 whether the file was unreachable,
// missing, or genuinely undecodable. Ask the network which it was, so the node
// says something true instead of blaming the codec for a failed download.
const trouble = { reached: 0, blocked: 0, http: 0, codec: 0, first: '' };

function diagnose(url, show) {
  // fetch() is blocked by CORS on hosts that send no headers, so a fetch
  // failure would prove nothing. An <img> is exempt: if it can pull the bytes,
  // the file is reachable and the problem is the codec; if not, it's the host.
  const probe = new Image();
  probe.onload = probe.onerror = () => { /* settled below */ };
  const done = reachable => {
    if (reachable) {
      trouble.codec++;
      trouble.first = trouble.first || (url + ' — reachable, would not decode');
      show("browser can't decode this file");
    } else {
      trouble.blocked++;
      trouble.first = trouble.first || (url + ' — could not be fetched');
      show('could not load — check the connection');
    }
    report();
  };
  probe.onload = () => done(true);
  probe.onerror = () => done(false);
  probe.src = url + (url.includes('?') ? '&' : '?') + 'probe=' + Date.now();
}

let reportTimer;
function report() {
  clearTimeout(reportTimer);
  reportTimer = setTimeout(() => {
    const bits = [];
    if (trouble.blocked) bits.push(`${trouble.blocked} unreachable`);
    if (trouble.http) bits.push(`${trouble.http} HTTP errors`);
    if (trouble.codec) bits.push(`${trouble.codec} undecodable`);
    if (bits.length) {
      flash('media trouble: ' + bits.join(', ') + ' · ' + trouble.first);
      console.warn('[node map] media trouble', trouble);
    }
  }, 1500);
}

// Common capture/delivery rates. A measured rate within 2% of one of these is
// that rate — the difference is sampling noise, not a real cadence.
const RATES = [23.976, 24, 25, 29.97, 30, 48, 50, 59.94, 60, 90, 120, 240];

const needsProxy = src => PROXY_IMAGES.includes((src || '').split('.').pop().toLowerCase());

// Where serve.py puts a proxy. Knowing the convention means a proxy already on
// disk still displays even if the server never mentioned it.
const proxyPathFor = src => 'media/.previews/' + src.replace(/^media\//, '') + '.png';

// Nearest, not first-within-tolerance: 59.94 and 60 are both candidates for a
// measurement near 60, and only the closer one is the right answer.
function snapRate(v) {
  let best = 0, err = Infinity;
  for (const r of RATES) {
    const e = Math.abs(v - r) / r;
    if (e < err) { err = e; best = r; }
  }
  return err < 0.02 ? best : Math.round(v * 100) / 100;
}

// A media element that reports its own failure. Every path here can fail —
// the file may never have been copied, or be a codec the browser won't decode —
// so nothing is allowed to fail silently.
function mediaEl(n, foot) {
  const wrap = document.createElement('div');
  const fail = why => wrap.replaceChildren(noteEl(why));

  if (n.status === 'copying') return wrap.appendChild(noteEl('copying…')), wrap;
  if (n.status === 'missing') return wrap.appendChild(noteEl('not in media/ — re-drop ' + n.title)), wrap;
  if (n.status === 'converting') {
    return wrap.appendChild(noteEl('converting for playback…')), wrap;
  }
  if (n.status === 'convert_failed') {
    return wrap.appendChild(noteEl("couldn't convert this file — see the server log")), wrap;
  }
  if (!n.src) return wrap.appendChild(noteEl('no file')), wrap;

  // Reserving the true aspect ratio up front means the frame is never letterboxed
  // or reflowed on load. Known from a previous session, or set on metadata.
  if (n.sw && n.sh) { n.nw = n.sw; n.nh = n.sh; }
  const shape = () => { if (n.nw && n.nh) wrap.style.aspectRatio = `${n.nw} / ${n.nh}`; };
  shape();

  // Too small on screen to resolve any detail: show the poster instead. A map
  // at 4% zoom would otherwise fetch every full-size file to paint 14px of it.
  if (n.poster && !wantsFull(n)) {
    const el = new Image();
    el.decoding = 'async';
    el.onerror = () => diagnose(el.src, fail);
    el.src = urlFor(n.poster);
    wrap.appendChild(el);
    return wrap;
  }

  if (n.kind === 'image') {
    const el = new Image();
    el.decoding = 'sync';
    el.onerror = () => diagnose(el.src, fail);
    el.onload = () => {
      // For a proxied format the server reports the original's dimensions;
      // the proxy's own size would be a smaller, misleading number.
      if (!n.sw) { n.nw = el.naturalWidth; n.nh = el.naturalHeight; }
      shape();
      writeSpec(n, foot);
      save();
    };
    // Pointing an <img> at a TIFF or PSD can only ever fail, so fall back to
    // the conventional proxy path rather than a file the browser can't decode.
    el.src = urlFor(n.preview || (needsProxy(n.src) ? proxyPathFor(n.src) : n.src));
    wrap.appendChild(el);
  } else if (n.kind === 'video' || n.kind === 'audio') {
    const el = document.createElement(n.kind);
    el.controls = true;
    el.playsInline = true;
    if (n.poster && n.kind === 'video') el.poster = urlFor(n.poster);
    // Metadata only. Source files here run to hundreds of MB; preloading them
    // whole would exhaust memory across several nodes and cost frames rather
    // than save them. Smooth playback comes from serve.py's range support,
    // which lets the browser buffer just ahead of the playhead.
    el.preload = 'metadata';
    el.onerror = () => diagnose(el.currentSrc || el.src, fail);
    el.onloadedmetadata = () => {
      if (n.kind === 'video') {
        n.nw = el.videoWidth;
        n.nh = el.videoHeight;
        shape();
      }
      writeSpec(n, foot);
      save();
    };
    if (n.kind === 'video') measureRate(el, n, foot);
    // ProRes and friends can't be decoded by any browser; play the proxy when
    // one exists, while the node still points at the original file.
    el.src = urlFor(n.preview || n.src);
    wrap.appendChild(el);
  } else {
    wrap.appendChild(noteEl(n.src));
  }
  return wrap;
}

// What the node is actually showing, versus what the file actually is. If those
// two disagree the readout says so — that's the whole point of it.
function writeSpec(n, foot) {
  if (!foot) return;
  const spec = foot.querySelector('.spec');
  if (!spec) return;

  const bits = [];
  if (n.nw && n.nh) bits.push(`${n.nw}×${n.nh}`);
  if (n.fps) bits.push(`${n.fps} fps`);
  if (n.drops) bits.push('dropping frames');
  if (n.preview) bits.push('proxy');   // you're seeing a render, not the file

  // device pixels the frame currently occupies, against the source's own pixels
  if (n.nw) {
    const shown = n.w * rview.k * devicePixelRatio;
    const pct = shown / n.nw;
    if (pct < 0.995) bits.push(`at ${Math.round(pct * 100)}%`);
    else if (pct > 1.005) bits.push(`upscaled ${Math.round(pct * 100)}%`);
    else bits.push('1:1');
  }

  spec.textContent = bits.join(' · ');
  spec.classList.toggle('warn', !!n.drops);
}

// Measures the rate frames are actually presented at, from the video's own
// frame callbacks — not the container's claim, and not a guess.
function measureRate(el, n, foot) {
  if (!('requestVideoFrameCallback' in el)) return;

  let prev = null;
  const samples = [];

  const step = (now, meta) => {
    if (prev) {
      const dt = meta.mediaTime - prev.mediaTime;
      const df = meta.presentedFrames - prev.presentedFrames;
      if (dt > 0 && df > 0) samples.push(df / dt);
    }
    prev = meta;

    if (samples.length >= 12) {
      samples.sort((a, b) => a - b);
      n.fps = snapRate(samples[samples.length >> 1]);

      const q = el.getVideoPlaybackQuality ? el.getVideoPlaybackQuality() : null;
      n.drops = !!(q && q.totalVideoFrames && q.droppedVideoFrames / q.totalVideoFrames > 0.01);

      writeSpec(n, foot);
      save();
      samples.length = 0;
      prev = null;
    }
    el.requestVideoFrameCallback(step);   // keep watching; drops can start later
  };

  el.requestVideoFrameCallback(step);
}

/* ---------- render ---------- */

// Reconciles the DOM against state. Cheap and safe to call on any structural
// change — existing nodes keep their elements, so video keeps playing.
function render() {
  const seen = new Set();

  for (const n of state.nodes) {
    seen.add(n.id);
    let el = els.get(n.id);
    if (!el) {
      el = nodeEl(n);
      els.set(n.id, el);
      rpos.set(n.id, { x: n.x, y: n.y, w: n.w });
      place(n.id);
      world.appendChild(el);
    }
    el.classList.toggle('sel', sel.nodes.has(n.id));
  }

  for (const [id, el] of els) {
    if (seen.has(id)) continue;
    el.remove();
    els.delete(id);
    rpos.delete(id);
  }

  drawWires();
  paintPorts();       // the armed port outlives element rebuilds
  kick();
  save();
}

function nodeEl(n) {
  const el = document.createElement('div');
  el.className = n.kind === 'note' ? 'node note' : 'node';
  el.dataset.id = n.id;

  el.innerHTML = `
    <div class="head">
      <span class="kind"></span>
      <span class="title"></span>
    </div>
    <div class="body"></div>
    <div class="port in"></div>
    <div class="port out"></div>
    <div class="grip" title="drag to resize"></div>`;

  // filenames are user data — set as text, never parsed as markup
  el.querySelector('.kind').textContent = n.kind;
  const titleEl = el.querySelector('.title');
  titleEl.textContent = n.title;
  titleEl.title = n.title + '  (hold ⌥ to select this text, double-click to rename)';

  const body = el.querySelector('.body');
  if (n.kind === 'note') {
    const t = document.createElement('div');
    t.className = 'text';
    t.contentEditable = 'plaintext-only';
    t.textContent = n.text || '';
    t.addEventListener('blur', () => { n.text = t.textContent; save(); });
    body.appendChild(t);
  } else {
    const foot = document.createElement('div');
    foot.className = 'foot';
    foot.innerHTML = `<span class="spec"></span><button class="native" title="show at source resolution">1:1</button>`;
    foot.querySelector('.native').addEventListener('click', () => nativeSize(n));
    body.appendChild(mediaEl(n, foot));
    body.appendChild(foot);
    writeSpec(n, foot);
  }

  el.querySelector('.title').addEventListener('dblclick', e => {
    const t = e.currentTarget;
    t.contentEditable = 'plaintext-only';
    t.focus();
    document.execCommand('selectAll');
    t.onblur = () => { t.contentEditable = 'false'; n.title = t.textContent.trim() || 'untitled'; save(); };
  });

  return el;
}

// Rebuild one node's element in place, keeping its rendered position.
function refresh(id) {
  const n = node(id);
  const old = els.get(id);
  if (!n || !old) return;
  const el = nodeEl(n);
  el.classList.toggle('sel', sel.nodes.has(id));
  els.set(id, el);
  old.replaceWith(el);
  place(id);
  save();
}

function place(id) {
  const r = rpos.get(id);
  const el = els.get(id);
  el.style.transform = `translate(${r.x}px, ${r.y}px)`;
  el.style.width = r.w + 'px';
  // An image grows with the node it sits in; a note's text should too. This
  // rides the rendered width, so it scales through the glide rather than
  // snapping at the end.
  el.style.setProperty('--scale', r.w / NODE_W);
}

function portPos(id, side) {
  const r = rpos.get(id);
  return { x: r.x + (side === 'out' ? r.w : 0), y: r.y + PORT_Y };
}

// Size the node so one source pixel lands on one device pixel — the sharpest
// the file can be shown, given this display and the current zoom.
function nativeSize(n) {
  if (!n.nw) return;
  n.w = Math.round(clamp(n.nw / (rview.k * devicePixelRatio), 120, 4000));
  kick();
  save();
}

const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));

function pathD(a, b) {
  const dx = Math.max(40, Math.abs(b.x - a.x) * 0.5);
  return `M ${a.x} ${a.y} C ${a.x + dx} ${a.y}, ${b.x - dx} ${b.y}, ${b.x} ${b.y}`;
}

// Paths are pooled and rewritten in place — this runs every animated frame.
function drawWires() {
  const specs = [];
  const lifted = drag && drag.mode === 'rewire' ? drag.edges : null;

  for (const e of state.edges) {
    if (!rpos.has(e.from) || !rpos.has(e.to)) continue;
    if (lifted && lifted.has(e.id)) continue;      // drawn from the cursor instead
    specs.push({
      id: e.id,
      cls: sel.edges.has(e.id) ? 'sel' : '',
      d: pathD(portPos(e.from, 'out'), portPos(e.to, 'in')),
    });
  }

  if (drag && drag.mode === 'wire') {
    specs.push({ id: '', cls: 'temp', d: pathD(portPos(drag.from, 'out'), drag.cursor) });
  }

  // The grabbed bundle: each wire keeps the end that isn't moving and follows
  // the cursor with the end that is.
  if (lifted) {
    for (const e of state.edges) {
      if (!lifted.has(e.id)) continue;
      if (e.from === drag.node && rpos.has(e.to)) {
        specs.push({ id: '', cls: 'temp', d: pathD(drag.cursor, portPos(e.to, 'in')) });
      } else if (e.to === drag.node && rpos.has(e.from)) {
        specs.push({ id: '', cls: 'temp', d: pathD(portPos(e.from, 'out'), drag.cursor) });
      }
    }
  }

  while (wires.childElementCount < specs.length) wires.appendChild(document.createElementNS(NS, 'path'));
  while (wires.childElementCount > specs.length) wires.lastElementChild.remove();

  specs.forEach((s, i) => {
    const p = wires.children[i];
    p.dataset.id = s.id;
    p.setAttribute('class', s.cls);
    p.setAttribute('d', s.d);
  });
}

function applyView() {
  world.style.transform = `translate(${rview.x}px, ${rview.y}px) scale(${rview.k})`;
  wires.setAttribute('transform', `translate(${rview.x} ${rview.y}) scale(${rview.k})`);
  // The grid travels with the camera, so movement reads as movement. Zoomed
  // far out a 24-unit spacing collapses into moiré, so it steps up in octaves
  // and keeps roughly the same spacing on screen at any zoom.
  let g = 24 * rview.k;
  while (g < 14) g *= 4;
  canvas.style.backgroundSize = `${g}px ${g}px`;
  canvas.style.backgroundPosition = `${rview.x}px ${rview.y}px`;

  // Sub-pixel text is noise that still costs a layout — drop the chrome when
  // the nodes are too small to read anyway.
  document.body.classList.toggle('far', rview.k < 0.22);

}

/* ---------- the glide ---------- */

// Moves `obj[key]` a fraction of the way toward `target[key]`, snapping once
// the gap is imperceptible. Returns true while still moving.
function ease(obj, target, key, rate, eps) {
  const d = target[key] - obj[key];
  if (Math.abs(d) < eps) {
    if (obj[key] === target[key]) return false;
    obj[key] = target[key];
    return true;
  }
  obj[key] += d * rate;
  return true;
}

// The loop sleeps when nothing is moving. An always-scheduled rAF competes with
// video presentation for the main thread; idling gives the frames back.
let running = false;

function kick() {
  if (running) return;
  running = true;
  requestAnimationFrame(tick);
}

function tick() {
  let moving = false;

  if (Math.abs(vel.x) > 0.05 || Math.abs(vel.y) > 0.05) {
    state.view.x += vel.x;
    state.view.y += vel.y;
    vel.x *= FRICTION;
    vel.y *= FRICTION;
    moving = true;
  }

  let cam = false;
  cam = ease(rview, state.view, 'x', EASE_VIEW, 0.05) || cam;
  cam = ease(rview, state.view, 'y', EASE_VIEW, 0.05) || cam;
  cam = ease(rview, state.view, 'k', EASE_VIEW, 0.0002) || cam;
  if (cam) applyView();

  for (const n of state.nodes) {
    const r = rpos.get(n.id);
    if (!r) continue;
    const mx = ease(r, n, 'x', EASE_NODE, 0.05);
    const my = ease(r, n, 'y', EASE_NODE, 0.05);
    const mw = ease(r, n, 'w', EASE_NODE, 0.05);
    const el = els.get(n.id);
    if (mx || my || mw) {
      place(n.id);
      // a resize changes what fraction of the source you're seeing, so the
      // readout has to keep up with it rather than wait for the loop to idle
      if (mw && n.nw) writeSpec(n, el.querySelector('.foot'));
      if (!el.classList.contains('moving')) el.classList.add('moving');
      moving = true;
    } else if (el.classList.contains('moving')) {
      // drop the compositing hint once still, so a parked video isn't stuck in
      // its own layer competing for GPU memory
      el.classList.remove('moving');
    }
  }

  const wiring = !!(drag && (drag.mode === 'wire' || drag.mode === 'rewire'));
  if (moving || cam || wiring) drawWires();

  if (moving || cam || wiring) requestAnimationFrame(tick);
  else { running = false; respec(); syncDetail(); }
}

// How wide this node actually is on screen right now.
const wantsFull = n => {
  const r = rpos.get(n.id);
  return ((r ? r.w : n.w) * rview.k) >= DETAIL_AT;
};

// Swap posters for real media (and back) as the zoom changes. Runs when the
// camera settles, never mid-glide, so it can't stutter a movement.
function syncDetail() {
  for (const n of state.nodes) {
    if (n.kind === 'note' || !n.src || !n.poster) continue;
    const want = wantsFull(n) ? 'full' : 'poster';
    if ((n.detail || '') === want) continue;

    const el = els.get(n.id);
    const playing = el && el.querySelector('video') && !el.querySelector('video').paused;
    if (playing && want === 'poster') continue;      // never interrupt playback

    n.detail = want;
    refresh(n.id);
  }
}

// After a zoom settles, every readout's "at 60%" is stale — recompute them.
function respec() {
  for (const n of state.nodes) {
    if (!n.nw) continue;
    const el = els.get(n.id);
    if (el) writeSpec(n, el.querySelector('.foot'));
  }
}

/* ---------- coordinates ---------- */

// Screen -> world, using the *rendered* camera so the cursor lines up with
// what's actually on screen mid-glide.
function toWorld(ev) {
  return {
    x: (ev.clientX - rview.x) / rview.k,
    y: (ev.clientY - rview.y) / rview.k,
  };
}

/* ---------- interaction ---------- */

canvas.addEventListener('mousedown', ev => {
  const portOut = ev.target.closest('.port.out');
  const grip = ev.target.closest('.grip');
  const head = ev.target.closest('.head');
  const nodeDiv = ev.target.closest('.node');
  const wire = ev.target.closest('#wires path');

  vel.x = vel.y = 0;
  kick();

  // Shift is a mode of its own. Starting on a port or a header takes hold of
  // that node's existing connections; anywhere else draws a selection box.
  // Every gesture below is left exactly as it was.
  // Shift means "add to what's already picked" on a click, and stays the
  // modifier for the box and bundle drags. Which one this is isn't known until
  // the mouse either moves or doesn't, so both are set up and mouseup decides.
  if (ev.shiftKey) {
    ev.preventDefault();
    const port = ev.target.closest('.port');
    const onHead = ev.target.closest('.head');

    if (nodeDiv && (port || onHead)) {
      const id = nodeDiv.dataset.id;
      const side = port ? (port.classList.contains('out') ? 'out' : 'in') : 'both';
      drag = {
        mode: 'rewire', node: id, side, cursor: toWorld(ev),
        edges: new Set(state.edges.filter(e => attaches(e, id, side)).map(e => e.id)),
        ox: ev.clientX, oy: ev.clientY, onPort: !!port,
      };
      drawWires();
      return;
    }

    drag = {
      mode: 'mark', x0: ev.clientX, y0: ev.clientY, x1: ev.clientX, y1: ev.clientY,
      node: nodeDiv ? nodeDiv.dataset.id : null,
    };
    drawMarquee();
    return;
  }

  const anyPort = ev.target.closest('.port');
  if (anyPort) {
    ev.preventDefault();                       // ctrl-click must not open a menu
    const id = nodeDiv.dataset.id;
    const side = anyPort.classList.contains('out') ? 'out' : 'in';

    if (ev.metaKey || ev.ctrlKey) {
      if (armed.length) connectArmed(id, side);
      else flash(`click a port first, then ${HOLD}-click this one`);
      return;
    }

    // An outlet still drags out a wire. Whether this is a drag or a plain
    // click isn't known yet — mouseup decides, and a click arms the port.
    if (side === 'out') {
      drag = { mode: 'wire', from: id, cursor: toWorld(ev), ox: ev.clientX, oy: ev.clientY };
      return;
    }
    setPort(id, side);
    return;
  }

  if (grip) {
    const n = node(nodeDiv.dataset.id);
    pickNode(n.id);
    drag = { mode: 'size', n, px: ev.clientX, w0: n.w };
    render();
  } else if (head && ev.altKey) {
    return;                       // Alt: selecting the name, not moving the node
  } else if (head) {
    const n = node(nodeDiv.dataset.id);
    // dragging one of several selected nodes carries the whole selection
    if (!sel.nodes.has(n.id)) pickNode(n.id);
    const w = toWorld(ev);
    drag = {
      mode: 'node',
      items: state.nodes.filter(m => sel.nodes.has(m.id))
        .map(m => ({ n: m, dx: w.x - m.x, dy: w.y - m.y })),
    };
    for (const it of drag.items) world.appendChild(els.get(it.n.id));   // to front
    render();
  } else if (nodeDiv) {
    pickNode(nodeDiv.dataset.id);
    render();
  } else if (wire) {
    pickEdge(wire.dataset.id);
    render();
  } else {
    clearSel();
    disarm();                       // clicking away abandons a pending connection
    canvas.classList.add('panning');
    drag = { mode: 'pan', px: ev.clientX, py: ev.clientY };
    render();
  }
});

/* ---------- selection box ---------- */

const marquee = document.getElementById('marquee');

function drawMarquee() {
  const { x0, y0, x1, y1 } = drag;
  marquee.style.left = Math.min(x0, x1) + 'px';
  marquee.style.top = Math.min(y0, y1) + 'px';
  marquee.style.width = Math.abs(x1 - x0) + 'px';
  marquee.style.height = Math.abs(y1 - y0) + 'px';
  marquee.hidden = false;
}

// Anything the box touches is selected, the way a desktop marquee behaves —
// not only what falls entirely inside it. Compared in screen space, so it
// stays honest at any zoom.
function toggleNodeSel(id) {
  if (sel.nodes.has(id)) sel.nodes.delete(id);
  else sel.nodes.add(id);
  render();
  flash(sel.nodes.size ? `${sel.nodes.size} selected` : 'selection cleared');
}

function applyMarquee() {
  const x1 = Math.min(drag.x0, drag.x1), x2 = Math.max(drag.x0, drag.x1);
  const y1 = Math.min(drag.y0, drag.y1), y2 = Math.max(drag.y0, drag.y1);
  // additive: Shift means "add to the selection" for the box just as it does
  // for a click, so several boxes can be drawn in turn
  sel.edges.clear();

  for (const n of state.nodes) {
    const el = els.get(n.id);
    if (!el) continue;
    const r = el.getBoundingClientRect();
    if (r.right >= x1 && r.left <= x2 && r.bottom >= y1 && r.top <= y2) sel.nodes.add(n.id);
  }

  marquee.hidden = true;
  render();
  if (sel.nodes.size) flash(`${sel.nodes.size} selected`);
}

/* ---------- click a port, then ⌘-click its partner ---------- */

// Deliberately no wire trailing the cursor while a port is armed. Nothing is
// drawn until a connection actually exists, so the canvas never shows a
// relationship that isn't real yet.
function paintPorts() {
  document.querySelectorAll('.port.armed').forEach(p => p.classList.remove('armed'));
  document.body.classList.toggle('connecting', armed.length > 0);
  for (const p of armed) {
    const el = els.get(p.id);
    if (el) el.querySelector('.port.' + p.side).classList.add('armed');
  }
}

const HOLD = navigator.platform.toLowerCase().includes('mac') ? '⌘' : 'ctrl';

const isArmed = (id, side) => armed.some(p => p.id === id && p.side === side);

function announceArmed() {
  paintPorts();
  if (!armed.length) return;
  if (armed.length === 1) {
    const side = armed[0].side;
    flash(`${side === 'out' ? 'output' : 'input'} selected — ${HOLD}-click `
      + `${side === 'out' ? 'an input' : 'an output'} to connect`);
  } else {
    flash(`${armed.length} ports selected — ${HOLD}-click one to connect them all`);
  }
}

// A plain click starts a fresh selection; shift-click builds one up.
function setPort(id, side) {
  armed = isArmed(id, side) && armed.length === 1 ? [] : [{ id, side }];
  announceArmed();
}

function togglePort(id, side) {
  armed = isArmed(id, side)
    ? armed.filter(p => !(p.id === id && p.side === side))
    : [...armed, { id, side }];
  announceArmed();
}

function disarm() {
  if (!armed.length) return;
  armed = [];
  paintPorts();
}

// Joins every armed port to the one just clicked. Ports facing the same way as
// the target, or belonging to it, can't be joined and are reported rather than
// silently ignored.
function connectArmed(id, side) {
  const list = armed;
  disarm();

  const usable = list.filter(p => p.side !== side && p.id !== id);
  const wrongWay = list.filter(p => p.side === side).length;
  const ownPort = list.filter(p => p.side !== side && p.id === id).length;

  let made = 0, already = 0;
  let lastFrom = null, lastTo = null;

  for (const p of usable) {
    const from = p.side === 'out' ? p.id : id;
    const to = p.side === 'out' ? id : p.id;
    if (state.edges.some(e => e.from === from && e.to === to)) { already++; continue; }
    state.edges.push({ id: uid(), from, to });
    lastFrom = from; lastTo = to;
    made++;
  }

  render();

  const notes = [];
  if (already) notes.push(`${already} already connected`);
  if (wrongWay) notes.push(`${wrongWay} faced the same way`);
  if (ownPort) notes.push(`${ownPort} was its own node`);

  if (!made && !notes.length) return flash('nothing selected to connect');
  const head = made === 1 && lastFrom
    ? `${node(lastFrom).title}  →  ${node(lastTo).title}`
    : `${made} connection${made === 1 ? '' : 's'} made`;
  flash(head + (notes.length ? ' · ' + notes.join(' · ') : ''));
}

/* ---------- moving a bundle of connections ---------- */

// Re-points every wire in the grabbed bundle from its old node to `targetId`,
// keeping each wire's far end exactly where it was. Dropping on nothing, or
// back on the same node, leaves the graph untouched.
function applyRewire(targetId) {
  const src = drag.node;
  if (!targetId || targetId === src || !node(targetId)) {
    drawWires();
    return;
  }

  const lifted = drag.edges;
  const kept = [];
  const seen = new Set();
  let moved = 0, looped = 0, merged = 0;

  for (const e of state.edges) {
    const next = lifted.has(e.id)
      ? { ...e, from: e.from === src ? targetId : e.from, to: e.to === src ? targetId : e.to }
      : e;

    // a wire from a node back to itself isn't a connection
    if (next.from === next.to) { looped++; continue; }

    // two identical wires are one wire — this can also retire an edge that was
    // already there, which is why it's counted and reported
    const key = next.from + '>' + next.to;
    if (seen.has(key)) { merged++; continue; }

    seen.add(key);
    kept.push(next);
    if (lifted.has(e.id)) moved++;
  }

  state.edges = kept;
  render();

  const what = drag.side === 'both' ? 'connection' : drag.side === 'out' ? 'output' : 'input';
  const notes = [];
  if (merged) notes.push(`${merged} merged with an existing wire`);
  if (looped) notes.push(`${looped} would have looped back`);
  flash(`${moved} ${what}${moved === 1 ? '' : 's'} moved to ${node(targetId).title}`
    + (notes.length ? ' · ' + notes.join(' · ') : ''));
}

// Crosshair while Shift is held, so the mode is visible before you commit to it.
const markMode = on => document.body.classList.toggle('marking', on);

const pickText = on => document.body.classList.toggle('picktext', on);
window.addEventListener('keydown', ev => { if (ev.altKey) pickText(true); });
window.addEventListener('keyup', ev => { if (!ev.altKey) pickText(false); });
window.addEventListener('blur', () => pickText(false));

window.addEventListener('keydown', ev => { if (ev.key === 'Shift') markMode(true); });
window.addEventListener('keyup', ev => {
  // letting go of Shift part-way through a gesture shouldn't drop the mode out
  // from under it — the drag is already committed
  if (ev.key === 'Shift' && !(drag && (drag.mode === 'mark' || drag.mode === 'rewire'))) markMode(false);
});
window.addEventListener('blur', () => { if (!drag) markMode(false); });

window.addEventListener('mousemove', ev => {
  if (!drag) return;
  kick();

  if (drag.mode === 'mark') {
    drag.x1 = ev.clientX;
    drag.y1 = ev.clientY;
    drawMarquee();
  } else if (drag.mode === 'rewire') {
    drag.cursor = toWorld(ev);
    document.querySelectorAll('.node.target').forEach(el => el.classList.remove('target'));
    const over = ev.target.closest('.node');
    if (over && over.dataset.id !== drag.node) over.classList.add('target');
    drawWires();
  } else if (drag.mode === 'size') {
    drag.n.w = Math.round(clamp(drag.w0 + (ev.clientX - drag.px) / rview.k, 120, 4000));
  } else if (drag.mode === 'pan') {
    const dx = ev.clientX - drag.px;
    const dy = ev.clientY - drag.py;
    drag.px = ev.clientX;
    drag.py = ev.clientY;
    drag.t = performance.now();
    state.view.x += dx;
    state.view.y += dy;
    vel.x = dx;                          // remembered so release can keep gliding
    vel.y = dy;
  } else if (drag.mode === 'node') {
    const w = toWorld(ev);
    for (const it of drag.items) {
      it.n.x = Math.round(w.x - it.dx);
      it.n.y = Math.round(w.y - it.dy);
    }
  } else if (drag.mode === 'wire') {
    drag.cursor = toWorld(ev);
    document.querySelectorAll('.port.in.hot').forEach(p => p.classList.remove('hot'));
    const hit = ev.target.closest('.port.in');
    if (hit) hit.classList.add('hot');
  }
});

window.addEventListener('mouseup', ev => {
  if (!drag) return;

  const still = Math.abs(ev.clientX - (drag.ox ?? drag.x0 ?? 0)) < 4
    && Math.abs(ev.clientY - (drag.oy ?? drag.y0 ?? 0)) < 4;

  if (drag.mode === 'mark') {
    if (still) {
      // a shift-click that never moved adds or removes the one node under it
      const onNode = drag.node;
      marquee.hidden = true;
      drag = null;
      if (onNode) toggleNodeSel(onNode);
      else render();
    } else {
      applyMarquee();
      drag = null;
    }
    return;
  }

  if (drag.mode === 'rewire') {
    const over = ev.target.closest('.node');
    const g = drag;
    document.querySelectorAll('.node.target').forEach(el => el.classList.remove('target'));

    if (still) {
      drag = null;
      drawWires();
      // shift-click on a port adds it to the connection set; on a header it
      // adds the node to the selection
      if (g.onPort) togglePort(g.node, g.side);
      else toggleNodeSel(g.node);
      return;
    }

    if (!g.edges.size) {
      drag = null;
      drawWires();
      flash(g.side === 'both' ? 'nothing connected to this node'
        : `no ${g.side === 'out' ? 'outgoing' : 'incoming'} connections here`);
      return;
    }

    applyRewire(over ? over.dataset.id : null);
    drag = null;
    return;
  }

  // A press on an outlet that never moved is a click, not a drag — arm it.
  if (drag.mode === 'wire'
      && Math.abs(ev.clientX - drag.ox) < 4 && Math.abs(ev.clientY - drag.oy) < 4) {
    const id = drag.from;
    drag = null;
    canvas.classList.remove('panning');
    setPort(id, 'out');
    drawWires();
    return;
  }

  const wasWire = drag.mode === 'wire';
  const from = drag.from;
  const hit = wasWire ? ev.target.closest('.port.in') : null;

  // a throw only counts if the hand was still moving at release
  if (drag.mode === 'pan' && performance.now() - (drag.t || 0) > 80) { vel.x = 0; vel.y = 0; }
  canvas.classList.remove('panning');
  drag = null;

  document.querySelectorAll('.port.in.hot').forEach(p => p.classList.remove('hot'));
  if (hit) addEdge(from, hit.closest('.node').dataset.id);
  else if (wasWire) drawWires();
  else save();
});

/* ---------- wheel: trackpad pans, mouse wheel zooms ---------- */

let trackpad = false;

// Trackpads emit fine-grained, often fractional, frequently two-axis deltas.
// A wheel emits coarse integer notches on one axis. The guess is sticky so the
// low-value tail of a momentum scroll doesn't get misread.
function looksLikeTrackpad(ev) {
  if (ev.deltaMode !== 0) return false;
  if (ev.deltaX !== 0) return true;
  if (!Number.isInteger(ev.deltaY)) return true;
  return Math.abs(ev.deltaY) < 40;
}

function zoomAt(cx, cy, factor) {
  const k = clamp(state.view.k * factor, ZOOM_MIN, ZOOM_MAX);
  state.view.x = cx - (cx - state.view.x) * (k / state.view.k);
  state.view.y = cy - (cy - state.view.y) * (k / state.view.k);
  state.view.k = k;
  save();
}

canvas.addEventListener('wheel', ev => {
  ev.preventDefault();
  vel.x = vel.y = 0;
  kick();

  // pinch on a trackpad arrives as ctrl+wheel; cmd+scroll is the explicit zoom
  if (ev.ctrlKey || ev.metaKey) {
    zoomAt(ev.clientX, ev.clientY, Math.exp(-ev.deltaY * 0.01));
    return;
  }

  if (looksLikeTrackpad(ev)) trackpad = true;
  else if (Math.abs(ev.deltaY) >= 100) trackpad = false;

  if (trackpad) {
    state.view.x -= ev.deltaX;
    state.view.y -= ev.deltaY;
    save();
  } else {
    zoomAt(ev.clientX, ev.clientY, ev.deltaY < 0 ? 1.1 : 1 / 1.1);
  }
}, { passive: false });

canvas.addEventListener('dblclick', ev => {
  if (ev.target.closest('.node')) return;
  const w = toWorld(ev);
  addNode({ kind: 'note', title: 'note', x: Math.round(w.x), y: Math.round(w.y) });
});

window.addEventListener('keydown', ev => {
  if (document.activeElement.isContentEditable) return;
  if (ev.key === 'Backspace' || ev.key === 'Delete') { ev.preventDefault(); removeSel(); }
  if (ev.key === 'Escape') { disarm(); clearSel(); render(); }
  if (ev.key === 'f' || ev.key === '0') { ev.preventDefault(); fit(); }
});

// ctrl-click on a Mac is a right-click; don't let the menu eat the gesture
window.addEventListener('contextmenu', ev => {
  if (ev.target.closest('.port')) ev.preventDefault();
});

/* ---------- drop ---------- */

canvas.addEventListener('dragover', ev => ev.preventDefault());
canvas.addEventListener('drop', ev => {
  ev.preventDefault();
  const w = toWorld(ev);
  [...ev.dataTransfer.files].forEach((f, i) => {
    take(f, Math.round(w.x + i * 32), Math.round(w.y + i * 32));
  });
});

// A dropped File only exists in memory, so hand it to the server to write into
// media/. The node points at that copy, which is what survives a reload.
async function take(f, x, y) {
  const kind = kindOf(f.name);
  const n = addNode({
    kind, title: f.name, x, y, status: 'copying',
    w: kind === 'audio' || kind === 'file' ? NODE_W : MEDIA_W,
  });

  // Published copy: no server to store it, so hold the file in memory. It
  // works for this visit and is gone on reload — said plainly rather than
  // pretending it saved.
  if (STATIC) {
    n.src = URL.createObjectURL(f);
    n.preview = '';
    n.poster = '';
    n.status = '';
    n.local = true;
    refresh(n.id);
    flash(f.name + ' — added for this session only');
    return;
  }

  try {
    const res = await fetch('/upload', {
      method: 'POST',
      headers: { 'X-Filename': encodeURIComponent(f.name) },
      body: f,
    });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    const out = await res.json();
    n.src = out.src;
    n.preview = out.preview || '';
    n.sw = out.sw || 0;
    n.sh = out.sh || 0;
    n.status = '';
    n.title = out.src.replace(/^media\//, '');
    if (needsProxy(n.src) && !n.preview) {
      flash(n.title + ' — no preview could be rendered for this format');
    }
  } catch (err) {
    n.status = 'missing';
    n.src = 'media/' + f.name;
    flash('could not copy ' + f.name + ' — is serve.py running? (' + err.message + ')');
  }
  refresh(n.id);
}

// Nodes outlive the files they point at. Say so plainly instead of leaving a
// dead player on the canvas.
async function auditMedia() {
  let have;
  try {
    const res = await fetch(STATIC ? 'media-index.json?v=' + BUILD : '/api/media');
    if (!res.ok) throw new Error(res.status);
    const list = await res.json();
    // Older servers answer with bare filenames, newer ones with objects that
    // carry preview info. Read either — a shape mismatch must never be
    // mistaken for the files being gone.
    have = new Map(list.map(e => (typeof e === 'string' ? [e, { name: e }] : [e.name, e])));

    // A server too old to report previews will silently fail to show anything
    // that needs one. Say it out loud rather than let the nodes look broken.
    if (list.length && typeof list[0] === 'string') {
      flash('serve.py is out of date — restart it for previews, backups and disk saves');
    }
  } catch (err) {
    flash('serve.py is not running — media and drops will not work');
    return;
  }

  // If every last file looks missing, the far likelier explanation is that the
  // listing is wrong, not that the whole library vanished. Say so and change
  // nothing.
  const withFiles = state.nodes.filter(n => n.src && n.status !== 'copying');
  const found = withFiles.filter(n => have.has(n.src.replace(/^media\//, '')));
  if (withFiles.length > 1 && found.length === 0) {
    flash(`${withFiles.length} files did not match the server listing — leaving nodes alone. Restart serve.py.`);
    return;
  }

  let converting = 0;

  for (const n of state.nodes) {
    if (!n.src || n.status === 'copying' || n.local) continue;
    // Local builds index by bare filename; published ones by the path the site
    // asks for. Try both rather than assume which shape this is.
    const entry = have.get(n.src) || have.get(n.src.replace(/^media\//, ''));

    let want = '';
    if (!entry) want = 'missing';
    else if (entry.converting) { want = 'converting'; converting++; }
    else if (entry.convert_failed) want = 'convert_failed';

    // a proxy may have been rendered since this node was made, or the source
    // re-rendered at a different size — take the server's word for it
    const preview = (entry && entry.preview) || '';
    const poster = (entry && entry.poster) || '';
    const changed = (n.status || '') !== want
      || (n.preview || '') !== preview
      || (n.poster || '') !== poster
      || (entry && entry.sw && n.sw !== entry.sw);

    if (changed) {
      n.status = want;
      n.preview = preview;
      n.poster = poster;
      if (entry && entry.sw) { n.sw = entry.sw; n.sh = entry.sh; }
      refresh(n.id);
    }
  }

  // Transcoding runs on the server and takes as long as it takes. Keep asking
  // until every one is done, so the nodes light up on their own.
  if (converting) {
    flash(`${converting} file${converting === 1 ? '' : 's'} still converting for playback…`);
    clearTimeout(auditTimer);
    auditTimer = setTimeout(auditMedia, 5000);
  }
}

let auditTimer;

/* ---------- persistence ---------- */

let saveTimer;
let booting = true;     // never persist the seeded demo over real saved work

// `status` is something we worked out about the world a moment ago, not part of
// the map. Persisting it means one bad reading survives reloads; recomputing it
// each load means a wrong answer costs nothing.
function serialize() {
  return JSON.stringify({
    ...state,
    v: BUILD,                       // which published build this copy came from
    nodes: state.nodes.map(({ status, detail, ...keep }) => keep),
  });
}

function save() {
  if (booting) return;
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    const json = serialize();
    localStorage.setItem(STORE, json);
    // A published copy has no server to write to — a visitor's changes live in
    // their own browser and never touch anyone else's view.
    if (STATIC) return;
    fetch('/graph', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: json })
      .catch(() => {});
  }, 400);
}

function load() {
  try {
    const raw = localStorage.getItem(STORE);
    if (raw) {
      const saved = JSON.parse(raw);
      // A published copy that has moved on invalidates whatever a visitor's
      // browser kept: those nodes point at file paths this build no longer
      // uses, and localStorage otherwise wins forever — no refresh can fix it.
      if (STATIC && saved.v !== BUILD) {
        localStorage.removeItem(STORE);
      } else {
        state = Object.assign(state, saved);
      }
    }
  } catch (e) { /* start empty */ }
  migrate();
}

// Anything derivable from the file is recomputed on load rather than trusted
// from storage. `kind` in particular: it comes from the extension, so a node
// saved before a format was recognised would otherwise stay mistyped forever —
// a .tif written as kind 'file' never renders as an image again.
function migrate() {
  for (const n of state.nodes) {
    if (!n.w) n.w = NODE_W;      // graphs saved before widths
    delete n.status;             // clears flags left by an earlier bad audit
    if (n.src) n.kind = kindOf(n.src);
  }
}

// localStorage is per-browser; graph.json is the shared copy. Only consulted
// when this browser has nothing, so a fresh profile recovers instead of
// starting blank and then overwriting the real map.
async function loadFromDisk() {
  try {
    const res = await fetch(STATIC ? 'graph.json?v=' + BUILD : '/graph');
    if (!res.ok) return false;
    const disk = await res.json();
    if (!disk || !disk.nodes || !disk.nodes.length) return false;
    state = Object.assign(state, disk);
    migrate();
    return true;
  } catch (e) {
    return false;
  }
}

function flash(msg) {
  status.textContent = msg;
  setTimeout(() => { if (status.textContent === msg) status.textContent = ''; }, 4000);
}

/* ---------- toolbar ---------- */

document.getElementById('bar').addEventListener('click', ev => {
  const act = ev.target.dataset.act;
  if (act === 'note') {
    addNode({
      kind: 'note',
      title: 'note',
      x: Math.round((-rview.x + innerWidth / 2 - NODE_W / 2) / rview.k),
      y: Math.round((-rview.y + innerHeight / 3) / rview.k),
    });
  } else if (act === 'fit') {
    fit();
  } else if (act === 'export') {
    const blob = new Blob([serialize()], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'graph.json';
    a.click();
  } else if (act === 'import') {
    document.getElementById('importer').click();
  } else if (act === 'backup') {
    runBackup(ev.target);
  }
});

async function runBackup(btn) {
  btn.disabled = true;
  flash('backing up…');
  try {
    const res = await fetch('/backup', { method: 'POST' });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    const s = await res.json();
    flash(`backed up → ${s.dest} · ${s.new} new, ${s.updated} updated, ${s.unchanged} unchanged`
      + (s.archived ? `, ${s.archived} archived` : ''));
  } catch (err) {
    flash('backup failed — ' + err.message);
  }
  btn.disabled = false;
}

document.getElementById('importer').addEventListener('change', async ev => {
  const f = ev.target.files[0];
  if (!f) return;
  state = JSON.parse(await f.text());
  migrate();
  clearSel();
  for (const [id, el] of els) el.remove();
  els.clear();
  rpos.clear();
  render();
  fit();
});

// A node's height comes from its content, so it has to be measured rather than
// assumed — using the width as a stand-in framed the map wrong every time.
function nodeHeight(n) {
  const el = els.get(n.id);
  if (el && el.offsetHeight) return el.offsetHeight;
  return n.kind === 'note' ? 90 : n.w * 0.75;      // best guess before layout
}

function fit(pad = 60) {
  if (!state.nodes.length) return;
  // a hidden or minimised window reports no size; framing against that would
  // throw the camera somewhere useless
  if (innerWidth < 50 || innerHeight < 120) return;

  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const n of state.nodes) {
    minX = Math.min(minX, n.x);
    minY = Math.min(minY, n.y);
    maxX = Math.max(maxX, n.x + n.w);
    maxY = Math.max(maxY, n.y + nodeHeight(n));
  }
  minX -= pad; minY -= pad; maxX += pad; maxY += pad;

  // the toolbar floats over the bottom-left, so don't frame anything under it
  const availH = innerHeight - 64;
  const k = clamp(Math.min(innerWidth / (maxX - minX), availH / (maxY - minY)),
    ZOOM_MIN, 1);

  state.view = {
    k,
    x: -minX * k + (innerWidth - (maxX - minX) * k) / 2,
    y: -minY * k + (availH - (maxY - minY) * k) / 2,
  };
  kick();
  save();
  flash(`${state.nodes.length} nodes · ${Math.round(k * 100)}%`);
}

/* ---------- boot ---------- */

(async function boot() {
  if (STATIC) {
    // nothing here can write to a server, so don't offer to
    const b = document.querySelector('[data-act="backup"]');
    if (b) b.remove();
  }

  load();
  if (!state.nodes.length) await loadFromDisk();

  rview.x = state.view.x;
  rview.y = state.view.y;
  rview.k = state.view.k;
  applyView();

  if (!state.nodes.length) {
    const a = addNode({ kind: 'note', title: 'start', text: 'two-finger scroll to move.\npinch or cmd-scroll to zoom.\ndrop media anywhere.', x: 120, y: 140 });
    const b = addNode({ kind: 'note', title: 'next', text: 'drag the right dot into a left dot to wire.', x: 460, y: 300 });
    addEdge(a.id, b.id);
  }

  render();
  kick();
  booting = false;        // saving is live from here on
  await auditMedia();
})();
