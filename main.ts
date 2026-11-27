// png-squeeze encoder: lossless PNG re-encoder with colour-type reduction,
// per-row adaptive filter search, zlib level 9, and optimal-parse DEFLATE
// (pure JS, zopfli-like) on the screened winner. Written fresh for
// png-squeeze-01-run-20261127. Node 22, built-ins only, deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync, constants as zconst } from 'node:zlib';
import { deflateOptimal } from './optdeflate.ts';

const W = 1280;
const H = 720;

// ---------- CRC-32 (PNG) ----------
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c;
  }
  return t;
})();

function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

const SIG = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHAN = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

function chunkBytes(type, data) {
  const out = new Uint8Array(12 + data.length);
  const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  out.set([type.charCodeAt(0), type.charCodeAt(1), type.charCodeAt(2), type.charCodeAt(3)], 4);
  out.set(data, 8);
  v.setUint32(8 + data.length, crc32(out, 4, 8 + data.length));
  return out;
}

function pngOf(chunks) {
  let size = SIG.length;
  for (const [, d] of chunks) size += 12 + d.length;
  const out = new Uint8Array(size);
  out.set(SIG, 0);
  let at = SIG.length;
  for (const [type, data] of chunks) {
    out.set(chunkBytes(type, data), at);
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ---------- PNG decode to RGBA ----------
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

function decodePng(bytes) {
  if (bytes.length < 8 || SIG.some((b, i) => bytes[i] !== b)) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(type + ' CRC fail');
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], interlace: data[12] };
      if (header.depth !== 8 || header.interlace !== 0) throw new Error('unsupported IHDR');
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') ended = true;
    else throw new Error('unsupported chunk ' + type);
  }
  if (!header || !ended || idat.length === 0) throw new Error('incomplete PNG');
  const { width, height, colourType } = header;
  const bpp = CHAN[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('bad inflate length');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else if (ft === 4) {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    } else throw new Error('bad filter ' + ft);
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = palette[e * 3]; rgba[d + 1] = palette[e * 3 + 1]; rgba[d + 2] = palette[e * 3 + 2];
      rgba[d + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
  }
  return { rgba, width, height };
}

// ---------- Image analysis ----------
function analyse(rgba) {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const r = rgba[d], g = rgba[d + 1], b = rgba[d + 2], a = rgba[d + 3];
    if (a !== 255) opaque = false;
    if (r !== g || r !== b) grey = false;
    if (!many) {
      const key = ((r << 24) | (g << 16) | (b << 8) | a) >>> 0;
      const k = counts.get(key);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(key, 1);
      } else counts.set(key, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [];
    for (const [key, count] of counts) {
      colours.push({ r: (key >>> 24) & 255, g: (key >>> 16) & 255, b: (key >>> 8) & 255, a: key & 255, word: key, count });
    }
  }
  return { opaque, grey, colours };
}

// Single fully-transparent value usable as a tRNS key (type 0/2): every
// non-opaque pixel is that exact value at alpha 0, no opaque pixel shares it.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.r + 587 * c.g + 114 * c.b;
  const entries = [...colours].sort((x, y) => {
    const ta = x.a === 255 ? 1 : 0;
    const tb = y.a === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r; plte[i * 3 + 1] = c.g; plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    indices[i] = index.get(((rgba[d] << 24) | (rgba[d + 1] << 16) | (rgba[d + 2] << 8) | rgba[d + 3]) >>> 0);
  }
  return { plte, trns, indices };
}

// ---------- Filters ----------
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
    return;
  }
  if (type === 2) {
    if (prev === null) { out.set(cur); return; }
    for (let i = 0; i < n; i++) out[i] = cur[i] - prev[i];
    return;
  }
  if (type === 3) {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      out[i] = cur[i] - ((a + b) >> 1);
    }
    return;
  }
  for (let i = 0; i < n; i++) {
    const a = i >= bpp ? cur[i - bpp] : 0;
    const b = prev === null ? 0 : prev[i];
    const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
    out[i] = cur[i] - paeth(a, b, c);
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}

const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

// Fill `raw` (height rows of stride+1) with one filter choice per row:
// a fixed type 0..4, 'minsum' (least signed-sum), 'pairs' (fewest distinct
// byte pairs) or 'brute' (each filter actually deflated after the previous
// 32 KiB, smallest kept). Lower type wins ties.
function filtered(samples, width, height, bpp, choice, raw) {
  if (choice === 'block8') return filteredBlock(samples, width, height, bpp, raw);
  const stride = width * bpp;
  const trial = [];
  for (let t = 0; t < 5; t++) {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    trial.push(row);
  }
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else {
        cost = deflateSync(trial[t], before.length === 0
          ? { level: BRUTE_LEVEL, memLevel: 9 }
          : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      }
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// Block-brute: choose one filter per block of 8 rows, scoring each candidate
// block by a real level-9 deflate with the preceding 32 KiB as dictionary.
// Sits between per-row brute (cheap proxy) and whole-stream cost.
const BLOCK_ROWS = 8;
function filteredBlock(samples, width, height, bpp, raw) {
  const stride = width * bpp;
  const cands = [];
  for (let t = 0; t < 5; t++) cands.push(new Uint8Array(BLOCK_ROWS * (stride + 1)));
  for (let y0 = 0; y0 < height; y0 += BLOCK_ROWS) {
    const rows = Math.min(BLOCK_ROWS, height - y0);
    let bestT = 0;
    let bestLen = Infinity;
    for (let t = 0; t < 5; t++) {
      const buf = cands[t];
      for (let k = 0; k < rows; k++) {
        const y = y0 + k;
        const cur = samples.subarray(y * stride, (y + 1) * stride);
        const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
        buf[k * (stride + 1)] = t;
        filterRow(t, cur, prev, bpp, buf.subarray(k * (stride + 1) + 1, (k + 1) * (stride + 1)));
      }
      const at = y0 * (stride + 1);
      const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
      const len = deflateSync(buf.subarray(0, rows * (stride + 1)), before.length === 0
        ? { level: 9, memLevel: 9 }
        : { level: 9, memLevel: 9, dictionary: before }).length;
      if (len < bestLen) { bestLen = len; bestT = t; }
    }
    raw.set(cands[bestT].subarray(0, rows * (stride + 1)), y0 * (stride + 1));
  }
  return raw;
}

// ---------- Forms + screen ----------
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const order of ['count', 'luminance']) {
      const p = paletteForm(rgba, colours, order);
      forms.push({
        colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns,
        filters: [0, 'minsum', 'brute', 'block8'],
      });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({
    colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns,
    filters: [0, 1, 2, 3, 4, 'minsum', 'pairs', 'brute', 'block8'],
  });
  return forms;
}

const SCREEN = { level: 6, memLevel: 8, strategy: zconst.Z_DEFAULT_STRATEGY };
const chunkOverhead = (form) =>
  (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

function screen(rgba, width, height) {
  // Best two candidates per form by level-6 bytes; the caller re-ranks them
  // at level 9, since the level-6 and level-9 orderings can differ.
  const perForm = [];
  let spare = null;
  for (const form of formsOf(rgba)) {
    const size = height * (width * form.bpp + 1);
    const chunks = chunkOverhead(form);
    const kept = [];
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice,
        spare !== null && spare.length === size ? spare : new Uint8Array(size));
      spare = null;
      const zlib = deflateSync(data, SCREEN);
      const bytes = zlib.length + chunks;
      const cand = { form, data, bytes };
      if (kept.length < 2) {
        kept.push(cand);
        kept.sort((a, b) => a.bytes - b.bytes);
      } else if (bytes < kept[1].bytes) {
        spare = kept[1].data;
        kept[1] = cand;
        kept.sort((a, b) => a.bytes - b.bytes);
      } else spare = data;
    }
    perForm.push(...kept);
  }
  return perForm;
}

function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// Final compression of the screened winner: zlib level 9 (default strategy)
// as the fallback, then optimal-parse DEFLATE on the same filtered data;
// keep the smaller stream. Deterministic: no clock, no randomness; the
// chain budget depends only on the input size.
function encode(rgba, width, height, id) {
  const cands = screen(rgba, width, height);
  let best = null;
  for (const { form, data } of cands) {
    const s = deflateSync(data, { level: 9, memLevel: 9, strategy: zconst.Z_DEFAULT_STRATEGY });
    const total = s.length + chunkOverhead(form);
    if (best === null || total < best.total) best = { form, data, stream: s, total };
  }
  // Optimal-parse DEFLATE, 256 KiB blocks. Chain budget by input size: the
  // small instances are cheap to search deeply; the large ones get a shorter
  // chain so the whole set stays inside the 60 s budget.
  const chain = best.data.length <= 1048576 ? 1024 : 128;
  const opt = deflateOptimal(best.data, 262144, chain);
  let stream = best.stream;
  if (opt.length + chunkOverhead(best.form) < best.total) stream = opt;
  return pngOfForm(width, height, best.form, new Uint8Array(stream));
}

// ---------- Main ----------
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const { rgba, width, height } = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  if (width !== W || height !== H) throw new Error(id + ': unexpected size ' + width + 'x' + height);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), encode(rgba, width, height, id));
}
