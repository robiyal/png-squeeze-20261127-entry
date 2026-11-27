// optdeflate.ts — pure-JavaScript optimal-parse DEFLATE (zopfli-style) for
// lossless PNG recompression. No imports, no Node modules, no clock, no
// randomness: fully deterministic. Written fresh for png-squeeze-01-run-20261127.
//
// Pipeline: hash-chain LZ77 (longest match + longest near match per
// position) -> shortest-path DP over length-code boundaries (two cost-model
// iterations: fixed Huffman, then dynamic) -> dynamic-Huffman DEFLATE block(s)
// with zlib wrapper. Matches never cross block boundaries.

const MAX_MATCH = 258;
const MIN_MATCH = 3;
const WINDOW = 32768;
const CHAIN = 1024;
const NICE_LEN = 128;
const NEAR_DIST = 4096;
const NEAR2_DIST = 256;

const LEN_BASE = [
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258,
];
const LEN_EXTRA = [
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
const DIST_BASE = [
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
  8193, 12289, 16385, 24577,
];
const DIST_EXTRA = [
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13,
];

// CODE_MAX_LEN[c]: longest length encoded by length code c. Length 258 is
// its own code (285): code 284 covers 227..257 only, even though its 5
// extra bits could express 258.
const CODE_MAX_LEN = new Uint16Array(29);
for (let c = 0; c < 29; c++) {
  CODE_MAX_LEN[c] = c < 28 ? LEN_BASE[c + 1] - 1 : 258;
}
// LEN_CODE[L] for L in 3..258; DIST_CODE[d] for d in 1..32768.
const LEN_CODE = new Uint8Array(259);
for (let l = 3; l <= 258; l++) {
  for (let c = 0; c < 29; c++) {
    if (l >= LEN_BASE[c] && l <= CODE_MAX_LEN[c]) { LEN_CODE[l] = c; break; }
  }
}
const DIST_CODE = new Uint8Array(32769);
for (let d = 1; d <= 32768; d++) {
  for (let c = 0; c < 30; c++) {
    const mx = DIST_BASE[c] + (DIST_EXTRA[c] === 0 ? 0 : (1 << DIST_EXTRA[c]) - 1);
    if (d >= DIST_BASE[c] && d <= mx) { DIST_CODE[d] = c; break; }
  }
}
// CAND[len]: candidate (code, length) pairs for the DP. Within one length
// code only the longest length matters: same bit cost, further reach dominates.
const CAND = new Array(259);
for (let l = 3; l <= 258; l++) {
  const list = [];
  for (let c = 0; c < 29; c++) {
    if (LEN_BASE[c] > l) break;
    let L = CODE_MAX_LEN[c];
    if (L > l) L = l;
    list.push(c, L);
  }
  CAND[l] = list;
}

function adler32(buf) {
  let a = 1;
  let b = 0;
  const n = buf.length;
  let i = 0;
  while (i < n) {
    const lim = Math.min(i + 5552, n);
    for (; i < lim; i++) {
      a += buf[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// Bit writer, LSB-first, writing straight into a pre-sized buffer.
class BitWriter {
  constructor(out) {
    this.out = out;
    this.pos = 0;
    this.buf = 0;
    this.bits = 0;
  }
  writeBits(value, count) {
    this.buf |= (value << this.bits) >>> 0;
    this.bits += count;
    while (this.bits >= 8) {
      if (this.pos >= this.out.length) this.grow();
      this.out[this.pos++] = this.buf & 0xff;
      this.buf >>>= 8;
      this.bits -= 8;
    }
  }
  grow() {
    const bigger = new Uint8Array(this.out.length * 2);
    bigger.set(this.out);
    this.out = bigger;
  }
  flush() {
    if (this.bits > 0) {
      if (this.pos >= this.out.length) this.grow();
      this.out[this.pos++] = this.buf & 0xff;
      this.buf = 0;
      this.bits = 0;
    }
  }
}

// Canonical Huffman codes from code lengths (RFC 1951 section 3.2.2).
// Codes are returned bit-REVERSED: DEFLATE packs a Huffman code starting
// with its most-significant bit, while writeBits packs LSB-first, so the
// reversed value written LSB-first emits the code MSB-first.
function reverseBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) {
    r = (r << 1) | (code & 1);
    code >>>= 1;
  }
  return r;
}
function canonicalCodes(lengths) {
  let maxLen = 0;
  for (let i = 0; i < lengths.length; i++) if (lengths[i] > maxLen) maxLen = lengths[i];
  const blCount = new Uint32Array(maxLen + 1);
  for (let i = 0; i < lengths.length; i++) if (lengths[i]) blCount[lengths[i]]++;
  const nextCode = new Uint32Array(maxLen + 1);
  let code = 0;
  for (let b = 1; b <= maxLen; b++) {
    code = (code + blCount[b - 1]) << 1;
    nextCode[b] = code;
  }
  const codes = new Uint32Array(lengths.length);
  for (let i = 0; i < lengths.length; i++) {
    const len = lengths[i];
    if (len) {
      codes[i] = reverseBits(nextCode[len], len);
      nextCode[len]++;
    }
  }
  return codes;
}

// Length-limited Huffman code lengths, zlib gen_bitlen style: build the
// optimal tree, then fix any overflow past maxBits by moving leaves down,
// then reassign lengths so the most frequent symbols stay shortest.
function codeLengths(freqs, maxBits) {
  const n = freqs.length;
  const lengths = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freqs[i] > 0) syms.push(i);
  const m = syms.length;
  if (m === 0) return lengths;
  if (m === 1) { lengths[syms[0]] = 1; ensureTwo(lengths); return lengths; }
  // Sort used symbols by frequency ascending for the two-queue tree build.
  syms.sort((a, b) => (freqs[a] - freqs[b]) || (a - b));
  // Nodes: leaves 0..m-1 map to syms[], internal nodes m..2m-2.
  const total = 2 * m - 1;
  const freq = new Float64Array(total);
  const parent = new Int32Array(total).fill(-1);
  for (let i = 0; i < m; i++) freq[i] = freqs[syms[i]];
  const q2 = new Int32Array(m);
  let q1i = 0;
  let q2i = 0;
  let q2n = 0;
  let next = m;
  const takeMin = () => {
    if (q2i >= q2n) return q1i++;
    if (q1i >= m) return q2[q2i++];
    return freq[q1i] <= freq[q2[q2i]] ? q1i++ : q2[q2i++];
  };
  for (let k = 0; k < m - 1; k++) {
    const a = takeMin();
    const b = takeMin();
    const node = next++;
    freq[node] = freq[a] + freq[b];
    parent[a] = node;
    parent[b] = node;
    q2[q2n++] = node;
  }
  const blCount = new Uint32Array(300);
  for (let i = 0; i < m; i++) {
    let d = 0;
    let node = i;
    while (parent[node] !== -1) { d++; node = parent[node]; }
    blCount[d]++;
  }
  let overflow = 0;
  for (let d = maxBits + 1; d < 300; d++) overflow += blCount[d];
  while (overflow > 0) {
    let bits = maxBits - 1;
    while (bits > 0 && blCount[bits] === 0) bits--;
    if (bits === 0) break; // cannot happen for a full tree with m >= 2
    blCount[bits]--;
    blCount[bits + 1] += 2;
    blCount[maxBits]--;
    overflow -= 2;
  }
  // Most frequent symbols get the shortest lengths.
  const byFreq = syms.slice().sort((a, b) => (freqs[b] - freqs[a]) || (a - b));
  let idx = 0;
  for (let len = 1; len <= maxBits && idx < m; len++) {
    for (let k = 0; k < blCount[len] && idx < m; k++) lengths[byFreq[idx++]] = len;
  }
  while (idx < m) lengths[byFreq[idx++]] = maxBits; // safety net, never expected
  ensureTwo(lengths);
  return lengths;
}

// A valid DEFLATE code must never be a single symbol: give a second,
// never-used symbol length 1 as well when only one symbol is used.
function ensureTwo(lengths) {
  let used = 0;
  let only = -1;
  for (let i = 0; i < lengths.length; i++) {
    if (lengths[i] > 0) { used++; only = i; }
  }
  if (used === 1) {
    for (let i = 0; i < lengths.length; i++) {
      if (lengths[i] === 0) { lengths[i] = 1; return; }
    }
    lengths[only] = 1;
  }
}

// One LZ77 pass over the whole input: longest match and longest near match
// in two distance bands (<= NEAR2_DIST and <= NEAR_DIST) at every position.
// The bands matter because a shorter match at a tiny distance is often
// cheaper than the longest match at a far distance; the DP tries each.
function lz77FindMatches(data, chainLimit) {
  const chain = chainLimit === undefined || chainLimit === null || chainLimit <= 0 ? CHAIN : chainLimit;
  const n = data.length;
  const head = new Int32Array(32768).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const bestLen = new Uint16Array(n);
  const bestDist = new Int32Array(n);
  const nearLen = new Uint16Array(n);
  const nearDist = new Int32Array(n);
  const near2Len = new Uint16Array(n);
  const near2Dist = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    let bl = 0;
    let bd = 0;
    let nl = 0;
    let nd = 0;
    let n2l = 0;
    let n2d = 0;
    if (i + 2 < n) {
      const h = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & 32767;
      let cand = head[h];
      let cnt = 0;
      while (cand !== -1 && cnt < chain) {
        const dist = i - cand;
        if (dist > WINDOW) break;
        let len;
        if (bl > 0) {
          // Quick reject: the byte just past the current best must match,
          // else this candidate cannot beat it. It is only a filter: the
          // full comparison below still starts at byte 0.
          if (i + bl >= n || data[cand + bl] !== data[i + bl]) {
            cnt++;
            cand = prev[cand];
            continue;
          }
        }
        // Compare from byte 0: the hash only makes the first 3 bytes
        // likely equal, and a collision must not overstate the match.
        len = 0;
        while (len < MAX_MATCH && i + len < n && data[cand + len] === data[i + len]) len++;
        if (len > bl) { bl = len; bd = dist; }
        if (dist <= NEAR_DIST && len > nl) { nl = len; nd = dist; }
        if (dist <= NEAR2_DIST && len > n2l) { n2l = len; n2d = dist; }
        if (bl >= NICE_LEN) break;
        cnt++;
        cand = prev[cand];
      }
      prev[i] = head[h];
      head[h] = i;
    }
    bestLen[i] = bl;
    bestDist[i] = bd;
    nearLen[i] = nl;
    nearDist[i] = nd;
    near2Len[i] = n2l;
    near2Dist[i] = n2d;
  }
  return { bestLen, bestDist, nearLen, nearDist, near2Len, near2Dist };
}

// Shortest-path DP over one block [s, e) of data. litCosts[286] and
// distCosts[30] already include the extra bits of each length/distance code.
// Returns the forward token sequence as flat arrays.
function dpBlock(data, s, e, m, litCosts, distCosts) {
  const blen = e - s;
  const INF = 0x3fffffff;
  const cost = new Int32Array(blen + 1).fill(INF);
  const stepLen = new Int32Array(blen + 1);
  const stepDist = new Int32Array(blen + 1);
  cost[0] = 0;
  const { bestLen, bestDist, nearLen, nearDist, near2Len, near2Dist } = m;
  for (let i = 0; i < blen; i++) {
    const base = cost[i];
    if (base === INF) continue;
    const pos = s + i;
    const litCost = base + litCosts[data[pos]];
    if (litCost < cost[i + 1]) {
      cost[i + 1] = litCost;
      stepLen[i + 1] = 0;
    }
    const remain = blen - i;
    for (let opt = 0; opt < 3; opt++) {
      const len0 = opt === 0 ? bestLen[pos] : opt === 1 ? nearLen[pos] : near2Len[pos];
      const dist = opt === 0 ? bestDist[pos] : opt === 1 ? nearDist[pos] : near2Dist[pos];
      if (len0 < MIN_MATCH || dist === 0) continue;
      if (opt === 1 && dist === bestDist[pos]) continue;
      if (opt === 2 && (dist === bestDist[pos] || dist === nearDist[pos])) continue;
      const len = len0 < remain ? len0 : remain;
      if (len < MIN_MATCH) continue;
      const dc = distCosts[DIST_CODE[dist]];
      const cand = CAND[len];
      for (let k = 0; k < cand.length; k += 2) {
        const L = cand[k + 1];
        const mc = base + litCosts[257 + cand[k]] + dc;
        if (mc < cost[i + L]) {
          cost[i + L] = mc;
          stepLen[i + L] = L;
          stepDist[i + L] = dist;
        }
      }
    }
  }
  // Backtrack into flat forward arrays.
  const seqLit = new Uint8Array(blen + 1);
  const seqIsMatch = new Uint8Array(blen + 1);
  const seqLen = new Uint16Array(blen + 1);
  const seqDist = new Int32Array(blen + 1);
  let count = 0;
  let p = blen;
  const revLen = new Int32Array(blen + 1);
  const revDist = new Int32Array(blen + 1);
  let r = 0;
  while (p > 0) {
    const L = stepLen[p];
    if (L === 0) {
      revLen[r] = 0;
      revDist[r] = data[s + p - 1];
      p--;
    } else {
      revLen[r] = L;
      revDist[r] = stepDist[p];
      p -= L;
    }
    r++;
  }
  for (let i = r - 1; i >= 0; i--) {
    const L = revLen[i];
    if (L === 0) {
      seqLit[count] = revDist[i];
      seqIsMatch[count] = 0;
    } else {
      seqIsMatch[count] = 1;
      seqLen[count] = L;
      seqDist[count] = revDist[i];
    }
    count++;
  }
  return { seqLit, seqIsMatch, seqLen, seqDist, count };
}

function countFrequencies(seq) {
  const freqLitLen = new Uint32Array(286);
  const freqDist = new Uint32Array(30);
  for (let i = 0; i < seq.count; i++) {
    if (seq.seqIsMatch[i]) {
      freqLitLen[257 + LEN_CODE[seq.seqLen[i]]]++;
      freqDist[DIST_CODE[seq.seqDist[i]]]++;
    } else {
      freqLitLen[seq.seqLit[i]]++;
    }
  }
  freqLitLen[256]++;
  return { freqLitLen, freqDist };
}

// Cost arrays (in bits) from code lengths, extra bits folded in. A symbol
// with code length 0 is NOT in the code, so it must not look free: give it
// the maximum code length (15) so the DP only uses it when forced. (A cost
// of 0 here made iteration 2 flood small blocks with free literals of an
// unused byte, e.g. byte 0 in palette data: 30k literals instead of 144
// matches.)
function costsFromLengths(litLens, distLens) {
  const litCosts = new Int32Array(286);
  const distCosts = new Int32Array(30);
  for (let i = 0; i < 286; i++) litCosts[i] = litLens[i] === 0 ? 15 : litLens[i];
  for (let c = 0; c < 29; c++) litCosts[257 + c] += LEN_EXTRA[c];
  for (let c = 0; c < 30; c++) distCosts[c] = (distLens[c] === 0 ? 15 : distLens[c]) + DIST_EXTRA[c];
  return { litCosts, distCosts };
}

function fixedCosts() {
  const litLens = new Uint8Array(286);
  for (let i = 0; i <= 143; i++) litLens[i] = 8;
  for (let i = 144; i <= 255; i++) litLens[i] = 9;
  for (let i = 256; i <= 279; i++) litLens[i] = 7;
  for (let i = 280; i <= 287; i++) litLens[i] = 8;
  const distLens = new Uint8Array(30).fill(5);
  return costsFromLengths(litLens, distLens);
}

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

// Encode one dynamic-Huffman DEFLATE block holding seq (tokens of one block).
function encodeDynamicBlock(bw, seq, litLens, distLens, isFinal) {
  bw.writeBits(isFinal ? 1 : 0, 1);
  bw.writeBits(2, 2); // BTYPE = dynamic
  bw.writeBits(29, 5); // HLIT: 286 literal/length codes
  bw.writeBits(29, 5); // HDIST: 30 distance codes
  // RLE the 286 + 30 code lengths into (symbol, extra value) pairs.
  const total = 316;
  const allLens = new Uint8Array(total);
  allLens.set(litLens, 0);
  allLens.set(distLens, 286);
  const rclSym = new Uint8Array(1024);
  const rclExtra = new Uint16Array(1024);
  let rclN = 0;
  let i = 0;
  while (i < total) {
    const v = allLens[i];
    let run = 1;
    while (i + run < total && allLens[i + run] === v) run++;
    if (v === 0) {
      let rem = run;
      while (rem >= 11) {
        const u = rem < 138 ? rem : 138;
        rclSym[rclN] = 18; rclExtra[rclN] = u - 11; rclN++;
        rem -= u;
      }
      while (rem >= 3) {
        const u = rem < 10 ? rem : 10;
        rclSym[rclN] = 17; rclExtra[rclN] = u - 3; rclN++;
        rem -= u;
      }
      while (rem > 0) { rclSym[rclN] = 0; rclExtra[rclN] = 0; rclN++; rem--; }
    } else {
      rclSym[rclN] = v; rclExtra[rclN] = 0; rclN++;
      let rem = run - 1;
      while (rem >= 3) {
        const u = rem < 6 ? rem : 6;
        rclSym[rclN] = 16; rclExtra[rclN] = u - 3; rclN++;
        rem -= u;
      }
      while (rem > 0) { rclSym[rclN] = v; rclExtra[rclN] = 0; rclN++; rem--; }
    }
    i += run;
  }
  const clFreq = new Uint32Array(19);
  for (let k = 0; k < rclN; k++) clFreq[rclSym[k]]++;
  const clLens = codeLengths(clFreq, 7);
  const clCodes = canonicalCodes(clLens);
  let lastNz = -1;
  for (let k = 18; k >= 0; k--) {
    if (clLens[CL_ORDER[k]] !== 0) { lastNz = k; break; }
  }
  const hclen = lastNz + 1 < 4 ? 4 : lastNz + 1;
  bw.writeBits(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.writeBits(clLens[CL_ORDER[k]], 3);
  for (let k = 0; k < rclN; k++) {
    const sym = rclSym[k];
    bw.writeBits(clCodes[sym], clLens[sym]);
    if (sym === 16) bw.writeBits(rclExtra[k], 2);
    else if (sym === 17) bw.writeBits(rclExtra[k], 3);
    else if (sym === 18) bw.writeBits(rclExtra[k], 7);
  }
  const llCodes = canonicalCodes(litLens);
  const dCodes = canonicalCodes(distLens);
  for (let k = 0; k < seq.count; k++) {
    if (seq.seqIsMatch[k]) {
      const L = seq.seqLen[k];
      const lc = LEN_CODE[L];
      bw.writeBits(llCodes[257 + lc], litLens[257 + lc]);
      if (LEN_EXTRA[lc] > 0) bw.writeBits(L - LEN_BASE[lc], LEN_EXTRA[lc]);
      const d = seq.seqDist[k];
      const dc = DIST_CODE[d];
      bw.writeBits(dCodes[dc], distLens[dc]);
      if (DIST_EXTRA[dc] > 0) bw.writeBits(d - DIST_BASE[dc], DIST_EXTRA[dc]);
    } else {
      const b = seq.seqLit[k];
      bw.writeBits(llCodes[b], litLens[b]);
    }
  }
  bw.writeBits(llCodes[256], litLens[256]); // end of block
}

// Optimal-parse DEFLATE of data, one zlib stream. blockSize 0 means a single
// dynamic block for the whole input; otherwise blocks of at most blockSize
// bytes (matches never cross a block boundary).
export function deflateOptimal(data, blockSize, chainLimit) {
  const n = data.length;
  const bs = blockSize === undefined || blockSize === null || blockSize <= 0 ? n : blockSize;
  const out = new Uint8Array(n + (n >> 3) + 8192);
  const bw = new BitWriter(out);
  bw.writeBits(0x78, 8);
  bw.writeBits(0xda, 8);
  const m = lz77FindMatches(data, chainLimit);
  const fixed = fixedCosts();
  for (let s = 0; s < n; s += bs) {
    const e = s + bs < n ? s + bs : n;
    const isFinal = e >= n;
    // Iteration 1: fixed Huffman costs.
    const seq1 = dpBlock(data, s, e, m, fixed.litCosts, fixed.distCosts);
    const f1 = countFrequencies(seq1);
    const litLens1 = codeLengths(f1.freqLitLen, 15);
    const distLens1 = codeLengths(f1.freqDist, 15);
    const c2 = costsFromLengths(litLens1, distLens1);
    // Iteration 2: refined dynamic costs.
    const seq2 = dpBlock(data, s, e, m, c2.litCosts, c2.distCosts);
    const f2 = countFrequencies(seq2);
    const litLens2 = codeLengths(f2.freqLitLen, 15);
    const distLens2 = codeLengths(f2.freqDist, 15);
    encodeDynamicBlock(bw, seq2, litLens2, distLens2, isFinal);
  }
  bw.flush();
  const adler = adler32(data);
  const pos = bw.pos;
  const finalOut = bw.out; // the writer may have grown the buffer
  const res = new Uint8Array(pos + 4);
  res.set(finalOut.subarray(0, pos), 0);
  res[pos] = (adler >>> 24) & 0xff;
  res[pos + 1] = (adler >>> 16) & 0xff;
  res[pos + 2] = (adler >>> 8) & 0xff;
  res[pos + 3] = adler & 0xff;
  return res;
}
