# png-squeeze — lossless PNG re-encoder

Entry for [make.fun — Squeeze screenshots into the smallest PNG, 27 November 2026](https://make.fun/bounty/png-squeeze-01-run-20261127).

`main.ts` (Node 22, built-ins only) reads 8 screenshots of 1280×720 RGBA from
`/input/<id>/image.png` and writes a lossless, smaller PNG for each to
`/output/<id>/image.png`, in under 60 seconds for the whole set, deterministically
(two runs are byte-identical). `optdeflate.ts` is a pure-JavaScript
optimal-parse DEFLATE encoder (zopfli-style) used for the final compression.

How it squeezes:

- **Colour-type reduction, detected per image at runtime** — a palette
  (colour type 3, transparent entries first, tried in count order and in
  luminance order) when the image holds at most 256 colours; grey
  (type 0) or grey+alpha (type 4) when every pixel is grey; a `tRNS` key
  instead of an alpha channel when there is a single fully-transparent
  value; RGB/RGBA otherwise.
- **Adaptive filters, searched per image** — fixed filters, the
  minimum-sum and fewest-distinct-pairs heuristics, per-row brute force
  (each filter actually deflated after the previous 32 KiB), and a
  block-brute search (one filter per 8-row block, scored by a real
  level-9 deflate). Candidates are screened at zlib level 6, the best
  two per form re-ranked at level 9.
- **Final compression** — zlib level 9 as the fallback, then optimal-parse
  DEFLATE (`optdeflate.ts`: hash-chain LZ77 with near matches, shortest-path
  DP over length-code boundaries in two cost-model iterations, dynamic
  Huffman, 256 KiB blocks; the hash-chain budget is 1024 for the small
  instances and 128 for the large ones, chosen by input size only) on the
  same filtered data — the smaller stream wins.

## Run locally on the practice set

```sh
MAKEFUN_INPUT_DIR=<kit>/practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

## License

MIT. See [LICENSE](LICENSE).
