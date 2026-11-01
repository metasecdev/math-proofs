# A formally verified hexadecimal digit extraction for π with an explicit guard for every position

Author: Brian Bernard Taylor. AI tools were used for drafting and are credited
only in the acknowledgements; they are not authors.

**Status: draft.** This paper has not been submitted to arXiv or any venue,
and nothing in this folder has been made public.

## Contents

| File | Purpose |
|------|---------|
| `main.tex` | Paper source (`amsart`, BibTeX) |
| `refs.bib` | Bibliography |
| `main.pdf` | Built PDF (9 pages) |
| `guardtable.py` | Numerics for Table 1 (mpmath; not part of the Lean proof) |
| `PLAN.md` | Publication plan for the Lean code (status per step) |
| `LICENSE-CC-BY-4.0` | License for the text |

## Build

```
tectonic main.tex
```

Built with Tectonic 0.17.0: zero errors, no overfull boxes, no missing glyphs. Under XeTeX
the listings use DejaVu Sans Mono for the Lean symbols. A standard `latexmk -xelatex main.tex`
(or `-pdf`) should also work.

## Lean sources

The Lean code is in this repository, `metasecdev/math-proofs` (private), on branch `main`.
Table 2 of the paper cites the release tag `v1.0.0`, using paths relative to `Thoughts/`. The toolchain is
`leanprover/lean4:v4.29.0-rc8`, with Mathlib `816ff4582a01b10567d1d4ecb10be7c4ff92aab4` pinned
in both `lakefile.lean` and `lake-manifest.json`.

- Main theorem, two co-equal forms (sharp: `g ≥ 569n + ⌊log₁₆(n+1)⌋ + 1 + 1795710`;
  simplified: `g ≥ 570n + 1795711`):
  `Thoughts/Research/BBPMu570b.lean`. The irrationality measure is in
  `Thoughts/Research/MahlerSharp7b.lean`.
- Runs, distance and need (Section 7): `Thoughts/Research/PiDigitStructure.lean`.
- Capped certificate (Appendix A): the window near 2^272 is in
  `Thoughts/Research/BBPCapBracket.lean` and `Thoughts/Research/BBPCapRefutation.lean`.
  The `n ≤ 10000` certificates are in `Thoughts/Proved/BBPDigitsUnconditionalExt10000.lean`, in the
  Lake library `BBPHeavyCerts`. GitHub CI does not build that library. It was **checked by a local build on the MacBookPro at
  `d8e418e`** (`lake build BBPHeavyCerts`, then `Thoughts/AxiomsHeavy.lean`; only `propext`,
  `Classical.choice`, `Quot.sound`); see `reports/heavy-certs-2026-10-31.md`.
  The positions 10001 ≤ n ≤ 2^272 − 72 are unchecked.
- Axioms: `Thoughts/Axioms.lean` prints the axioms of every Table 2 result that is in the
  default build. The `Lean CI` workflow runs it and gates it with `scripts/check_axioms.py`
  (only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`).

The root `README.md` has a table mapping each paper result to its Lean name and file.
`PLAN.md` records which publication steps are done and which are still open.

## CI

The `Paper` workflow (`.github/workflows/paper.yml`) builds `main.tex` with Tectonic 0.17.0 on
every change under `paper/`. It fails on missing glyphs or unresolved references, and uploads
the PDF as the `paper-pdf` artifact.

## License

The text of the paper is licensed under CC-BY-4.0 (`LICENSE-CC-BY-4.0`).
