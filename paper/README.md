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
| `PLAN.md` | Plan (not executed) for a clean public Lean snapshot |
| `LICENSE-CC-BY-4.0` | License for the text |

## Build

```
tectonic main.tex
```

Built with Tectonic 0.17.0: zero errors, no overfull boxes. A standard
`latexmk -xelatex main.tex` (or `-pdf`) should also work.

## Lean sources

Repository `metasecdev/irrational-gap-mobius`, Lean `leanprover/lean4:v4.29.0-rc8`,
Mathlib `816ff4582a01b10567d1d4ecb10be7c4ff92aab4` (from `lake-manifest.json`).
The results currently live on three branches:

- (a) `research/sharpen-guard-2` at `2c596fec85385aec9c7d289153d41280409bdd84`: measure μ = 570, main theorem with B = 1 795 710.
- (b) `research/cap-bracket` at `881fc8069c6fef99948a2c4a6ab87cf864d3bb53`: capped certificate (Appendix A).
- (c) `research/digit-structure` at `7d37c5d1ed3749925a5ddc18c4ab6c38ae9d5876`: runs, distance and guard need (Section 7).

`PLAN.md` describes the single public snapshot that should replace these
references before submission.

## License

The text of the paper is licensed under CC-BY-4.0 (`LICENSE-CC-BY-4.0`).
