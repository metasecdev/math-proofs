# math-proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23867087.svg)](https://doi.org/10.5281/zenodo.23867087)

Lean 4 formalization of the Bailey–Borwein–Plouffe (BBP) formula for π and of
guarded, finitely checkable certificates for the hexadecimal digits of π.

**Author:** Brian Bernard Taylor (sole author).

## Scope

This repository contains only the BBP / π work. In particular:

1. **The BBP identity.** π = Σₖ 16⁻ᵏ (4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)),
   proved in Lean against Mathlib's `Real.pi` (`bbpSeries_eq_pi`).
2. **Guarded digit certificates.** A natural-number interval `[lo, hi]` computed from the
   BBP series with an explicit tail guard `g`. Whenever `lo = hi` (a decidable check), the
   common value is provably `⌊16ⁿ·π⌋`, so its residue mod 16 is the `n`-th hex digit of π.
   Concrete instances are checked by the Lean kernel (`decide +kernel`).
3. **An effective irrationality-measure bound for π in base 16.** A Mahler-style
   argument giving an explicit lower bound on `|16ᵏ·π − p|` for all integers `p` and all
   `k ≥ 1`. It yields an explicit linear guard `g(n)` that certifies the `n`-th hex
   digit of π for every `n`.

Not claimed here: anything about the normality of π, digit statistics beyond what is
stated in the Lean files, or results outside the BBP / π programme.

## Finitist framing

Every digit statement reduces to a computation on natural numbers: finite sums of integer
BBP terms, a finite guard, and an equality check `lo = hi`. Real analysis enters only to
connect that finite check to `Real.pi`, through the BBP identity and an explicit tail
bound. The kernel checks all certificates; no external oracle or compiled evaluation is
trusted.

## Trust base

* No `sorry`, and no `native_decide` (so `Lean.ofReduceBool` never appears).
* `#print axioms` on the key theorems may list only Lean's three standard axioms:
  `propext`, `Classical.choice`, `Quot.sound`. CI fails on anything else.
* The list of key theorems is `Thoughts/Axioms.lean` (not imported by `Thoughts.lean`). CI runs
  `lake env lean Thoughts/Axioms.lean` after `lake build`, gates the output with
  `scripts/check_axioms.py`, and uploads it as the `axioms-report` artifact.
  `scripts/check_axioms.py` also scans every `.lean` file for `sorry`, `admit`, `native_decide`,
  `axiom`, `implemented_by` and `extern`.

## Main results

Names and files on `main`. The paper is `paper/main.tex`; section numbers refer to it.
The headline theorems are in the namespace `BBPPi` (full names shown); the other declarations are
in `FinitistProved` unless another namespace is shown. The earlier names of the renamed theorems
remain as deprecated aliases in `Thoughts/Deprecated.lean` (see the name map below).

| Result (paper) | Lean name | File |
|---|---|---|
| BBP identity (Sec. 3) | `bbpSeries_eq_pi` | `Thoughts/Proved/BBPPiIdentity.lean` |
| Soundness of the certificate (Sec. 4) | `BBPGuardAgreesAt.floor_pi`, `BBPGuardAgreesAt.digit_pi` | `Thoughts/Proved/BBPExplicitGuard.lean` |
| An agreeing guard exists for every `n` | `BBPPi.exists_guard_floor_digit_eq` | `Thoughts/Proved/BBPExplicitGuard.lean` |
| Distance criterion (Sec. 4) | `guardAgreesAt_of_dist` | `Thoughts/Research/BBPConditionalAllN.lean` |
| Irrationality measure at `16^k`: `\|16^k π − p\| · 16^(570k) > 2^-7182802 · 16^k` (Sec. 5) | `BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure` | `Thoughts/Research/MahlerSharp7b.lean` |
| **Main theorem (1), sharp form** (Thm 6.1): every guard depth `g ≥ 569·n + ⌊log₁₆(n+1)⌋ + 1 + B`, `B = 1795710`, returns `⌊16ⁿπ⌋` and the `n`-th hex digit | `BBPPi.guardAgreesAt_guard570`, `BBPPi.floor_digit_eq_guard570`, `BBPPi.guardAgreesAt_of_guard570_le` | `Thoughts/Research/BBPMu570b.lean` |
| **Main theorem (2), simplified form** (Thm 6.1): every guard depth `g ≥ 570·n + 1795711` returns `⌊16ⁿπ⌋` and the `n`-th hex digit | `BBPPi.bbpDigit_eq_of_guard_ge`, `BBPPi.bbpDigit_eq_at_guard570_simple` | `Thoughts/Research/BBPMu570b.lean` |
| Exponent-658 guard `657·n + ⌊log₁₆(n+1)⌋ + 1 + 430009` (remark, Sec. 6) | `BBPPi.guardAgreesAt_guard658`, `BBPPi.floor_digit_eq_guard658` | `Thoughts/Research/BBPMu658.lean` |
| Runs, distance and need (Sec. 7) | `PiDigitStructure.piDist_run`, `piNeed_bounds`, `forced_chain`, `long_run_forces` | `Thoughts/Research/PiDigitStructure.lean` |
| `ρ(77) = 0` and `γ(78) = 49` (Sec. 7) | `PiDigitStructure.long_gap_short_run`, `cert_78_127` | `Thoughts/Research/PiDigitStructure.lean` |
| Capped certificate returns a wrong digit for `2^272 − 71 ≤ n`, `5n + 348 ≤ 14·2^272` (Appendix A) | `not_BBPSpigotDigitCorrect_window'`, `not_BBPSpigotDigitCorrect_window` | `Thoughts/Research/BBPCapBracket.lean`, `Thoughts/Research/BBPCapRefutation.lean` |
| Capped certificate correct for `n ≤ 10000` (Appendix A; checked by a local build on the MacBookPro at `d8e418e`; GitHub CI does not build it, see `reports/heavy-certs-2026-10-31.md`) | `BBPSpigotDigitCorrect_of_le_10000_unconditional` | `Thoughts/Proved/BBPDigitsUnconditionalExt10000.lean` |
| Capped certificate correct for `n ≤ 2000` (checked by CI) | `BBPSpigotDigitCorrect_of_le_2000_unconditional` | `Thoughts/Proved/BBPDigitsUnconditionalExt2000.lean` |

Earlier, weaker versions of the main theorem remain in the tree (`MahlerPiMeasure`,
`MahlerSharp`, `MahlerSharp7`, `BBPUnconditionalAllN`, `BBPGuardLog`, `BBPMu570*`); they are
listed in the second block of `Thoughts/Axioms.lean`.

### Name map (renamed 2026-11-01, release `v1.0.0`)

| Old name (deprecated alias) | New name |
|---|---|
| `FinitistProved.bbp_guard_all_n_mu570b` | `BBPPi.guardAgreesAt_guard570` |
| `FinitistProved.bbp_digit_all_n_mu570b` | `BBPPi.floor_digit_eq_guard570` |
| `FinitistProved.bbp_guard_mu570b_of_ge` | `BBPPi.guardAgreesAt_of_guard570_le` |
| `FinitistProved.bbp_digit_all_n_fixed7b` | `BBPPi.bbpDigit_eq_of_guard_ge` |
| `FinitistProved.bbp_digit_all_n_at_G7b` | `BBPPi.bbpDigit_eq_at_guard570_simple` |
| `FinitistProved.bbp_guard_all_n_mu658` | `BBPPi.guardAgreesAt_guard658` |
| `FinitistProved.bbp_digit_all_n_mu658` | `BBPPi.floor_digit_eq_guard658` |
| `FinitistProved.bbp_explicit_guard_all_n` | `BBPPi.exists_guard_floor_digit_eq` |
| `MahlerSharp7b.pi_pow16_measure7` | `BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure` |

The old names still resolve, with a deprecation warning. The heavy certificate theorems
(`BBPSpigotDigitCorrect_of_le_10000_unconditional`, `bbpGuardAgrees_of_lt_10001`) keep their names,
so the heavy modules are unchanged.

## Building

```
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

The toolchain is pinned in `lean-toolchain`. The Mathlib revision is pinned in
`lakefile.lean` and `lake-manifest.json`.

## Provenance

The code was imported from the author's development repository; each import commit
records the source repository and commit SHA.

## Heavy certificates (not built by GitHub CI; checked locally)

`lean_lib BBPHeavyCerts` (`BBPDigitsUnconditionalExt3099/5899/8299/10000` and the
`BBPFastCerts*` modules) holds the kernel certificates for the capped digit checks up to
n ≤ 10000. It is **not** a default target, and **CI does not build or check it**: each Lean
process needs more than 10 GB of RAM (up to about 16 GB). It was built and axiom-checked locally on
the MacBookPro at commit `d8e418e` (2026-10-31): 0 errors, no `sorry`, and every theorem uses only
`propext`, `Classical.choice`, `Quot.sound`; see `reports/heavy-certs-2026-10-31.md`.
To reproduce, build it explicitly on a large machine, then audit its axioms:

```
lake build BBPHeavyCerts
lake env lean Thoughts/AxiomsHeavy.lean 2>&1 | tee axioms-heavy.log
python3 scripts/check_axioms.py axioms-heavy.log
```

The default build covers everything else, including n ≤ 2000.

## How to cite

Citation metadata is in [`CITATION.cff`](CITATION.cff) (GitHub shows it as "Cite this repository").
Please cite the software as:

> Brian Bernard Taylor. *A formally verified hexadecimal digit extraction for pi with an explicit
> guard for every position (Lean 4 development)*, version 1.0.1. Zenodo.
> https://doi.org/10.5281/zenodo.23867088

The release is archived on Zenodo. The concept DOI
[10.5281/zenodo.23867087](https://doi.org/10.5281/zenodo.23867087) always resolves to the latest
version; the version DOI [10.5281/zenodo.23867088](https://doi.org/10.5281/zenodo.23867088) is
v1.0.1 exactly.

## License

* Code (Lean sources, scripts, CI and everything outside `paper/`): Apache License 2.0, see
  [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Copyright 2026 Brian Bernard Taylor.
* Paper (`paper/`): the text is licensed under CC BY 4.0, see
  [`paper/LICENSE-CC-BY-4.0`](paper/LICENSE-CC-BY-4.0).
