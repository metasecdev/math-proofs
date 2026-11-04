# math-proofs v1.0.1 — verified hexadecimal digits of π for every position

Lean 4 development of the BBP formula for π and an explicit, kernel-checked guard depth for the
BBP digit certificate at every position n. Accompanies `paper/main.tex` (PDF: `paper/main.pdf`).
Author: Brian Bernard Taylor.

## Changes since v1.0.0
No Lean source, `lakefile.lean`, `lake-manifest.json` or `lean-toolchain` changes; all theorem
names and statements are as in v1.0.0.
- **License and citation (#16):** code is licensed under Apache-2.0 (`LICENSE`, `NOTICE`); the paper
  text in `paper/` stays CC-BY-4.0. Added `CITATION.cff` and `.zenodo.json`, and "License" and
  "How to cite" sections in `README.md`. `lean_tools/gen_fast_guard_all.py` now reads its cache
  directory from `$FAST_G_CACHE_DIR`.
- **Paper fixes (#14):** date; Lean 4 citation (de Moura–Ullrich, CADE 2021); abstract states the
  sharp guard and notes the simplified linear form; capped-certificate status in the introduction
  shortened to a pointer to the appendix; related-work wording and lean-DLMF file history;
  certificate-section wording; Lean names fully qualified (`LcmChebyshevSharp7b.*`,
  `MahlerSharp7b.*`); strictness remark in Section 7; an appendix remark marked as heuristic,
  not proved.
- **PDF (#15):** `paper/main.pdf` rebuilt from CI.

## Toolchain
- Lean: `leanprover/lean4:v4.29.0-rc8` (`lean-toolchain`)
- Mathlib: `816ff4582a01b10567d1d4ecb10be7c4ff92aab4`, pinned in `lakefile.lean` and `lake-manifest.json`
- Build: `lake exe cache get && lake build` (default library `Thoughts`)

## Main results (paper numbering; paths relative to `Thoughts/`)
| Result | Lean name | File |
|---|---|---|
| Thm 3.1 BBP identity | `FinitistProved.bbpSeries_eq_pi` | `Proved/BBPPiIdentity.lean` |
| Thm 4.2 soundness | `FinitistProved.BBPGuardAgreesAt.floor_pi`, `.digit_pi` | `Proved/BBPExplicitGuard.lean` |
| Existence of an agreeing guard | `BBPPi.exists_guard_floor_digit_eq` | `Proved/BBPExplicitGuard.lean` |
| Lem 4.3 distance criterion | `FinitistProved.guardAgreesAt_of_dist` | `Research/BBPConditionalAllN.lean` |
| Thm 5.1 `\|16^k π − p\| · 16^(570k) > 2^-7182802 · 16^k` | `BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure` | `Research/MahlerSharp7b.lean` |
| Thm 6.1(1) sharp form: every `g ≥ 569n + ⌊log₁₆(n+1)⌋ + 1 + 1795710` | `BBPPi.guardAgreesAt_guard570`, `BBPPi.floor_digit_eq_guard570`, `BBPPi.guardAgreesAt_of_guard570_le` | `Research/BBPMu570b.lean` |
| Thm 6.1(2) simplified form: every `g ≥ 570n + 1795711` | `BBPPi.bbpDigit_eq_of_guard_ge`, `BBPPi.bbpDigit_eq_at_guard570_simple` | `Research/BBPMu570b.lean` |
| Rem 6.2 exponent-658 guard | `BBPPi.floor_digit_eq_guard658` | `Research/BBPMu658.lean` |
| Sec 7 runs, distance, need | `FinitistProved.PiDigitStructure.piDist_run`, `piNeed_bounds`, `forced_chain`, `long_run_forces`, `long_gap_short_run`, `cert_78_127` | `Research/PiDigitStructure.lean` |
| Thm A.1 capped certificate correct for n ≤ 10000 | `FinitistProved.BBPSpigotDigitCorrect_of_le_10000_unconditional` | `Proved/BBPDigitsUnconditionalExt10000.lean` (library `BBPHeavyCerts`) |
| Thm A.2 capped certificate wrong on a window near 2^272 | `FinitistProved.not_BBPSpigotDigitCorrect_window'`, `not_BBPSpigotDigitCorrect_window` | `Research/BBPCapBracket.lean`, `Research/BBPCapRefutation.lean` |

Positions 10001 ≤ n ≤ 2^272 − 72 are unchecked for the capped certificate; the main theorem
(Thm 6.1) covers every n.

## Axioms
Every theorem above reports only `propext`, `Classical.choice` and `Quot.sound` under
`#print axioms` (`cert_78_127`: `propext` only). No `sorry`, no `native_decide`, no custom
`axiom`, no `implemented_by`/`extern`. GitHub CI enforces this for the default target
(`Thoughts/Axioms.lean` + `scripts/check_axioms.py`; report uploaded as the `axioms-report`
artifact). Finite computations use `decide +kernel`.

## Heavy certificates (`BBPHeavyCerts`)
The `n ≤ 10000` certificates need more memory than hosted runners provide, so GitHub CI does not
build them. They were checked by a local build on the MacBookPro at `d8e418e`
(`lake build BBPHeavyCerts`, then `Thoughts/AxiomsHeavy.lean`; only the three standard axioms; see
`reports/heavy-certs-2026-10-31.md`). No module in the import closure of `BBPHeavyCerts`, and none of
`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, changed between `d8e418e` and this tag
(only a comment in `Thoughts/AxiomsHeavy.lean`), and no Lean source or build file changed between v1.0.0 and v1.0.1, so that check applies to v1.0.1.

## Framing
Results are stated finitistically; finite checks are kernel-checked computations (`decide +kernel`). For the capped
certificate, positions outside the checked and refuted ranges are called unchecked, not failures.

## License
Code: Apache-2.0. Paper text (`paper/`): CC-BY-4.0. Citation metadata in `CITATION.cff`.
