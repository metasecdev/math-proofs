# math-proofs

Lean 4 / Mathlib formalisation accompanying the paper
*Explicit guard depths for the BBP digit-extraction formula for π* (Brian Bernard Taylor),
whose source is in [`paper/`](paper/).

What it proves, at a glance:

* the BBP identity `bbpSeries = Real.pi`;
* soundness of a guarded, natural-number BBP spigot: whenever the guard check passes at
  depth `g`, the certificate returns `⌊16ⁿ π⌋` and the `n`-th hex digit of π;
* an explicit irrationality measure of π at the denominators `16^k`
  (`|π − p/16^k| > 2^(−7182802) · 16^(−570k)`), via a Mahler–Mignotte argument;
* hence an explicit guard depth that is correct for **every** position `n`
  (`g(n) = 569n + ⌊log₁₆(n+1)⌋ + 1795711`, or simply any `g ≥ 570n + 1795711`);
* structural results relating runs of `0`/`F` digits, the distance of `16ⁿπ` to the
  integers, and the depth actually needed.

Everything is in the namespace `BBPPi`. There is no `sorry`, no `native_decide`
(finite checks use `decide +kernel`), and every headline theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain
(`leanprover/lean4:v4.29.0-rc8`) is pinned in `lean-toolchain`, and Mathlib is pinned to
`816ff4582a01b10567d1d4ecb10be7c4ff92aab4` in both `lakefile.lean` and `lake-manifest.json`.

```bash
lake exe cache get      # download prebuilt Mathlib oleans
lake build              # default target: library BBPPi
bash scripts/check_axioms.sh   # #print axioms for every headline theorem -> axioms-report.txt
bash scripts/check_hygiene.sh  # no sorry / admit / native_decide
```

The default target builds in a few minutes on a laptop once the Mathlib cache is present.

### Optional certificate library

`BBPPiCerts` is **not** part of the default target. It contains the capped certificate
(guard cap 68) and the kernel-checked certificates for all positions `n ≤ 10000`:

```bash
lake build BBPPiCerts
lake env lean BBPPiCerts/Axioms.lean
```

The largest certificate files need more than 10 GB of RAM per Lean process; limit
parallelism (e.g. `LEAN_NUM_THREADS=4`) on smaller machines. Expect it to take much
longer than the default target. CI builds only the default target.

## Main results

| Result (paper) | Lean name | File |
|---|---|---|
| BBP identity (Thm 3.1) | `bbpSeries_eq_pi` | `BBPPi/Identity.lean` |
| Guarded bracket | `bbpGuarded_bracket`, `bbpGuarded_floor_eq` | `BBPPi/Guarded.lean` |
| Soundness (Thm 4.1) | `BBPGuardAgreesAt.floor_pi`, `BBPGuardAgreesAt.digit_pi` | `BBPPi/ExplicitGuard.lean` |
| Existence of a guard | `exists_guard_agrees`, `exists_guard_floor_digit_eq`, `PBBP01ExplicitGuard_proved` | `BBPPi/GuardExists.lean`, `BBPPi/ExplicitGuard.lean` |
| Distance ⇒ guard (Lem 4.2) | `guardAgreesAt_of_dist` | `BBPPi/ConditionalAllN.lean` |
| First measure at `16^k` | `MahlerPiMeasure.pi_pow16_measure` | `BBPPi/Mahler/PiMeasure.lean` |
| Sharper measure (`2^-1720001`) | `MahlerSharp.pi_pow16_measure6` | `BBPPi/Mahler/Sharp.lean` |
| Irrationality measure (Thm 5.1) | `MahlerSharp7b.pi_pow16_irrationality_measure` | `BBPPi/Mahler/Sharp570.lean` |
| All `n` from a measure | `pi_pow16_measure_guard_all_n'`, `pi_pow16_measure_guard_all_n''` | `BBPPi/ConditionalAllN.lean`, `BBPPi/GuardLog.lean` |
| All `n`, first explicit guards | `bbp_digit_all_n_unconditional`, `bbp_digit_all_n_unconditional''` | `BBPPi/UnconditionalAllN.lean`, `BBPPi/GuardLog.lean` |
| Main theorem (Thm 6.1) | `guardAgreesAt_guard570`, `floor_digit_eq_guard570`, `guardAgreesAt_of_guard570_le` | `BBPPi/Mu570.lean` |
| Simple form (Cor 6.2) | `bbpDigit_eq_of_guard_ge`, `bbpDigit_eq_at_guard570_simple` | `BBPPi/Mu570.lean` |
| μ = 658 variant (Rem 6.3) | `guardAgreesAt_guard658`, `floor_digit_eq_guard658` | `BBPPi/Mu658.lean` |
| Generic guard-log lemma | `guard_agrees_of_const`, `guardConst_hyp_mono` | `BBPPi/GuardLog.lean` |
| Runs, distance, need (Sec 7) | `PiDigitStructure.piDist_run`, `piNeed_bounds`, `forced_chain`, `long_run_forces`, `long_gap_short_run`, `cert_78_127` | `BBPPi/DigitStructure.lean` |
| Capped cert, `n ≤ 10000` (optional) | `BBPSpigotDigitCorrect_of_le_10000_unconditional`, `bbpGuardAgrees_of_lt_10001` | `BBPPiCerts/Digits10000.lean`, `BBPPiCerts/FastCerts/All10000.lean` |
| Capped cert fails (optional) | `not_BBPSpigotDigitCorrect_window'`, `not_BBPSpigotDigitCorrect_window` | `BBPPiCerts/CapBracket.lean`, `BBPPiCerts/CapRefutation.lean` |

Section numbers refer to `paper/main.tex`. `BBPPi/Axioms.lean` and `BBPPiCerts/Axioms.lean`
list every headline theorem with `#print axioms`.

Note: the irrationality measure lives at `BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure`
rather than in the `Real` namespace, to keep this project from adding names to Mathlib's
namespaces.

## Layout and name map

This repository is a cleaned snapshot of a larger research development. Module and
declaration names were changed to Mathlib style; the old declaration names remain available
as `@[deprecated]` aliases in `BBPPi/Deprecated.lean`.

| Old declaration | New declaration |
|---|---|
| `bbp_guard_all_n_mu570b` | `guardAgreesAt_guard570` |
| `bbp_digit_all_n_mu570b` | `floor_digit_eq_guard570` |
| `bbp_guard_mu570b_of_ge` | `guardAgreesAt_of_guard570_le` |
| `bbp_digit_all_n_fixed7b` | `bbpDigit_eq_of_guard_ge` |
| `bbp_digit_all_n_at_G7b` | `bbpDigit_eq_at_guard570_simple` |
| `bbp_guard_all_n_mu658` | `guardAgreesAt_guard658` |
| `bbp_digit_all_n_mu658` | `floor_digit_eq_guard658` |
| `bbp_explicit_guard_all_n` | `exists_guard_floor_digit_eq` |
| `MahlerSharp7b.pi_pow16_measure7` | `MahlerSharp7b.pi_pow16_irrationality_measure` |

The old namespace `FinitistProved` is now `BBPPi`; namespaces such as `MahlerSharp7b` became
`BBPPi.MahlerSharp7b`.

| Old module | New module |
|---|---|
| `Proved.BBPAlgebra`, `BBPTail`, `BBPSeries`, `BBPPiIdentity`, `BBPGuarded` | `BBPPi.Algebra`, `Tail`, `Series`, `Identity`, `Guarded` |
| `Proved.Normality` (definitions) | `BBPPi.Defs` |
| `Proved.BBPSpigot`, `BBPGuardExists`, `BBPExplicitGuard` | `BBPPi.Spigot`, `GuardExists`, `ExplicitGuard` |
| `Research.BBPConditionalAllN`, `BBPUnconditionalAllN` | `BBPPi.ConditionalAllN`, `UnconditionalAllN` |
| `Research.Mahler{General,Vanishing,Det,Bounds,Mignotte,Remainder,PiMeasure,Sharp}` | `BBPPi.Mahler.{General,…,Sharp}` |
| `Research.LcmChebyshev`, `LcmChebyshevSharp` | `BBPPi.Mahler.LcmChebyshev`, `LcmChebyshevSharp` |
| `Research.MahlerSharp7b` | `BBPPi.Mahler.Sharp570` |
| `Research.BBPGuardLog`, `BBPMu570Fixed` | `BBPPi.GuardLog` |
| `Research.BBPMu658`, `BBPMu570b` | `BBPPi.Mu658`, `BBPPi.Mu570` |
| `Research.PiDigitStructure` | `BBPPi.DigitStructure` |
| `Proved.BBPGuardedCerts`, `BBPGuardedCertsExt` | `BBPPiCerts.GuardedCerts`, `GuardedCertsExt` |
| `Proved.BBPDigitsUnconditional`, `…Ext`, `…Ext10000` | `BBPPiCerts.Digits300`, `Digits1000`, `Digits10000` |
| `Proved.BBPFastGuard`, `BBPFastCerts*` | `BBPPiCerts.FastGuard`, `BBPPiCerts.FastCerts.*` |
| `Proved.BBPGuardCap`, `Research.BBPCap{Analysis,Refutation,Bracket}` | `BBPPiCerts.GuardCap`, `Cap{Analysis,Refutation,Bracket}` |

The intermediate certificate files for `n ≤ 2000, 3099, 5899, 8299` were not copied: the
`n ≤ 10000` certificate supersedes them.

## Paper

`paper/main.tex` (with `refs.bib`) builds with `tectonic main.tex`. `paper/guardtable.py`
regenerates the numerical guard table in `guardtable.json`.

## License

Copyright © 2026 Brian Bernard Taylor.

* The paper (`paper/`) is licensed under CC BY 4.0, see `paper/LICENSE-CC-BY-4.0`.
* The license for the Lean code is still to be decided (see `LICENSE`). Until then, all
  rights are reserved.
