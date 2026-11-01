import Thoughts

/-!
# Axiom audit for the headline theorems

Not imported by `Thoughts.lean`. CI runs `lake env lean Thoughts/Axioms.lean` after `lake build`,
and `scripts/check_axioms.py` fails the job unless every result below lists only `propext`,
`Classical.choice` and `Quot.sound` (so no `sorryAx` and no `Lean.ofReduceBool`, i.e. no
`native_decide`).

The first block is exactly the list of results in Table 2 of `paper/main.tex` that the default
target contains. The heavy capped certificate for `n ≤ 10000` is in `Thoughts/AxiomsHeavy.lean`
(library `BBPHeavyCerts`, not built by GitHub CI; checked by a local build on the MacBookPro at
`d8e418e`, see `reports/heavy-certs-2026-10-31.md`). Add new headline theorems here when they are
imported into `Thoughts.lean`.

The headline theorems are named in the namespace `BBPPi`; their earlier names are deprecated
aliases in `Thoughts/Deprecated.lean`.
-/

/-! ## Paper, Table 2 (default target) -/

-- Sec. 3: the BBP identity
#print axioms FinitistProved.bbpSeries_eq_pi
-- Sec. 4: soundness of the certificate
#print axioms FinitistProved.BBPGuardAgreesAt.floor_pi
#print axioms FinitistProved.BBPGuardAgreesAt.digit_pi
-- Sec. 4: distance criterion
#print axioms FinitistProved.guardAgreesAt_of_dist
-- Sec. 5: irrationality measure of π at `16^k` (μ = 570, C = 2^-7182802)
#print axioms BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure
-- Sec. 6: main theorem, part (1) sharp form (B = 1795710)
#print axioms BBPPi.guardAgreesAt_guard570
#print axioms BBPPi.floor_digit_eq_guard570
#print axioms BBPPi.guardAgreesAt_of_guard570_le
-- Sec. 6: main theorem, part (2) simplified form (570·n + 1795711)
#print axioms BBPPi.bbpDigit_eq_of_guard_ge
#print axioms BBPPi.bbpDigit_eq_at_guard570_simple
-- Sec. 6: the exponent-658 guard (remark)
#print axioms BBPPi.guardAgreesAt_guard658
#print axioms BBPPi.floor_digit_eq_guard658
-- Sec 7: runs, distance and need
#print axioms FinitistProved.PiDigitStructure.piDist_run
#print axioms FinitistProved.PiDigitStructure.piNeed_bounds
#print axioms FinitistProved.PiDigitStructure.forced_chain
#print axioms FinitistProved.PiDigitStructure.long_run_forces
#print axioms FinitistProved.PiDigitStructure.long_gap_short_run
#print axioms FinitistProved.PiDigitStructure.cert_78_127
-- Appendix A: the capped certificate returns a wrong digit on an explicit window
#print axioms FinitistProved.not_BBPSpigotDigitCorrect_window'
#print axioms FinitistProved.not_BBPSpigotDigitCorrect_window

/-! ## Other key theorems -/

-- BBP identity in the `PBBP` form, guarded digit certificates
#print axioms FinitistProved.bbpPiEqualsSeries_proved
#print axioms FinitistProved.BBPSpigotDigitCorrect_of_guard
#print axioms FinitistProved.BBPSpigotDigitCorrect_of_le_2000_unconditional
#print axioms BBPPi.exists_guard_floor_digit_eq
-- earlier irrationality measures at `16^k` and the explicit guards they give
#print axioms MahlerPiMeasure.pi_pow16_measure
#print axioms MahlerSharp.pi_pow16_measure6
#print axioms MahlerSharp7.pi_pow16_measure7
#print axioms FinitistProved.pi_pow16_measure_unconditional
#print axioms FinitistProved.bbp_digit_all_n_unconditional
#print axioms FinitistProved.bbp_digit_all_n_unconditional''
#print axioms FinitistProved.pi_pow16_measure_mu570
#print axioms FinitistProved.bbp_digit_all_n_mu570
#print axioms FinitistProved.bbp_digit_all_n_simple
#print axioms FinitistProved.bbp_digit_all_n_fixed
#print axioms FinitistProved.bbp_digit_all_n_at_G
-- capped-certificate analysis: fast checker soundness, refutation of the capped statement
#print axioms FinitistProved.chkFrom_sound
#print axioms FinitistProved.not_PBBP01General
#print axioms FinitistProved.not_BBPSpigotDigitCorrect_first
#print axioms FinitistProved.cap_window_condition_sharp
