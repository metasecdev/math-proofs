/-
  Axiom report for the key theorems. CI runs `lake env lean scripts/AxiomReport.lean`
  after `lake build` and `scripts/check_axioms.py` fails the job unless every result
  lists only `propext`, `Classical.choice`, `Quot.sound`.
  Add new headline theorems here when they are imported into `Thoughts.lean`.
-/
import Thoughts

-- (a) BBP identity
#print axioms FinitistProved.bbpSeries_eq_pi
#print axioms FinitistProved.bbpPiEqualsSeries_proved
-- (b) guarded digit certificates
#print axioms FinitistProved.BBPSpigotDigitCorrect_of_guard
#print axioms FinitistProved.BBPSpigotDigitCorrect_of_le_2000_unconditional
#print axioms FinitistProved.bbp_explicit_guard_all_n
-- (c) irrationality measure of π in base 16 and the resulting explicit guards
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
-- (c') sharpened guard at μ = 570: B = 1795710
#print axioms MahlerSharp7b.pi_pow16_measure7
#print axioms FinitistProved.bbp_digit_all_n_mu570b
#print axioms FinitistProved.bbp_digit_all_n_fixed7b
#print axioms FinitistProved.bbp_digit_all_n_at_G7b
-- forced structure of π's hex digits (runs, gaps, distance, guard need)
#print axioms FinitistProved.PiDigitStructure.forced_chain
#print axioms FinitistProved.PiDigitStructure.piNeed_bounds
#print axioms FinitistProved.PiDigitStructure.long_gap_short_run
