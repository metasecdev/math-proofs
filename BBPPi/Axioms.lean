import BBPPi

/-!
# Axiom audit for the headline theorems

Run with `lake env lean BBPPi/Axioms.lean` (or `scripts/check_axioms.sh`).
Every theorem below should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

open BBPPi

-- The BBP identity
#print axioms BBPPi.bbpSeries_eq_pi
-- Soundness of the guarded bracket
#print axioms BBPPi.bbpGuarded_bracket
#print axioms BBPPi.bbpGuarded_floor_eq
-- Existence of an agreeing guard for every `n` (from irrationality of π)
#print axioms BBPPi.exists_guard_agrees
#print axioms BBPPi.exists_guard_floor_digit_eq
#print axioms BBPPi.PBBP01ExplicitGuard_proved
-- Conditional all-`n` theorems from an irrationality-measure hypothesis
#print axioms BBPPi.pi_pow16_measure_guard_all_n'
#print axioms BBPPi.pi_pow16_measure_guard_all_n''
-- Explicit irrationality measures for π at denominators `16^k`
#print axioms BBPPi.MahlerPiMeasure.pi_pow16_measure
#print axioms BBPPi.MahlerSharp.pi_pow16_measure6
#print axioms BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure
-- Unconditional all-`n` digit correctness with explicit linear guard depth
#print axioms BBPPi.bbp_digit_all_n_unconditional
#print axioms BBPPi.bbp_digit_all_n_unconditional''
#print axioms BBPPi.floor_digit_eq_guard658
#print axioms BBPPi.guardAgreesAt_guard570
#print axioms BBPPi.floor_digit_eq_guard570
#print axioms BBPPi.guardAgreesAt_of_guard570_le
#print axioms BBPPi.bbpDigit_eq_of_guard_ge
#print axioms BBPPi.bbpDigit_eq_at_guard570_simple
-- Digit structure of π
#print axioms BBPPi.PiDigitStructure.piNeed_bounds
#print axioms BBPPi.PiDigitStructure.forced_chain
#print axioms BBPPi.PiDigitStructure.long_gap_short_run
