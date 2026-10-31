import BBPPiCerts

/-!
# Axiom audit for the optional certificate library

Run with `lake build BBPPiCerts && lake env lean BBPPiCerts/Axioms.lean`.
-/

#print axioms BBPPi.bbpGuardAgrees_of_lt_301
#print axioms BBPPi.bbpGuardAgrees_of_lt_1001
#print axioms BBPPi.BBPSpigotDigitCorrect_of_le_1000_via_explicit
#print axioms BBPPi.not_forall_bbpGuardAgrees
#print axioms BBPPi.not_PBBP01General
#print axioms BBPPi.mu570_cert_of_cap
#print axioms BBPPi.bbpGuardAgrees_of_lt_10001
#print axioms BBPPi.BBPSpigotDigitCorrect_of_le_10000_unconditional
