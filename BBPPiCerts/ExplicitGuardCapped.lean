import BBPPi.ExplicitGuard
import BBPPiCerts.Digits300
import BBPPiCerts.Digits1000

/-!
# Capped digit theorems for `n ≤ 1000` via the explicit guard

The capped certificate `bbpHexDigitCert` (guard search `g ≤ 68`) is correct for `n ≤ 1000`; this
re-derives that from the explicit-guard soundness of `BBPPi.ExplicitGuard`, using the kernel
certificates `bbpGuardAgrees_of_lt_301` and `bbpGuardAgrees_of_lt_1001`.
-/

namespace BBPPi

/-- `n ≤ 300` capped theorem, re-derived from the explicit-guard soundness (`g = bbpCertGuard n`). -/
theorem BBPSpigotDigitCorrect_of_le_300_via_explicit (n : ℕ) (hn : n ≤ 300) :
    BBPSpigotDigitCorrect n :=
  BBPSpigotDigitCorrect_of_guardAt (bbpGuardAgrees_of_lt_301 n (by omega))

/-- `n ≤ 1000` capped theorem, re-derived from the explicit-guard soundness. -/
theorem BBPSpigotDigitCorrect_of_le_1000_via_explicit (n : ℕ) (hn : n ≤ 1000) :
    BBPSpigotDigitCorrect n :=
  BBPSpigotDigitCorrect_of_guardAt (bbpGuardAgrees_of_lt_1001 n (by omega))

/-- `n ≤ 1000` floor equation, re-derived from the explicit-guard soundness. -/
theorem bbpCertFloor_eq_floor_pi_of_le_1000_via_explicit (n : ℕ) (hn : n ≤ 1000) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloor n : ℤ) :=
  (show BBPGuardAgreesAt n (bbpCertGuard n) from bbpGuardAgrees_of_lt_1001 n (by omega)).floor_pi

end BBPPi
