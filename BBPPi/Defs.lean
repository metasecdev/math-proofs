import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import BBPPi.Tail

/-!
# Hex digits of π: certificate digit and true digit

This file defines the two digit functions that the rest of the library compares.

## Main definitions

* `BBPPi.bbpHexDigitCert n`: the low hex digit of the guarded BBP floor certificate
  `bbpCertFloor n` (computable, natural numbers only). `bbp_hex_digit` is an alias.
* `BBPPi.piHexDigit n`: the true `n`-th hexadecimal digit `⌊16^n · π⌋ mod 16` of `π`,
  so `piHexDigit 0 = 3` (`π = 3.243F6A88…₁₆`). Noncomputable.
* `BBPPi.piGapSeq start`: the distance from `start` to the next position whose true hex digit is
  `1` (`0` if there is none).

The certificate digit is shown to equal the true digit (under explicit guard hypotheses) in
`BBPPi.Spigot` and `BBPPi.ExplicitGuard`.
-/

namespace BBPPi

open Real Nat Finset

/-- Certificate hex digit at position `n`: `bbpCertFloor n % 16`, where `bbpCertFloor n` is the
guarded spigot floor certificate for `⌊16^n · π⌋`. It equals the true digit whenever the
decidable guard check `bbpGuardAgrees n` passes (`BBPSpigotDigitCorrect_of_guard`). -/
def bbpHexDigitCert (n : Nat) : Nat := bbpCertFloor n % 16

/-- Alias of `bbpHexDigitCert`. -/
abbrev bbp_hex_digit (n : Nat) : Nat := bbpHexDigitCert n

/-- True `n`-th hex digit of π: `⌊16^n · π⌋ mod 16` (`d_0 = 3`). Noncomputable. -/
noncomputable def piHexDigit (n : Nat) : Nat := (⌊(16 : ℝ) ^ n * Real.pi⌋).toNat % 16

open Classical in
/-- Distance from `start` to the next position whose true π hex digit is `1`
(`0` if there is none). -/
noncomputable def piGapSeq (start : Nat) : Nat :=
  if h : ∃ k, piHexDigit (start + k) = 1 then Nat.find h else 0

theorem bbp_hex_digit_eq_cert (n : Nat) : bbp_hex_digit n = bbpHexDigitCert n := rfl

end BBPPi
