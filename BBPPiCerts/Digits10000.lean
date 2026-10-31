/-
  digit correctness (literal capped form, `BBPSpigotDigitCorrect`) unconditionally for every `n ≤ 10000`.
  Check: `BBPFastGuard.lean` + `BBPFastCertsAll10000`. The bound is a compute-budget choice, not a
  mathematical limit. NOT proved: `PBBP01General` (all `n`); see `Thoughts/Research/BBPCapAnalysis.lean`.
-/
import BBPPi.Identity
import BBPPi.Guarded
import BBPPi.Spigot
import BBPPiCerts.Digits300
import BBPPiCerts.FastCerts.All10000

namespace BBPPi

theorem BBPSpigotDigitCorrect_of_le_10000_unconditional (n : ℕ) (hn : n ≤ 10000) :
    BBPSpigotDigitCorrect n :=
  BBPSpigotDigitCorrect_of_guard bbpPiEqualsSeries_proved n (bbpGuardAgrees_of_lt_10001 n (by omega))

end BBPPi
