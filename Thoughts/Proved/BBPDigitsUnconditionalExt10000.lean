/-
  P-BBP-01 (literal capped form, `BBPSpigotDigitCorrect`) unconditionally for every `n ≤ 10000`.
  Check: `BBPFastGuard.lean` + `BBPFastCertsAll10000`. The bound is a compute-budget choice, not a
  mathematical limit. NOT proved: `PBBP01General` (all `n`); see `Thoughts/Research/BBPCapAnalysis.lean`.
-/
import Thoughts.Proved.BBPPiIdentity
import Thoughts.Proved.BBPGuarded
import Thoughts.Proved.BBPSpigot
import Thoughts.Proved.BBPDigitsUnconditional
import Thoughts.Proved.BBPFastCertsAll10000

namespace FinitistProved

theorem BBPSpigotDigitCorrect_of_le_10000_unconditional (n : ℕ) (hn : n ≤ 10000) :
    BBPSpigotDigitCorrect n :=
  BBPSpigotDigitCorrect_of_guard bbpPiEqualsSeries_proved n (bbpGuardAgrees_of_lt_10001 n (by omega))

end FinitistProved

#print axioms FinitistProved.BBPSpigotDigitCorrect_of_le_10000_unconditional
