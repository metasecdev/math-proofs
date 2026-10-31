import Lake
open Lake DSL

package math_proofs where
  moreServerArgs := #["-DautoImplicit=false"]

-- Mathlib pinned to the exact revision used by the source development.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "816ff4582a01b10567d1d4ecb10be7c4ff92aab4"

/-- BBP / π development. Default target: CI builds every module imported by `Thoughts.lean`. -/
@[default_target]
lean_lib Thoughts where
  roots := #[`Thoughts]

-- Heavy kernel certificates for the capped P-BBP-01 checks n ≤ 3099 / 5899 / 8299 / 10000
-- (`decide +kernel` over BBPFastGuard.chkFrom; source: irrational-gap-mobius @ 881fc80).
-- NOT a default target and NOT built or checked by CI: they need > 10 GB RAM per Lean process
-- and time out / run out of memory on hosted runners. Build explicitly on a large machine:
--   lake build BBPHeavyCerts
lean_lib BBPHeavyCerts where
  roots := #[`Thoughts.Proved.BBPDigitsUnconditionalExt3099,
    `Thoughts.Proved.BBPDigitsUnconditionalExt5899,
    `Thoughts.Proved.BBPDigitsUnconditionalExt8299,
    `Thoughts.Proved.BBPDigitsUnconditionalExt10000]
