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
