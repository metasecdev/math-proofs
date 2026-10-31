import Lake
open Lake DSL

package mathProofs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "816ff4582a01b10567d1d4ecb10be7c4ff92aab4"

/-- Default library: the BBP identity, the guarded spigot, explicit irrationality measures for π
at denominators `16^k`, and all-`n` digit correctness with explicit guard depth. -/
@[default_target]
lean_lib BBPPi

/-- Optional library (NOT built by default): capped results and the kernel certificates for
`n ≤ 10000`. The largest certificate files need more than 10 GB of RAM per Lean process.
Build explicitly with `lake build BBPPiCerts`. -/
lean_lib BBPPiCerts
