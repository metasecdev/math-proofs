# Plan: clean public Lean snapshot for the BBP/π paper (NOT executed)

Nothing here has been done. The repository stays private until Brian decides otherwise.

1. **New repository or folder.** Create a fresh repository (e.g. `bbp-pi-lean`) that holds only
   the modules the paper needs: `BBPAlgebra`, `BBPSeries`, `BBPTail`, `BBPGuarded`,
   `BBPPiIdentity`, `BBPExplicitGuard`, `BBPConditionalAllN`, `BBPGuardLog`, the `MahlerSharp*`
   chain, `BBPMu570b`, `BBPMu658`, `PiDigitStructure`, and for Appendix A `BBPSpigot`,
   `BBPFastGuard`, the `BBPFastCerts*` files, `BBPDigitsUnconditionalExt10000`, `BBPCapBracket`,
   `BBPCapRefutation`. Start from a squashed copy, not the full history.
2. **Cut unrelated imports.** In the source repository `BBPSpigot.lean` pulls in modules
   unrelated to the BBP/π work. Rewire `BBPSpigot` so that the closure of every cited theorem
   contains only BBP/π modules. Check with `lake exe graph` (import-graph).
3. **Pin dependencies.** Keep `lean-toolchain` at `leanprover/lean4:v4.29.0-rc8` (or move to a
   stable release and re-check), and pin Mathlib in the lakefile:
   `require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "816ff4582a01b10567d1d4ecb10be7c4ff92aab4"`.
   Remove the duplicate `lakefile.toml`.
4. **One commit.** Merge the content of branches #34 (`research/sharpen-guard-2`), #35
   (`research/cap-bracket`) and #38 (`research/digit-structure`) into a single tagged commit,
   e.g. `v1.0-paper`, and cite that commit in Table 2 of the paper.
5. **Docstrings.** Fix stale text: `MahlerSharp7b` still says "Round-6 … 2^-1720001"; remove
   internal jargon ("Round 7b", "P-BBP-01", "H-04") in favour of the paper's terminology.
6. **Names.** Rename to Mathlib style where cheap, e.g. `bbp_digit_all_n_mu570b` →
   `bbpDigit_eq_of_guard_ge`, `MahlerSharp7b.pi_pow16_measure7` → `Real.pi_pow16_irrationality_measure`;
   keep deprecated aliases for the old names, and update Table 2.
7. **CI axiom report.** A GitHub Action that builds the closure and runs `#print axioms` on every
   theorem in Table 2, failing unless the output is exactly `propext, Classical.choice, Quot.sound`
   and there is no `sorryAx` or `Lean.ofReduceBool` (i.e. no `native_decide`). Publish the report
   as a build artifact.
8. **README** with build instructions, the expected build time for the `decide +kernel`
   certificate files, and a link to the paper.
