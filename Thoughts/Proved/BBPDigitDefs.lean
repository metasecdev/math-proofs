/-
  BBP digit definitions shared by the guarded-certificate files.

  Provenance: extracted from `Thoughts/Proved/Normality.lean` of
  metasecdev/irrational-gap-mobius @ ad5468ae8611c352071e3b3de706989c3ae65bfe.
  Only the π / BBP digit definitions were kept: `bbpHexDigitCert`, `bbp_hex_digit`,
  `bbpHexDigitUnguarded`, `piHexDigit`, `piGapSeq`, `bbpIntHeadSum`, `BBPIntHeadCorrect`.
  Declarations of the source file that served other programmes (the opaque `gapSeq`,
  the synthetic `i % 3` sequence and its mod-3 lemmas, and the legacy refuted
  equidistribution statement) are not part of this repository.

  No `sorry`, no axioms, no `native_decide` in this file.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Thoughts.Proved.BBPTail

namespace FinitistProved

open Real Nat Finset

/-! ### Certificate hex digit (corrected) -/

/--
  Certificate hex digit at position `n`: `bbpCertFloor n % 16`, where `bbpCertFloor n`
  is the guarded spigot floor certificate for `⌊16^n · π⌋` (`d_0 = 3`).
  Proved equal to the true digit `⌊16^n·π⌋ mod 16` whenever the decidable guard check
  `bbpGuardAgrees n` passes, conditional only on `BBPPiEqualsSeries`
  (`BBPSpigotDigitCorrect_of_guard` in `BBPSpigot.lean`).
-/
def bbpHexDigitCert (n : Nat) : Nat := bbpCertFloor n % 16

/-- Proof/runtime alias: total certificate digit (no partiality). -/
abbrev bbp_hex_digit (n : Nat) : Nat := bbpHexDigitCert n

/--
  Low hex digit of the **unguarded** corrected sum `∑_{k < n+51} bbp_term k n`.
  Kept for comparison only: the unguarded sum overshoots `⌊16^n·π⌋` by a few units, so
  this is usually *not* the `n`-th digit.
-/
def bbpHexDigitUnguarded (n : Nat) : Nat :=
  ((∑ k ∈ Finset.range (n + 51), bbp_term k n) % 16)

/-! ### True hex digits of π -/

/-- True `n`-th hex digit of π: `⌊16^n · π⌋ mod 16` (`d_0 = 3`). Noncomputable. -/
noncomputable def piHexDigit (n : Nat) : Nat := (⌊(16 : ℝ) ^ n * Real.pi⌋).toNat % 16

open Classical in
/--
  Run-length from `start` to the next true π hex digit `1` (`0` if there is none; whether
  digit `1` occurs infinitely often is itself open).
-/
noncomputable def piGapSeq (start : Nat) : Nat :=
  if h : ∃ k, piHexDigit (start + k) = 1 then Nat.find h else 0

/-! ### Integer head sum -/

/-- Integer head sum `∑_{k≤n} bbp_term k n` (corrected term; unguarded). -/
def bbpIntHeadSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), bbp_term k n

/--
  Legacy subgoal: unguarded integer head equals `⌊bbpScaledHead n⌋`. Generally FALSE for
  `n ≥ 1` (the floors overshoot; see `bbpSpigotIntHeadSum_gt_scaledHead_*`). Superseded by
  the guarded certificate (`BBPGuarded.lean`). Kept as a named Prop only.
-/
def BBPIntHeadCorrect (n : Nat) : Prop :=
  (bbpIntHeadSum n : ℝ) = ⌊bbpScaledHead n⌋

theorem bbp_hex_digit_eq_cert (n : Nat) : bbp_hex_digit n = bbpHexDigitCert n := rfl

end FinitistProved
