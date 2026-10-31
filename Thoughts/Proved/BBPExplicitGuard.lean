/-
  Explicit-guard digit certificate for π: the honest all-`n` statement (2026-09-30).

  The repo's capped certificate (`bbpCertFloor`, `bbpGuardAgrees`, `bbpHexDigitCert`) picks the
  guard depth `g = bbpCertGuard n ≤ 68` by a bounded search, so `∀ n, bbpGuardAgrees n` is false
  (`not_forall_bbpGuardAgrees`, `BBPGuardCap.lean`). Here the guard depth `g` is an explicit
  parameter instead:

  * `bbpCertFloorAt n g := bbpGuardedLo n g`, `bbpCertDigitAt n g := bbpCertFloorAt n g % 16`
    (the real guarded-bracket definitions `(S − E)/16^g`, `(S + E)/16^g` of `BBPTail.lean`);
  * `BBPGuardAgreesAt n g :↔ bbpGuardedLo n g = bbpGuardedHi n g` (decidable, natural numbers only).

  Proved unconditionally (H-04 = `bbpSeries_eq_pi`, no hypotheses):
  * soundness: `BBPGuardAgreesAt n g → ⌊16^n·π⌋ = bbpCertFloorAt n g` and
    `bbpCertDigitAt n g = bbpHexDigitReal n` (the `n`-th hex digit, `d_0 = 3`);
  * `bbp_explicit_guard_all_n : ∀ n, ∃ g, BBPGuardAgreesAt n g ∧ floor ∧ digit` (from
    `exists_guard_agrees`, which uses `irrational_pi`);
  * the capped certificate is the special case `g = bbpCertGuard n`
    (`bbpGuardAgrees_iff_at`, `bbpCertFloor_eq_at`, `bbpHexDigitCert_eq_at`), and the old
    `n ≤ 300` / `n ≤ 1000` theorems are re-derived from the new ones.

  NOT proved, and not claimed:
  * **No bound on `g` in terms of `n`.** The `g` in the all-`n` theorem is existential. A bound
    like `g ≤ C·n + C'` would follow from an effective irrationality measure of π with explicit
    constants (not in Mathlib; not attempted). Equivalently, `g(n)` is governed by the length of
    the run of hex `0`s / `F`s of π after position `n`.
  * Nothing about normality of π.
  * `PBBP01General` (the capped statement `∀ n, bbp_hex_digit n = bbpHexDigitReal n`) is still
    not proved (and not refuted); its route via `∀ n, bbpGuardAgrees n` is refuted. The
    statement proved here is the explicit-guard one, `PBBP01ExplicitGuard`.
-/
import Thoughts.Proved.BBPPiIdentity
import Thoughts.Proved.BBPGuarded
import Thoughts.Proved.BBPSpigot
import Thoughts.Proved.BBPGuardExists
import Thoughts.Proved.BBPGuardedCerts
import Thoughts.Proved.BBPDigitsUnconditional
import Thoughts.Proved.BBPGuardedCertsExt
import Thoughts.Proved.BBPDigitsUnconditionalExt

namespace FinitistProved

open Real

/-! ### Definitions (explicit guard depth) -/

/-- Certified value of `⌊16^n·π⌋` at guard depth `g`: the lower end `(S − E)/16^g` of the
guarded bracket. Exact exactly when `BBPGuardAgreesAt n g` holds (soundness below). -/
def bbpCertFloorAt (n g : ℕ) : ℕ := bbpGuardedLo n g

/-- Certified hex digit at position `n` (`d_0 = 3`) at guard depth `g`. -/
def bbpCertDigitAt (n g : ℕ) : ℕ := bbpCertFloorAt n g % 16

/-- The two guarded bracket ends coincide at depth `g` (a check on natural numbers). -/
def BBPGuardAgreesAt (n g : ℕ) : Prop := bbpGuardedLo n g = bbpGuardedHi n g

instance (n g : ℕ) : Decidable (BBPGuardAgreesAt n g) :=
  Nat.decEq (bbpGuardedLo n g) (bbpGuardedHi n g)

/-- Digit correctness at an explicit depth: the certificate digit is the true `n`-th hex digit
of π. -/
def BBPDigitCorrectAt (n g : ℕ) : Prop := bbpCertDigitAt n g = bbpHexDigitReal n

/-- **P-BBP-01, explicit-guard form:** every position `n` has *some* guard depth `g` at which the
bracket collapses and the certificate digit is the true digit. The depth is existential; this
does not bound `g` in terms of `n` and says nothing about normality. -/
def PBBP01ExplicitGuard : Prop := ∀ n, ∃ g, BBPGuardAgreesAt n g ∧ BBPDigitCorrectAt n g

/-! ### (a) Soundness -/

/-- Series version (no π needed): agreement at depth `g` pins `⌊16^n·bbpSeries⌋`. -/
theorem BBPGuardAgreesAt.floor_series {n g : ℕ} (h : BBPGuardAgreesAt n g) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ = (bbpCertFloorAt n g : ℤ) :=
  bbpGuarded_floor_eq n g h

/-- **Soundness (floor):** if the bracket ends agree at depth `g`, the certificate floor is
exactly `⌊16^n·π⌋`. Unconditional (uses H-04). -/
theorem BBPGuardAgreesAt.floor_pi {n g : ℕ} (h : BBPGuardAgreesAt n g) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) := by
  rw [← bbpSeries_eq_pi]; exact h.floor_series

/-- Two-sided bracket on `16^n·π` from agreement at depth `g`. -/
theorem BBPGuardAgreesAt.bracket_pi {n g : ℕ} (h : BBPGuardAgreesAt n g) :
    (bbpCertFloorAt n g : ℝ) ≤ (16 : ℝ) ^ n * Real.pi ∧
      (16 : ℝ) ^ n * Real.pi < (bbpCertFloorAt n g : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := bbpGuarded_bracket n g
  rw [bbpSeries_eq_pi] at h1 h2
  have h' : bbpGuardedHi n g = bbpCertFloorAt n g := h.symm
  rw [h'] at h2
  exact ⟨h1, h2⟩

/-- **Soundness (digit):** if the bracket ends agree at depth `g`, the certificate hex digit is
the true `n`-th hex digit of π (`d_0 = 3`, so `n = 1` gives `2`). Unconditional. -/
theorem BBPGuardAgreesAt.digit_pi {n g : ℕ} (h : BBPGuardAgreesAt n g) :
    bbpCertDigitAt n g = bbpHexDigitReal n := by
  unfold bbpCertDigitAt bbpHexDigitReal
  rw [h.floor_pi]
  simp

theorem BBPGuardAgreesAt.digitCorrect {n g : ℕ} (h : BBPGuardAgreesAt n g) :
    BBPDigitCorrectAt n g := h.digit_pi

/-- Any two agreeing depths certify the same floor and the same digit. -/
theorem certFloorAt_eq_of_agree {n g g' : ℕ} (h : BBPGuardAgreesAt n g)
    (h' : BBPGuardAgreesAt n g') : bbpCertFloorAt n g = bbpCertFloorAt n g' := by
  have := h.floor_pi.symm.trans h'.floor_pi
  exact_mod_cast this

/-! ### (b) The honest all-`n` theorem -/

/-- **All `n`, explicit guard (unconditional):** for every `n` there is a guard depth `g` such that
the bracket ends agree at `g`, the certificate floor is `⌊16^n·π⌋`, and the certificate digit is
the true `n`-th hex digit of π. The depth `g` is existential — no bound in terms of `n` is
proved (that would need an effective irrationality measure of π). -/
theorem bbp_explicit_guard_all_n (n : ℕ) :
    ∃ g : ℕ, BBPGuardAgreesAt n g ∧ ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
      bbpCertDigitAt n g = bbpHexDigitReal n := by
  obtain ⟨g, hg⟩ := exists_guard_agrees n
  have h : BBPGuardAgreesAt n g := hg
  exact ⟨g, h, h.floor_pi, h.digit_pi⟩

theorem bbp_explicit_guard_all_n' : ∀ n : ℕ, ∃ g : ℕ, BBPGuardAgreesAt n g ∧
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧ bbpCertDigitAt n g = bbpHexDigitReal n :=
  bbp_explicit_guard_all_n

/-- The explicit-guard form of P-BBP-01 holds for all `n` (existential `g`). -/
theorem PBBP01ExplicitGuard_proved : PBBP01ExplicitGuard := fun n => by
  obtain ⟨g, h, -, hd⟩ := bbp_explicit_guard_all_n n
  exact ⟨g, h, hd⟩

/-! ### (c) Decidable check; relation to the capped certificate -/

/-- `BBPGuardAgreesAt n g` is decidable (instance above), so for concrete `(n, g)` it is closed
by kernel `decide`; a witness certifies the true hex digit via `digit_pi`. -/
theorem BBPGuardAgreesAt.iff_decide (n g : ℕ) :
    BBPGuardAgreesAt n g ↔ (decide (BBPGuardAgreesAt n g) = true) := (decide_eq_true_iff).symm

/-- Bridge: the capped agreement check is the explicit one at `g = bbpCertGuard n`. -/
theorem bbpGuardAgrees_iff_at (n : ℕ) :
    bbpGuardAgrees n ↔ BBPGuardAgreesAt n (bbpCertGuard n) := Iff.rfl

/-- Bridge: the capped certificate floor is the explicit one at `g = bbpCertGuard n`. -/
theorem bbpCertFloor_eq_at (n : ℕ) : bbpCertFloor n = bbpCertFloorAt n (bbpCertGuard n) := rfl

/-- Bridge: the capped certificate digit is the explicit one at `g = bbpCertGuard n`. -/
theorem bbpHexDigitCert_eq_at (n : ℕ) :
    bbpHexDigitCert n = bbpCertDigitAt n (bbpCertGuard n) := rfl

/-- Old general digit statement for the capped certificate, derived from the new soundness. -/
theorem BBPSpigotDigitCorrect_of_guardAt {n : ℕ} (h : BBPGuardAgreesAt n (bbpCertGuard n)) :
    BBPSpigotDigitCorrect n := h.digit_pi

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

/-! ### Worked examples (kernel `decide`, no `native_decide`) -/

theorem guardAgreesAt_0_2 : BBPGuardAgreesAt 0 2 := by decide +kernel
theorem guardAgreesAt_1_2 : BBPGuardAgreesAt 1 2 := by decide +kernel
theorem guardAgreesAt_20_2 : BBPGuardAgreesAt 20 2 := by decide +kernel
theorem guardAgreesAt_100_3 : BBPGuardAgreesAt 100 3 := by decide +kernel
theorem guardAgreesAt_1000_4 : BBPGuardAgreesAt 1000 4 := by decide +kernel

/-- `d_20 = 9` (π = 3.243F6A8885A308D313198A2E…₁₆; the 20th hex digit after the point is `9`),
certified by `BBPGuardAgreesAt 20 2` + soundness. -/
theorem bbpHexDigitReal_twenty_explicit : bbpHexDigitReal 20 = 9 := by
  rw [← guardAgreesAt_20_2.digit_pi]; decide +kernel

theorem bbpHexDigitReal_hundred_explicit : bbpHexDigitReal 100 = 12 := by
  rw [← guardAgreesAt_100_3.digit_pi]; decide +kernel

theorem bbpHexDigitReal_thousand_explicit : bbpHexDigitReal 1000 = 3 := by
  rw [← guardAgreesAt_1000_4.digit_pi]; decide +kernel

end FinitistProved
