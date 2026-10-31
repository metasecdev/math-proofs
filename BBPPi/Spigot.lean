import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import BBPPi.Algebra
import BBPPi.Tail
import BBPPi.Series
import BBPPi.Guarded
import BBPPi.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.StarOrdered

/-!
# The certificate digit versus the true hex digit of π

## Main definitions

* `bbpHexDigitReal n`: the true `n`-th hex digit `⌊16^n·π⌋ mod 16` (`d_0 = 3`).
* `BBPSpigotDigitCorrect n`: the certificate digit `bbp_hex_digit n` equals `bbpHexDigitReal n`.
* `PBBP01General`: `∀ n, BBPSpigotDigitCorrect n` for the *capped* certificate. This statement is
  false (`not_PBBP01General` in the optional library `BBPPiCerts.CapRefutation`); it is kept as a
  named `Prop` because the capped results are stated with it.

## Main results

* `BBPSpigotDigitCorrect_of_guard`: if the decidable guard check `bbpGuardAgrees n` passes, then
  `BBPSpigotDigitCorrect n`, given `BBPPiEqualsSeries` (proved as `bbpSeries_eq_pi`).
* `bbpHexDigitReal_zero`: `d_0 = 3`.

Note: `bbpHexDigitNextReal n = ⌊16·{16^n π}⌋ mod 16` is the digit at position `n + 1`.
-/

namespace BBPPi

open Real Nat

/-! ### Real π hex-digit target -/

/-- Fractional part `x - ⌊x⌋`. -/
noncomputable def bbpFracPart (x : ℝ) : ℝ := x - ⌊x⌋

/-- Fractional part of `16^n · π`. -/
noncomputable def bbpHexShiftReal (n : Nat) : ℝ := bbpFracPart ((16 : ℝ) ^ n * Real.pi)

/--
  `n`-th hexadecimal digit of π: `⌊16^n · π⌋ mod 16`, so `d_0 = 3`, `d_1 = 2`, `d_2 = 4`, …
  (π = 3.243F6A88…₁₆). Equal to `piHexDigit n` from `BBPPi.Defs`.
-/
noncomputable def bbpHexDigitReal (n : Nat) : Nat :=
  (⌊(16 : ℝ) ^ n * Real.pi⌋).toNat % 16

/--
  `⌊16 · {16^n π}⌋ mod 16` — this is the digit at position `n + 1`, **not** `n`.
  (This was the pre-audit definition of `bbpHexDigitReal`, the source of the off-by-one.)
-/
noncomputable def bbpHexDigitNextReal (n : Nat) : Nat :=
  (Int.toNat ⌊16 * bbpHexShiftReal n⌋) % 16

theorem bbpHexDigitReal_eq_piHexDigit (n : Nat) : bbpHexDigitReal n = piHexDigit n := rfl

/-- Sanity check of the digit convention: `d_0 = 3`. -/
theorem bbpHexDigitReal_zero : bbpHexDigitReal 0 = 3 := by
  simp [bbpHexDigitReal, Real.floor_pi_eq_three]

theorem bbpHexShiftReal_nonneg (n : Nat) : 0 ≤ bbpHexShiftReal n := by
  unfold bbpHexShiftReal bbpFracPart
  have h := Int.floor_le ((16 : ℝ) ^ n * Real.pi)
  linarith

theorem bbpHexShiftReal_lt_one (n : Nat) : bbpHexShiftReal n < 1 := by
  unfold bbpHexShiftReal bbpFracPart
  have h := Int.lt_floor_add_one ((16 : ℝ) ^ n * Real.pi)
  linarith

theorem bbpHexDigitReal_lt_sixteen (n : Nat) : bbpHexDigitReal n < 16 := by
  unfold bbpHexDigitReal
  exact Nat.mod_lt _ (by decide : 0 < 16)

/-! ### Statements -/

/--
  **digit correctness at `n`:** the certificate digit equals the true `n`-th hex digit of π.
  (Same statement text as before the audit; both sides are now corrected.)
-/
def BBPSpigotDigitCorrect (n : Nat) : Prop :=
  bbp_hex_digit n = bbpHexDigitReal n

/--
  **digit correctness, general `n` (capped) — REFUTED** by `not_PBBP01General`
  (`BBPPiCerts.CapRefutation`: wrong digit for every `n ∈ [2^272, 2^273]`).
  The explicit-guard form is proved for all `n`. Historically: would follow from `BBPPiEqualsSeries` plus
  `∀ n, bbpGuardAgrees n`; but the latter is FALSE as defined (the guard search is capped at
  `g ≤ 68`; `not_forall_bbpGuardAgrees` in `BBPPiCerts.GuardCap`), so this route cannot prove it.
-/
def PBBP01General : Prop := ∀ n, BBPSpigotDigitCorrect n

/--
  **Series split (proved):** scaled split for the formal BBP series `bbpSeries`.
-/
def BBPScaledPiSplitSeries (n : Nat) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + ε

/--
  **π split:** scaled-π split; single analytic gate `BBPPiEqualsSeries`.
-/
def BBPScaledPiSplit (n : Nat) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * Real.pi = bbpScaledHead n + ε

/--
  **Truncated split (proved):** finite `M`-term scaled tail split.
-/
def BBPScaledTruncSplit (n M : Nat) : Prop :=
  bbpScaledHead n + bbpScaledTailTrunc n M =
    (16 : ℝ) ^ n * (bbpHead n + bbpTailTrunc n M)

/-! ### Proved series split; π via `BBPPiEqualsSeries` -/

theorem bbpScaledPiSplit_series_holds (n : Nat) : BBPScaledPiSplitSeries n := by
  rcases bbpScaledPiSplit_series n with ⟨ε, hε0, hε1, hEq⟩
  exact ⟨ε, hε0, hε1, hEq⟩

theorem bbpScaledPiSplit_holds (n : Nat) (h : BBPPiEqualsSeries) : BBPScaledPiSplit n := by
  rcases bbpScaledPiSplit_of_pi_eq_series n h with ⟨ε, hε0, hε1, hEq⟩
  exact ⟨ε, hε0, hε1, hEq⟩

theorem bbpScaledPiSplit_tail (n : Nat) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + ε ∧
      ε = bbpScaledTail n :=
  ⟨bbpScaledTail n, bbpScaledTail_nonneg n, bbpScaledTail_lt_one n,
    bbpSeries_scaled_split n, rfl⟩

theorem bbpScaledPiSplit_pi_tail (n : Nat) (h : BBPPiEqualsSeries) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * Real.pi = bbpScaledHead n + ε ∧
      ε = bbpScaledTail n := by
  rcases bbpScaledPiSplit_tail n with ⟨ε, hε0, hε1, hEq, hεdef⟩
  refine ⟨ε, hε0, hε1, ?_, hεdef⟩
  rw [← h]
  exact hEq

/-! ### Hex digits of the formal series -/

/-- `n`-th hex digit of `bbpSeries`: `⌊16^n · bbpSeries⌋ mod 16`. -/
noncomputable def bbpHexDigitRealSeries (n : Nat) : Nat :=
  (⌊(16 : ℝ) ^ n * bbpSeries⌋).toNat % 16

/-- Fractional part of `16^n · bbpSeries`. -/
noncomputable def bbpHexShiftSeries (n : Nat) : ℝ :=
  bbpFracPart ((16 : ℝ) ^ n * bbpSeries)

/-- `⌊16 · {16^n · bbpSeries}⌋ mod 16` — digit `n + 1` of the series (pre-audit meaning). -/
noncomputable def bbpHexDigitNextSeries (n : Nat) : Nat :=
  (Int.toNat ⌊16 * bbpHexShiftSeries n⌋) % 16

theorem bbpHexDigitReal_eq_series_of (n : Nat) (h : BBPPiEqualsSeries) :
    bbpHexDigitReal n = bbpHexDigitRealSeries n := by
  unfold bbpHexDigitReal bbpHexDigitRealSeries
  rw [h]

theorem bbpHexDigitNextReal_eq_series_of (n : Nat) (h : BBPPiEqualsSeries) :
    bbpHexDigitNextReal n = bbpHexDigitNextSeries n := by
  unfold bbpHexDigitNextReal bbpHexDigitNextSeries bbpHexShiftReal bbpHexShiftSeries bbpFracPart
  rw [h]

/-! ### digit correctness via the guarded certificate (proved, conditional on the BBP identity for π) -/

/-- Series version, **no π hypothesis:** guard check ⇒ certificate digit = series digit. -/
theorem bbpHexDigitCert_eq_series_of_guard (n : Nat) (h : bbpGuardAgrees n) :
    bbp_hex_digit n = bbpHexDigitRealSeries n := by
  unfold bbpHexDigitRealSeries
  rw [bbpCertFloor_eq_floor_series n h]
  simp [bbp_hex_digit, bbpHexDigitCert]

/--
  **digit correctness at `n` (proved from the guard check + the BBP identity):**
  `bbpGuardAgrees n → BBPPiEqualsSeries → BBPSpigotDigitCorrect n`.
-/
theorem BBPSpigotDigitCorrect_of_guard (hπ : BBPPiEqualsSeries) (n : Nat)
    (h : bbpGuardAgrees n) : BBPSpigotDigitCorrect n := by
  unfold BBPSpigotDigitCorrect
  rw [bbpHexDigitReal_eq_series_of n hπ]
  exact bbpHexDigitCert_eq_series_of_guard n h

/-- General digit correctness reduces to the BBP identity plus the guard check at every `n` (the guard hypothesis is
false, and `PBBP01General` itself is refuted by `not_PBBP01General`). -/
theorem PBBP01General_of_guard (hπ : BBPPiEqualsSeries) (h : ∀ n, bbpGuardAgrees n) :
    PBBP01General :=
  fun n => BBPSpigotDigitCorrect_of_guard hπ n (h n)

theorem bbpHexShiftSeries_eq_frac_of_split (n : Nat) (ε : ℝ)
    (_hε : 0 ≤ ε) (_hε1 : ε < 1)
    (hEq : (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + ε) :
    bbpHexShiftSeries n = bbpFracPart (bbpScaledHead n + ε) := by
  unfold bbpHexShiftSeries bbpFracPart
  rw [hEq]

/-! ### Proved truncated scaled split -/

theorem bbp_scaled_trunc_split (n M : Nat) :
    bbpScaledHead n + bbpScaledTailTrunc n M =
      (16 : ℝ) ^ n * (bbpHead n + bbpTailTrunc n M) :=
  bbpScaledHead_plus_tailTrunc n M

theorem bbp_scaled_trunc_split_holds (n M : Nat) : BBPScaledTruncSplit n M :=
  bbp_scaled_trunc_split n M

theorem bbpScaledTailTrunc_lt_pow (n M : Nat) (hM : 0 < M) :
    bbpScaledTailTrunc n M < (16 : ℝ) ^ n := by
  unfold bbpScaledTailTrunc
  have h16 : 0 < (16 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 16) n
  have ht := bbpTailTrunc_lt_one n M hM
  nlinarith [ht, h16]

theorem bbp_tail_trunc_nonneg_and_lt_one (n M : Nat) (hM : 0 < M) :
    0 ≤ (bbp_tail n M : ℝ) ∧ (bbp_tail n M : ℝ) < 1 := by
  have h := bbp_tail_bound n M hM
  exact ⟨mod_cast h.1, mod_cast h.2⟩

theorem bbp_hex_shift_real_eq_frac_of_split (n : Nat) (ε : ℝ)
    (_hε : 0 ≤ ε) (_hε1 : ε < 1)
    (hEq : (16 : ℝ) ^ n * Real.pi = bbpScaledHead n + ε) :
    bbpHexShiftReal n = bbpFracPart (bbpScaledHead n + ε) := by
  unfold bbpHexShiftReal bbpFracPart
  rw [hEq]

/-! ### Helpers -/

theorem bbp_hex_digit_real_in_range (n : Nat) :
    bbpHexDigitReal n < 16 := bbpHexDigitReal_lt_sixteen n

/-- If digit correctness holds at `n`, the certificate and real digits agree. -/
theorem bbp_hex_digit_eq_real_of (n : Nat) (h : BBPSpigotDigitCorrect n) :
    bbp_hex_digit n = bbpHexDigitReal n := h

/-- Digit `n + 1` from the scaled split (fractional extraction; pre-audit target). -/
theorem bbpHexDigitNextReal_eq_floor_shift_of_split (n : Nat) (ε : ℝ)
    (_hε : 0 ≤ ε) (_hε1 : ε < 1)
    (hEq : (16 : ℝ) ^ n * Real.pi = bbpScaledHead n + ε) :
    bbpHexDigitNextReal n =
      (Int.toNat ⌊16 * bbpFracPart (bbpScaledHead n + ε)⌋) % 16 := by
  unfold bbpHexDigitNextReal bbpHexShiftReal bbpFracPart
  rw [hEq]

end BBPPi
