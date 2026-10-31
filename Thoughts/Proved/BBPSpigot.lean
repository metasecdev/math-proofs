/-
  BBP digit bridge: certificate digit vs the true hex digit of π (P-BBP-01..04).

  **2026-09 correctness audit.**
  * `bbpHexDigitReal n` is now the true `n`-th hex digit `⌊16^n·π⌋ mod 16` (`d_0 = 3`,
    `bbpHexDigitReal_zero`). The former definition `⌊16·{16^n·π}⌋ mod 16` is digit `n+1`;
    it is kept as `bbpHexDigitNextReal`.
  * `BBPSpigotDigitCorrect n` (P-BBP-01 at `n`) therefore now compares the certificate with
    the digit at the *same* position.
  * Proved: `BBPSpigotDigitCorrect_of_guard` — if the decidable guard check
    `bbpGuardAgrees n` passes, then `BBPSpigotDigitCorrect n`, conditional only on the
    stated hypothesis `BBPPiEqualsSeries` (H-04). Concrete `n` are in `BBPGuardedCerts.lean`.
  * P-BBP-01 for general `n` (`PBBP01General`) remains OPEN.
  * Removed: the cert-gap chain and Tier-1 cluster witnesses (they certified chance
    agreements with digit `n+1`, and four of their `hz` numerals were false).

  Provenance: metasecdev/irrational-gap-mobius @ ad5468ae8611c352071e3b3de706989c3ae65bfe,
  with the legacy P-BBP-03/P-BBP-04 statements (and their imports) removed; the digit
  definitions formerly in `Normality.lean` now come from `BBPDigitDefs.lean`.

  No `sorry`, no axioms, no `native_decide` in this file.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Thoughts.Proved.BBPAlgebra
import Thoughts.Proved.BBPTail
import Thoughts.Proved.BBPSeries
import Thoughts.Proved.BBPIntDigit
import Thoughts.Proved.BBPGuarded
import Thoughts.Proved.BBPDigitDefs

namespace FinitistProved

open Real Nat

/-! ### Real π hex-digit target -/

/-- Fractional part `x - ⌊x⌋`. -/
noncomputable def bbpFracPart (x : ℝ) : ℝ := x - ⌊x⌋

/-- Fractional part of `16^n · π`. -/
noncomputable def bbpHexShiftReal (n : Nat) : ℝ := bbpFracPart ((16 : ℝ) ^ n * Real.pi)

/--
  `n`-th hexadecimal digit of π: `⌊16^n · π⌋ mod 16`, so `d_0 = 3`, `d_1 = 2`, `d_2 = 4`, …
  (π = 3.243F6A88…₁₆). Corrected 2026-09; equal to `piHexDigit n` from `BBPDigitDefs.lean`.
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

/-! ### Goals -/

/--
  **P-BBP-01 at `n`:** the certificate digit equals the true `n`-th hex digit of π.
  (Same statement text as before the audit; both sides are now corrected.)
-/
def BBPSpigotDigitCorrect (n : Nat) : Prop :=
  bbp_hex_digit n = bbpHexDigitReal n

/--
  **P-BBP-01, general `n` — OPEN.** Would follow from `BBPPiEqualsSeries` plus
  `∀ n, bbpGuardAgrees n`; but the latter is FALSE as defined (the guard search is capped at
  `g ≤ 68`; `not_forall_bbpGuardAgrees` in `BBPGuardCap.lean`), so this route cannot prove it.
  See `docs/PBBP01_EXTENSION_ANALYSIS.md`.
-/
def PBBP01General : Prop := ∀ n, BBPSpigotDigitCorrect n

/--
  **P-BBP-02 (series, proved):** scaled split for the formal BBP series `bbpSeries`.
-/
def BBPScaledPiSplitSeries (n : Nat) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + ε

/--
  **P-BBP-02 (π):** scaled-π split; single analytic gate `BBPPiEqualsSeries`.
-/
def BBPScaledPiSplit (n : Nat) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * Real.pi = bbpScaledHead n + ε

/--
  **P-BBP-02a (truncated, proved):** finite `M`-term scaled tail split.
-/
def BBPScaledTruncSplit (n M : Nat) : Prop :=
  bbpScaledHead n + bbpScaledTailTrunc n M =
    (16 : ℝ) ^ n * (bbpHead n + bbpTailTrunc n M)

/-! ### P-BBP-02: proved series split; π via `BBPPiEqualsSeries` -/

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

/-! ### P-BBP-01 via the guarded certificate (proved, conditional on H-04 for π) -/

/-- Series version, **no π hypothesis:** guard check ⇒ certificate digit = series digit. -/
theorem bbpHexDigitCert_eq_series_of_guard (n : Nat) (h : bbpGuardAgrees n) :
    bbp_hex_digit n = bbpHexDigitRealSeries n := by
  unfold bbpHexDigitRealSeries
  rw [bbpCertFloor_eq_floor_series n h]
  simp [bbp_hex_digit, bbpHexDigitCert]

/--
  **P-BBP-01 at `n` (proved from the guard check + H-04):**
  `bbpGuardAgrees n → BBPPiEqualsSeries → BBPSpigotDigitCorrect n`.
-/
theorem BBPSpigotDigitCorrect_of_guard (hπ : BBPPiEqualsSeries) (n : Nat)
    (h : bbpGuardAgrees n) : BBPSpigotDigitCorrect n := by
  unfold BBPSpigotDigitCorrect
  rw [bbpHexDigitReal_eq_series_of n hπ]
  exact bbpHexDigitCert_eq_series_of_guard n h

/-- General P-BBP-01 reduces to H-04 plus the guard check at every `n` (both open). -/
theorem PBBP01General_of_guard (hπ : BBPPiEqualsSeries) (h : ∀ n, bbpGuardAgrees n) :
    PBBP01General :=
  fun n => BBPSpigotDigitCorrect_of_guard hπ n (h n)

theorem bbpHexShiftSeries_eq_frac_of_split (n : Nat) (ε : ℝ)
    (_hε : 0 ≤ ε) (_hε1 : ε < 1)
    (hEq : (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + ε) :
    bbpHexShiftSeries n = bbpFracPart (bbpScaledHead n + ε) := by
  unfold bbpHexShiftSeries bbpFracPart
  rw [hEq]

/-! ### P-BBP-02a: proved truncated scaled split -/

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

/-- If P-BBP-01 holds at `n`, the certificate and real digits agree. -/
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

/-! ### Unguarded sums: one-sided facts (kept, correctly labelled) -/

/--
  Digit `n + 1` of the series from the unguarded weighted spigot gap (true, but this is the
  *next* digit; it is not a certificate for digit `n`).
-/
theorem bbpHexDigitNextSeries_eq_spigot_gap_floor_of_upper (n : Nat)
    (h : BBPSpigotIntSeriesBracketUpper n) :
    bbpHexDigitNextSeries n =
      bbpHexDigitOfGapFloor
        ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋ := by
  simpa [bbpHexDigitNextSeries, bbpHexShiftSeries, bbpFracPart] using
    bbpHexDigitSeries_eq_spigot_gap_floor_of_upper n h

theorem bbpIntGapBracket_iff_series_bracket (n : Nat) :
    BBPIntGapBracket n ↔ BBPIntSeriesBracket n :=
  bbpIntGapBracket_iff_bracket n

theorem bbpIntSeriesBracket_upper_of_head_budget (n : Nat)
    (hTail : BBPIntTailCertBound n)
    (hHead : bbpIntHeadGap n < 1 - bbpIntTailGap n) :
    BBPIntSeriesBracketUpper n :=
  bbpIntSeriesBracket_upper_of_tail_budget n hTail (by
    simpa [bbpIntHeadGap_eq, bbpIntTailGap_eq] using hHead)

theorem bbpIntHeadGap_eq_frac_when_correct (n : Nat) (h : BBPIntHeadCorrect n) :
    bbpIntHeadGap n = bbpFracPart (bbpScaledHead n) := by
  unfold bbpIntHeadGap bbpFracPart BBPIntHeadCorrect at *
  rw [h]

end FinitistProved
