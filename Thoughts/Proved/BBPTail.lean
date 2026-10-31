/-
  BBP tail bounds (geometric-series proofs) and rational tail aligned with `bbpSummand`.
-/
import Mathlib
import Thoughts.Proved.BBPAlgebra

namespace FinitistProved

open Real Nat Finset

/-! ### Coefficient bounds -/

private lemma abs_sub_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : |x - y| ≤ x + y := by
  calc
    |x - y| = |x + -y| := by ring_nf
    _ ≤ |x| + |-y| := abs_add_le x (-y)
    _ = x + y := by rw [abs_of_nonneg hx, abs_neg, abs_of_nonneg hy]

private lemma abs_sub_sub_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    |x - y - z| ≤ x + y + z := by
  calc
    |x - y - z| ≤ |x - y| + |z| := by
      simpa [sub_eq_add_neg] using abs_add_le (x - y) (-z)
    _ ≤ x + y + z := by
      gcongr
      · exact abs_sub_nonneg hx hy
      · rw [abs_of_nonneg hz]

theorem bbpCoeff_abs_le (k : Nat) : |bbpCoeff k| ≤ 8 := by
  unfold bbpCoeff
  have hp1 : 0 ≤ (4 : ℝ) / (8 * k + 1) := div_nonneg (by norm_num) (by positivity)
  have hp2 : 0 ≤ (2 : ℝ) / (8 * k + 4) := div_nonneg (by norm_num) (by positivity)
  have hp3 : 0 ≤ (1 : ℝ) / (8 * k + 5) := div_nonneg (by norm_num) (by positivity)
  have hp4 : 0 ≤ (1 : ℝ) / (8 * k + 6) := div_nonneg (by norm_num) (by positivity)
  have h1 : 1 ≤ (8 * k + 1 : ℝ) := by linarith
  have h4 : 1 ≤ (8 * k + 4 : ℝ) := by linarith
  have h5 : 1 ≤ (8 * k + 5 : ℝ) := by linarith
  have h6 : 1 ≤ (8 * k + 6 : ℝ) := by linarith
  have hsub3 :
      |((4 : ℝ) / (8 * k + 1)) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5)| ≤
        (4 : ℝ) / (8 * k + 1) + (2 : ℝ) / (8 * k + 4) + (1 : ℝ) / (8 * k + 5) :=
    abs_sub_sub_nonneg hp1 hp2 hp3
  have hsub4 :
      |((4 : ℝ) / (8 * k + 1)) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5) -
          (1 : ℝ) / (8 * k + 6)| ≤
        |((4 : ℝ) / (8 * k + 1)) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5)| +
          (1 : ℝ) / (8 * k + 6) := by
    have h :=
      abs_add_le
        ((4 : ℝ) / (8 * k + 1) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5))
        (-(1 : ℝ) / (8 * k + 6))
    have habs : |(-1 : ℝ) / (8 * k + 6)| = (1 : ℝ) / (8 * k + 6) := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1), abs_of_pos (by positivity)]
    have hfix : (-1 : ℝ) / (8 * k + 6) = -((8 * k + 6 : ℝ)⁻¹) := by
      simp [neg_div, one_div]
    have hden : |(8 * k + 6 : ℝ)|⁻¹ = (8 * k + 6 : ℝ)⁻¹ := by
      rw [abs_of_nonneg (le_of_lt (by positivity : 0 < (8 * k + 6 : ℝ)))]
    simpa [sub_eq_add_neg, habs, hfix, hden] using h
  calc
    |((4 : ℝ) / (8 * k + 1)) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5) -
        (1 : ℝ) / (8 * k + 6)| ≤
        |((4 : ℝ) / (8 * k + 1)) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5)| +
            (1 : ℝ) / (8 * k + 6) := hsub4
    _ ≤ (4 : ℝ) / (8 * k + 1) + (2 : ℝ) / (8 * k + 4) + (1 : ℝ) / (8 * k + 5) +
          (1 : ℝ) / (8 * k + 6) := by
      linarith [hsub3]
    _ ≤ 4 + 2 + 1 + 1 := by
      gcongr
      · exact div_le_self (by norm_num : (0 : ℝ) ≤ 4) h1
      · exact div_le_self (by norm_num : (0 : ℝ) ≤ 2) h4
      · exact div_le_self (by norm_num : (0 : ℝ) ≤ 1) h5
      · exact div_le_self (by norm_num : (0 : ℝ) ≤ 1) h6
    _ = 8 := by norm_num

theorem bbpSummand_abs_le (k : Nat) : |bbpSummand k| ≤ 8 / (16 : ℝ) ^ k := by
  unfold bbpSummand
  have h := bbpCoeff_abs_le k
  have h16 : 0 < (16 : ℝ) ^ k := pow_pos (by norm_num : (0 : ℝ) < 16) k
  rw [abs_div, abs_of_pos h16]
  exact div_le_div_of_nonneg_right h (le_of_lt h16)

/-! ### Geometric helpers -/

private lemma geom_sum_range_lt (M : Nat) (hM : 0 < M) :
    (∑ j ∈ Finset.range M, (1 / (16 : ℝ)) ^ j) < 16 / 15 := by
  have hr : (1 / (16 : ℝ)) ≠ 1 := by norm_num
  have hr1 : (1 / (16 : ℝ)) < 1 := by norm_num
  have hM' : (1 / (16 : ℝ)) ^ M < 1 :=
    (pow_lt_one_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) (Nat.ne_of_gt hM)).mpr hr1
  rw [geom_sum_eq hr M]
  have hden : (1 / (16 : ℝ) - 1) < 0 := by norm_num
  have hnum : (1 / (16 : ℝ)) ^ M - 1 < 0 := by linarith
  rw [div_lt_iff_of_neg hden]
  have hRHS : (16 / 15 : ℝ) * (1 / 16 - 1) = -1 := by norm_num
  rw [hRHS]
  linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 16) M]

private lemma eight_div_pow_factor (n j : Nat) :
    (8 : ℝ) / ((16 : ℝ) ^ (n + 1) * (16 : ℝ) ^ j) =
      (8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j := by
  have hpow : (16 : ℝ) ^ (n + 1 + j) = (16 : ℝ) ^ (n + 1) * (16 : ℝ) ^ j := pow_add (16 : ℝ) (n + 1) j
  rw [← hpow, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, one_div_pow]
  ring

lemma summand_term_bound (n j : Nat) :
    bbpSummand (n + 1 + j) ≤ (8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j := by
  have hk := bbpSummand_abs_le (n + 1 + j)
  have hpow := pow_add (16 : ℝ) (n + 1) j
  have hk' : |bbpSummand (n + 1 + j)| ≤ 8 / ((16 : ℝ) ^ (n + 1) * (16 : ℝ) ^ j) := by
    simpa [hpow] using hk
  have hcast := eight_div_pow_factor n j
  linarith [le_abs_self (bbpSummand (n + 1 + j)), hk', hcast]

theorem bbpTailTrunc_lt_one (n M : Nat) (hM : 0 < M) : bbpTailTrunc n M < 1 := by
  unfold bbpTailTrunc
  have hterm :
      ∀ j ∈ Finset.range M,
        bbpSummand (n + 1 + j) ≤ (8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j :=
    fun j hj => summand_term_bound n j
  have hle :
      ∑ j ∈ Finset.range M, bbpSummand (n + 1 + j) ≤
        ∑ j ∈ Finset.range M, (8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j :=
    Finset.sum_le_sum hterm
  have hfactor :
      ∑ j ∈ Finset.range M, (8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j =
        (8 / (16 : ℝ) ^ (n + 1)) * ∑ j ∈ Finset.range M, (1 / (16 : ℝ)) ^ j := by
    rw [Finset.mul_sum]
  have hpow : (16 : ℝ) ≤ (16 : ℝ) ^ (n + 1) := by
    have h1 : (1 : ℝ) ≤ 16 := by norm_num
    simpa [one_pow] using le_self_pow₀ h1 (by omega : (n + 1) ≠ 0)
  have hmono : 8 / (16 : ℝ) ^ (n + 1) ≤ 8 / (16 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
    · positivity
    · exact hpow
  have hhead : (8 / (16 : ℝ)) * (16 / 15) < 1 := by norm_num
  have hbound :
      (8 / (16 : ℝ) ^ (n + 1)) * ∑ j ∈ Finset.range M, (1 / (16 : ℝ)) ^ j < 1 := by
    calc
      (8 / (16 : ℝ) ^ (n + 1)) * ∑ j ∈ Finset.range M, (1 / (16 : ℝ)) ^ j ≤
          (8 / (16 : ℝ)) * ∑ j ∈ Finset.range M, (1 / (16 : ℝ)) ^ j := by gcongr
      _ < (8 / (16 : ℝ)) * (16 / 15) := by
        gcongr
        exact geom_sum_range_lt M hM
      _ < 1 := hhead
  linarith [hle, hfactor, hbound]

/-! ### Nonnegativity -/

theorem bbpSummand_nonneg (k : Nat) : 0 ≤ bbpSummand k := by
  unfold bbpSummand bbpCoeff
  have hdom :
      (2 : ℝ) / (8 * k + 4) + (1 : ℝ) / (8 * k + 5) + (1 : ℝ) / (8 * k + 6) ≤
        (4 : ℝ) / (8 * k + 1) := by
    have h41 : (8 * k + 1 : ℝ) ≤ 8 * k + 4 := by linarith
    have h42 : (8 * k + 1 : ℝ) ≤ 8 * k + 5 := by linarith
    have h43 : (8 * k + 1 : ℝ) ≤ 8 * k + 6 := by linarith
    have ht2 : (2 : ℝ) / (8 * k + 4) ≤ (2 : ℝ) / (8 * k + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < (8 * k + 1 : ℝ)) h41
    have ht3 : (1 : ℝ) / (8 * k + 5) ≤ (1 : ℝ) / (8 * k + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < (8 * k + 1 : ℝ)) h42
    have ht4 : (1 : ℝ) / (8 * k + 6) ≤ (1 : ℝ) / (8 * k + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < (8 * k + 1 : ℝ)) h43
    have hsum :
        (2 : ℝ) / (8 * k + 4) + (1 : ℝ) / (8 * k + 5) + (1 : ℝ) / (8 * k + 6) ≤
          (2 : ℝ) / (8 * k + 1) + (1 : ℝ) / (8 * k + 1) + (1 : ℝ) / (8 * k + 1) := by
      linarith [ht2, ht3, ht4]
    have hsum' :
        (2 : ℝ) / (8 * k + 1) + (1 : ℝ) / (8 * k + 1) + (1 : ℝ) / (8 * k + 1) =
          (4 : ℝ) / (8 * k + 1) := by ring
    linarith [hsum, hsum']
  have hcoeff : 0 ≤ (4 : ℝ) / (8 * k + 1) - (2 : ℝ) / (8 * k + 4) - (1 : ℝ) / (8 * k + 5) -
      (1 : ℝ) / (8 * k + 6) := by linarith [hdom]
  exact div_nonneg hcoeff (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) k)

theorem bbpTailTrunc_nonneg (n M : Nat) : 0 ≤ bbpTailTrunc n M := by
  unfold bbpTailTrunc
  exact Finset.sum_nonneg fun j _ => bbpSummand_nonneg (n + 1 + j)

theorem bbpTailTrunc_bound (n M : Nat) (hM : 0 < M) :
    0 ≤ bbpTailTrunc n M ∧ bbpTailTrunc n M < 1 :=
  ⟨bbpTailTrunc_nonneg n M, bbpTailTrunc_lt_one n M hM⟩

/-! ### Rational tail (same scaling as `bbpSummand`) -/

/-- Rational BBP coefficient; casts to `bbpCoeff`. -/
def bbpCoeffQ (k : Nat) : ℚ :=
  (4 : ℚ) / (8 * k + 1) - (2 : ℚ) / (8 * k + 4) - (1 : ℚ) / (8 * k + 5) - (1 : ℚ) / (8 * k + 6)

@[simp] lemma bbpCoeffQ_coe (k : Nat) : (bbpCoeffQ k : ℝ) = bbpCoeff k := by
  simp [bbpCoeffQ, bbpCoeff]

/-- Finite rational tail ∑ `bbpCoeffQ (n+1+j) / 16^(n+1+j)` — aligns with `bbpTailTrunc`. -/
def bbp_tail (n : Nat) (M : Nat := 100) : ℚ :=
  ∑ j ∈ Finset.range M, bbpCoeffQ (n + 1 + j) / (16 : ℚ) ^ (n + 1 + j)

private lemma bbp_tail_term_coe (n j : Nat) :
    (↑(bbpCoeffQ (n + 1 + j) / (16 : ℚ) ^ (n + 1 + j)) : ℝ) = bbpSummand (n + 1 + j) := by
  rw [Rat.cast_div, bbpSummand, bbpCoeffQ_coe]
  norm_cast

@[simp] lemma bbp_tail_coe (n M : Nat) : (bbp_tail n M : ℝ) = bbpTailTrunc n M := by
  unfold bbp_tail bbpTailTrunc
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  exact bbp_tail_term_coe n j

theorem bbp_tail_nonneg (n : Nat) (M : Nat) : 0 ≤ bbp_tail n M := by
  suffices 0 ≤ (bbp_tail n M : ℝ) by exact_mod_cast this
  rw [bbp_tail_coe]
  exact bbpTailTrunc_nonneg n M

theorem bbp_tail_lt_one (n : Nat) (M : Nat) (hM : 0 < M) : bbp_tail n M < 1 := by
  suffices (bbp_tail n M : ℝ) < 1 by exact_mod_cast this
  rw [bbp_tail_coe]
  exact bbpTailTrunc_lt_one n M hM

theorem bbp_tail_bound (n : Nat) (M : Nat) (hM : 0 < M) :
    0 ≤ bbp_tail n M ∧ bbp_tail n M < 1 :=
  ⟨bbp_tail_nonneg n M, bbp_tail_lt_one n M hM⟩

/-! ### Integer BBP terms for the spigot (scaled by `16^n`, not the tail sum) -/

/--
  **LEGACY — MIS-SCALED, DO NOT USE FOR DIGITS.** This was the original `bbp_term`.
  It omits the `1/16^k` weight of the BBP series (`16^n/(8k+j)` instead of
  `16^n/(16^k·(8k+j))`), so `∑_k bbp_term_legacy k n ≈ 3.38·16^n`, not `16^n·π`.
  Every "bracket" and certificate built on it was an artifact of that scaling
  (see `PROVEN_RECORD.md`, 2026-09 correctness audit). Kept only for traceability;
  it agrees with the corrected `bbp_term` at `k = 0` only.
-/
def bbp_term_legacy (k n : Nat) : Nat :=
  let pow16 := 16 ^ n
  (4 * pow16) / (8 * k + 1) -
  (2 * pow16) / (8 * k + 4) -
  pow16 / (8 * k + 5) -
  pow16 / (8 * k + 6)

/--
  Analytically weighted spigot term: `16^{n-k}` scaling via `16^n / 16^k`.
  Aligns with `16^n · bbpSummand k` (P-BBP-01 convergence layer); the legacy
  mis-scaled `bbp_term_legacy` matches this at `k = 0` only.
-/
def bbpSpigotTerm (k n : Nat) : Nat :=
  let num := 16 ^ n
  let den := 16 ^ k
  (4 * num) / (den * (8 * k + 1)) -
  (2 * num) / (den * (8 * k + 4)) -
  num / (den * (8 * k + 5)) -
  num / (den * (8 * k + 6))

/--
  Corrected integer BBP term (2026-09 audit): the floor form of `16^n · bbpSummand k`,
  i.e. `⌊4·16^n/(16^k(8k+1))⌋ - ⌊2·16^n/(16^k(8k+4))⌋ - ⌊16^n/(16^k(8k+5))⌋ -
  ⌊16^n/(16^k(8k+6))⌋`. Definitionally the spigot term `bbpSpigotTerm`; for `k ≤ n`
  this is the `16^(n-k)` spigot weighting and it vanishes for `k > n`
  (`bbpSpigotTerm_eq_zero_of_gt`). Mirrors `scripts/` after the Python fix.
-/
def bbp_term (k n : Nat) : Nat := bbpSpigotTerm k n

theorem bbp_term_eq_bbpSpigotTerm (k n : Nat) : bbp_term k n = bbpSpigotTerm k n := rfl

theorem bbpSpigotTerm_eq_bbp_term_zero (n : Nat) :
    bbpSpigotTerm 0 n = bbp_term 0 n := by
  rfl

/-- The legacy (mis-scaled) term agrees with the corrected one only at `k = 0`. -/
theorem bbpSpigotTerm_eq_bbp_term_legacy_zero (n : Nat) :
    bbpSpigotTerm 0 n = bbp_term_legacy 0 n := by
  simp [bbpSpigotTerm, bbp_term_legacy]

/-! ### `k = 0` floor-division excess (P-BBP-01 head overshoot input) -/

private lemma pow16_mod_five_eq_one (n : Nat) : 16 ^ n % 5 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [pow_succ, Nat.mul_mod, ih]

private lemma pow16_mod_three_eq_one (n : Nat) : 16 ^ n % 3 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [pow_succ, Nat.mul_mod, ih]

private lemma pow16_mod_six_succ (n : Nat) : 16 ^ n.succ % 6 = 4 := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ, Nat.mul_mod, ih, show (16 : Nat) % 6 = 4 by decide]

private lemma pow16_mod_six_ne_zero (n : Nat) : 16 ^ n % 6 ≠ 0 := by
  rcases n with _ | n
  · decide
  · intro h
    simp [pow16_mod_six_succ n] at h

private lemma two_mul_pow16_div_four_eq (n : Nat) (hn : 1 ≤ n) :
    (2 * 16 ^ n) / 4 = 16 ^ n / 2 := by
  have hn' : n ≠ 0 := by omega
  have h2 : 2 ∣ 16 ^ n := dvd_pow (by decide : 2 ∣ 16) hn'
  have h4 : 4 ∣ 2 * 16 ^ n := by
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  have hL : (16 ^ n / 2) * 4 = 2 * 16 ^ n := by
    calc
      (16 ^ n / 2) * 4 = (16 ^ n / 2 * 2) * 2 := by ring
      _ = 16 ^ n * 2 := by rw [Nat.div_mul_cancel h2]
      _ = 2 * 16 ^ n := by ring
  have hR : ((2 * 16 ^ n) / 4) * 4 = 2 * 16 ^ n := Nat.div_mul_cancel h4
  apply Nat.mul_right_cancel (by decide : 0 < 4)
  rw [hL, hR]

private lemma cast_pow16_div_mod_sub (n d : Nat) (hd : d ≠ 0) :
    (16 : ℝ) ^ n / d - ↑(16 ^ n / d) = ↑(16 ^ n % d) / d := by
  have hpow : (16 ^ n : ℝ) = (16 : ℝ) ^ n := by norm_cast
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hmod : (16 ^ n : ℝ) = ↑(16 ^ n % d) + d * ↑(16 ^ n / d) := by
    norm_cast
    rw [Nat.mod_add_div]
  rw [hpow]
  field_simp [hd']
  rw [hmod]
  ring_nf

private lemma pow16_div_five_floor_loss_pos (n : Nat) :
    0 < (16 : ℝ) ^ n / (5 : ℝ) - ((16 ^ n / 5 : ℕ) : ℝ) := by
  have h := cast_pow16_div_mod_sub n 5 (by decide : 5 ≠ 0)
  have hpos : 0 < ((16 ^ n % 5 : ℕ) : ℝ) / (5 : ℝ) := by
    rw [pow16_mod_five_eq_one n]
    norm_num
  linarith [h, hpos]

private lemma pow16_div_six_floor_loss_pos (n : Nat) :
    0 < (16 : ℝ) ^ n / (6 : ℝ) - ((16 ^ n / 6 : ℕ) : ℝ) := by
  have h := cast_pow16_div_mod_sub n 6 (by decide : 6 ≠ 0)
  have hmod : 16 ^ n % 6 ≠ 0 := pow16_mod_six_ne_zero n
  have hpos : 0 < ((16 ^ n % 6 : ℕ) : ℝ) / (6 : ℝ) :=
    div_pos (mod_cast (Nat.pos_of_ne_zero hmod)) (by norm_num : (0 : ℝ) < 6)
  linarith [h, hpos]

/--
  **Proved k = 0 excess:** the weighted `k = 0` spigot term strictly dominates its
  analytic counterpart `16^n · bbpSummand 0`. The gap is exactly the floor losses on
  the `1/5` and `1/6` branches (and at `n = 0` also the `1/2` branch).
-/
theorem bbpSpigotTerm_zero_gt_scaledSummand (n : Nat) :
    (16 : ℝ) ^ n * bbpSummand 0 < (bbpSpigotTerm 0 n : ℝ) := by
  have hpow : (16 ^ n : ℝ) = (16 : ℝ) ^ n := by norm_cast
  have hloss5 := pow16_div_five_floor_loss_pos n
  have hloss6 := pow16_div_six_floor_loss_pos n
  have hloss5' :
      0 < (16 : ℝ) ^ n / (5 : ℝ) - ((16 ^ n / 5 : ℕ) : ℝ) := hloss5
  have hloss6' :
      0 < (16 : ℝ) ^ n / (6 : ℝ) - ((16 ^ n / 6 : ℕ) : ℝ) := hloss6
  rcases n.eq_zero_or_pos with rfl | hn
  · dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
    norm_num
  · have hdiv := two_mul_pow16_div_four_eq n (Nat.succ_le_iff.mp hn)
    have hnat :
        bbpSpigotTerm 0 n =
          4 * 16 ^ n - 16 ^ n / 2 - 16 ^ n / 5 - 16 ^ n / 6 := by
      dsimp [bbpSpigotTerm]
      simp [hdiv]
    have hterm :
        (bbpSpigotTerm 0 n : ℝ) =
          (4 : ℝ) * (16 : ℝ) ^ n - ((16 ^ n / 2 : ℕ) : ℝ) -
            ((16 ^ n / 5 : ℕ) : ℝ) - ((16 ^ n / 6 : ℕ) : ℝ) := by
      rw [hnat]
      have h₁ : 16 ^ n / 2 ≤ 4 * 16 ^ n := by
        have := Nat.div_le_self (16 ^ n) 2
        omega
      have h₂ : 16 ^ n / 5 ≤ 4 * 16 ^ n - 16 ^ n / 2 := by omega
      have h₃ : 16 ^ n / 6 ≤ 4 * 16 ^ n - 16 ^ n / 2 - 16 ^ n / 5 := by omega
      rw [Nat.cast_sub h₃, Nat.cast_sub h₂, Nat.cast_sub h₁]
      norm_cast
    have hanalytic :
        (16 : ℝ) ^ n * bbpSummand 0 =
          (4 : ℝ) * (16 : ℝ) ^ n - ((16 ^ n / 2 : ℕ) : ℝ) -
            (16 : ℝ) ^ n / (5 : ℝ) - (16 : ℝ) ^ n / (6 : ℝ) := by
      have h₂div : 2 ∣ 16 ^ n := dvd_pow (by decide : 2 ∣ 16) (by omega : n ≠ 0)
      have hcast2 : ((16 ^ n / 2 : ℕ) : ℝ) = (16 : ℝ) ^ n / (2 : ℝ) := by
        simpa [hpow] using Nat.cast_div h₂div (by norm_num : (2 : ℝ) ≠ 0)
      dsimp [bbpSummand, bbpCoeff]
      rw [hpow, div_eq_mul_inv, hcast2]
      field_simp
      ring_nf
    rw [hterm, hanalytic]
    linarith [hloss5', hloss6']

/--
  **Exact k = 0 excess (n ≥ 1):** gap equals `/5` and `/6` floor losses; `/2` divides
  exactly since `2 ∣ 16^n`. Used for sum-level head overshoot (`P-BBP-01`).
-/
theorem bbpSpigotTerm_zero_scaled_excess_eq (n : Nat) (hn : 1 ≤ n) :
    (bbpSpigotTerm 0 n : ℝ) - (16 : ℝ) ^ n * bbpSummand 0 =
      ((16 ^ n % 5 : ℕ) : ℝ) / 5 + ((16 ^ n % 6 : ℕ) : ℝ) / 6 := by
  have hpow : (16 ^ n : ℝ) = (16 : ℝ) ^ n := by norm_cast
  have hloss5 := cast_pow16_div_mod_sub n 5 (by decide : 5 ≠ 0)
  have hloss6 := cast_pow16_div_mod_sub n 6 (by decide : 6 ≠ 0)
  have hdiv := two_mul_pow16_div_four_eq n hn
  have hnat :
      bbpSpigotTerm 0 n =
        4 * 16 ^ n - 16 ^ n / 2 - 16 ^ n / 5 - 16 ^ n / 6 := by
    dsimp [bbpSpigotTerm]
    simp [hdiv]
  have hterm :
      (bbpSpigotTerm 0 n : ℝ) =
        (4 : ℝ) * (16 : ℝ) ^ n - ((16 ^ n / 2 : ℕ) : ℝ) -
          ((16 ^ n / 5 : ℕ) : ℝ) - ((16 ^ n / 6 : ℕ) : ℝ) := by
    rw [hnat]
    have h₁ : 16 ^ n / 2 ≤ 4 * 16 ^ n := by
      have := Nat.div_le_self (16 ^ n) 2
      omega
    have h₂ : 16 ^ n / 5 ≤ 4 * 16 ^ n - 16 ^ n / 2 := by omega
    have h₃ : 16 ^ n / 6 ≤ 4 * 16 ^ n - 16 ^ n / 2 - 16 ^ n / 5 := by omega
    rw [Nat.cast_sub h₃, Nat.cast_sub h₂, Nat.cast_sub h₁]
    norm_cast
  have hanalytic :
      (16 : ℝ) ^ n * bbpSummand 0 =
        (4 : ℝ) * (16 : ℝ) ^ n - ((16 ^ n / 2 : ℕ) : ℝ) -
          (16 : ℝ) ^ n / (5 : ℝ) - (16 : ℝ) ^ n / (6 : ℝ) := by
    have h₂div : 2 ∣ 16 ^ n := dvd_pow (by decide : 2 ∣ 16) (by omega : n ≠ 0)
    have hcast2 : ((16 ^ n / 2 : ℕ) : ℝ) = (16 : ℝ) ^ n / (2 : ℝ) := by
      simpa [hpow] using Nat.cast_div h₂div (by norm_num : (2 : ℝ) ≠ 0)
    dsimp [bbpSummand, bbpCoeff]
    rw [hpow, div_eq_mul_inv, hcast2]
    field_simp
    ring_nf
  rw [hterm, hanalytic]
  linarith [hloss5, hloss6]

theorem bbpSpigotTerm_zero_scaled_excess_ge (n : Nat) (hn : 1 ≤ n) :
    (11 : ℝ) / 30 ≤ (bbpSpigotTerm 0 n : ℝ) - (16 : ℝ) ^ n * bbpSummand 0 := by
  rw [bbpSpigotTerm_zero_scaled_excess_eq n hn, pow16_mod_five_eq_one n]
  have hmod6 : 1 ≤ 16 ^ n % 6 :=
    Nat.one_le_of_lt (Nat.pos_of_ne_zero (pow16_mod_six_ne_zero n))
  have h6 : (1 : ℝ) / 6 ≤ ((16 ^ n % 6 : ℕ) : ℝ) / 6 := by
    gcongr
    exact_mod_cast hmod6
  linarith [h6]

/-! ### Weighted tail terms vanish past the head index -/

private lemma four_pow_succ_le_mul (n : Nat) :
    4 * 16 ^ n < 16 ^ (n + 1) * (8 * n + 9) := by
  have h : 16 ^ (n + 1) = 16 * 16 ^ n := by ring_nf
  rw [h, Nat.mul_comm]
  have hineq : 4 < 16 * (8 * n + 9) := by
    have : 16 * (8 * n + 9) = 128 * n + 144 := by ring
    rw [this]
    omega
  nlinarith [pow_pos (by decide : 0 < 16) n]

private lemma two_pow_succ_le_mul (n : Nat) :
    2 * 16 ^ n < 16 ^ (n + 1) * (8 * n + 12) := by
  have h : 16 ^ (n + 1) = 16 * 16 ^ n := by ring_nf
  rw [h, Nat.mul_comm]
  have hineq : 2 < 16 * (8 * n + 12) := by
    have : 16 * (8 * n + 12) = 128 * n + 192 := by ring
    rw [this]
    omega
  nlinarith [pow_pos (by decide : 0 < 16) n]

private lemma one_pow_succ_le_mul (n : Nat) :
    16 ^ n < 16 ^ (n + 1) * (8 * n + 13) := by
  have h : 16 ^ (n + 1) = 16 * 16 ^ n := by ring_nf
  rw [h, Nat.mul_comm]
  have hineq : 1 < 16 * (8 * n + 13) := by
    have : 16 * (8 * n + 13) = 128 * n + 208 := by ring
    rw [this]
    omega
  nlinarith [pow_pos (by decide : 0 < 16) n]

private lemma spigot_branch1_lt (k n : Nat) (hk : n < k) :
    4 * 16 ^ n < 16 ^ k * (8 * k + 1) := by
  have hk' : n + 1 ≤ k := Nat.succ_le_of_lt hk
  have hbase := four_pow_succ_le_mul n
  have hmono : 16 ^ (n + 1) * (8 * n + 9) ≤ 16 ^ k * (8 * k + 1) := by
    have hpow : 16 ^ (n + 1) ≤ 16 ^ k := Nat.pow_le_pow_right (by decide : 16 > 0) hk'
    have hcoef : (8 * n + 9 : Nat) ≤ 8 * k + 1 := by omega
    exact Nat.mul_le_mul hpow hcoef
  exact lt_of_lt_of_le hbase hmono

private lemma spigot_branch2_lt (k n : Nat) (hk : n < k) :
    2 * 16 ^ n < 16 ^ k * (8 * k + 4) := by
  have hk' : n + 1 ≤ k := Nat.succ_le_of_lt hk
  have hbase := two_pow_succ_le_mul n
  have hmono : 16 ^ (n + 1) * (8 * n + 12) ≤ 16 ^ k * (8 * k + 4) := by
    have hpow : 16 ^ (n + 1) ≤ 16 ^ k := Nat.pow_le_pow_right (by decide : 16 > 0) hk'
    have hcoef : (8 * n + 12 : Nat) ≤ 8 * k + 4 := by omega
    exact Nat.mul_le_mul hpow hcoef
  exact lt_of_lt_of_le hbase hmono

private lemma spigot_branch3_lt (k n : Nat) (hk : n < k) :
    16 ^ n < 16 ^ k * (8 * k + 5) := by
  have hk' : n + 1 ≤ k := Nat.succ_le_of_lt hk
  have hbase := one_pow_succ_le_mul n
  have hmono : 16 ^ (n + 1) * (8 * n + 13) ≤ 16 ^ k * (8 * k + 5) := by
    have hpow : 16 ^ (n + 1) ≤ 16 ^ k := Nat.pow_le_pow_right (by decide : 16 > 0) hk'
    have hcoef : (8 * n + 13 : Nat) ≤ 8 * k + 5 := by omega
    exact Nat.mul_le_mul hpow hcoef
  exact lt_of_lt_of_le hbase hmono

private lemma spigot_branch4_lt (k n : Nat) (hk : n < k) :
    16 ^ n < 16 ^ k * (8 * k + 6) := by
  have hk' : n + 1 ≤ k := Nat.succ_le_of_lt hk
  have hbase := one_pow_succ_le_mul n
  have hmono : 16 ^ (n + 1) * (8 * n + 13) ≤ 16 ^ k * (8 * k + 6) := by
    have hpow : 16 ^ (n + 1) ≤ 16 ^ k := Nat.pow_le_pow_right (by decide : 16 > 0) hk'
    have hcoef : (8 * n + 13 : Nat) ≤ 8 * k + 6 := by omega
    exact Nat.mul_le_mul hpow hcoef
  exact lt_of_lt_of_le hbase hmono

/--
  Past the head index (`k > n`), each weighted branch divides to zero, hence the
  whole `bbpSpigotTerm` vanishes. This is the analytic reason tail cert depth
  `50` suffices at sum level without per-term cast bounds.
-/
theorem bbpSpigotTerm_eq_zero_of_gt (k n : Nat) (hk : n < k) :
    bbpSpigotTerm k n = 0 := by
  dsimp [bbpSpigotTerm]
  have hpos1 : 0 < 16 ^ k * (8 * k + 1) := by positivity
  have hpos2 : 0 < 16 ^ k * (8 * k + 4) := by positivity
  have hpos3 : 0 < 16 ^ k * (8 * k + 5) := by positivity
  have hpos4 : 0 < 16 ^ k * (8 * k + 6) := by positivity
  have hb1 :
      (4 * 16 ^ n) / (16 ^ k * (8 * k + 1)) = 0 :=
    Nat.div_eq_of_lt (spigot_branch1_lt k n hk)
  have hb2 :
      (2 * 16 ^ n) / (16 ^ k * (8 * k + 4)) = 0 :=
    Nat.div_eq_of_lt (spigot_branch2_lt k n hk)
  have hb3 :
      16 ^ n / (16 ^ k * (8 * k + 5)) = 0 :=
    Nat.div_eq_of_lt (spigot_branch3_lt k n hk)
  have hb4 :
      16 ^ n / (16 ^ k * (8 * k + 6)) = 0 :=
    Nat.div_eq_of_lt (spigot_branch4_lt k n hk)
  simp [hb1, hb2, hb3, hb4]

/-! ### Guarded spigot floor certificate (2026-09 audit)

  The unguarded sum `∑_{k ≤ n} bbp_term k n` overshoots `⌊16^n·bbpSeries⌋` by a few
  units (each of the four floors per term loses < 1), so its low hex digit is NOT the
  `n`-th digit. The guarded certificate works at precision `16^(n+g)`, sums
  `K = n+g+1` terms, and brackets the error by `E = 4K+2`; if
  `(S-E)/16^g = (S+E)/16^g` the common value is exactly `⌊16^n·bbpSeries⌋`
  (proved in `Thoughts/Proved/BBPGuarded.lean`). This mirrors the guarded spigot in
  `scripts/` (which uses `K = n+51`; the extra terms are zero, only `E` differs).
-/

/-- `∑_{k < K} bbp_term k N`, by structural recursion (kernel-`decide` friendly). -/
def bbpSpigotSum (N : Nat) : Nat → Nat
  | 0 => 0
  | K + 1 => bbpSpigotSum N K + bbp_term K N

/-- Initial number of guard hex digits used by the digit certificate. -/
def bbpGuardDigits : Nat := 4

/-- Error budget `E = 4K + 2` for `K = n + g + 1` terms. -/
def bbpGuardErr (n g : Nat) : Nat := 4 * (n + g + 1) + 2

/-- Guarded sum `S = ∑_{k ≤ n+g} bbp_term k (n+g)`. -/
def bbpGuardedSum (n g : Nat) : Nat := bbpSpigotSum (n + g) (n + g + 1)

/-- Lower end `(S - E) / 16^g` of the guarded floor bracket. -/
def bbpGuardedLo (n g : Nat) : Nat := (bbpGuardedSum n g - bbpGuardErr n g) / 16 ^ g

/-- Upper end `(S + E) / 16^g` of the guarded floor bracket. -/
def bbpGuardedHi (n g : Nat) : Nat := (bbpGuardedSum n g + bbpGuardErr n g) / 16 ^ g

/--
  Adaptive guard search: starting from `g`, try `g, g+4, g+8, …` (at most `fuel` steps)
  and return the first guard depth at which the two guarded ends agree (or the last one
  tried). Correctness never depends on this choice: every theorem is stated for arbitrary
  `g` and only uses the decidable agreement check.
-/
def bbpGuardSearch (n : Nat) : Nat → Nat → Nat
  | 0, g => g
  | fuel + 1, g =>
    if bbpGuardedLo n g = bbpGuardedHi n g then g else bbpGuardSearch n fuel (g + 4)

/-- Guard depth used by the certificate: search `4, 8, …, 64` (16 steps). -/
def bbpCertGuard (n : Nat) : Nat := bbpGuardSearch n 16 bbpGuardDigits

/-- Certified value for `⌊16^n · π⌋` (exact whenever `bbpGuardAgrees n`). -/
def bbpCertFloor (n : Nat) : Nat := bbpGuardedLo n (bbpCertGuard n)

/-- The decidable agreement check that makes `bbpCertFloor n` provably exact. -/
def bbpGuardAgrees (n : Nat) : Prop :=
  bbpGuardedLo n (bbpCertGuard n) = bbpGuardedHi n (bbpCertGuard n)

instance (n : Nat) : Decidable (bbpGuardAgrees n) :=
  Nat.decEq (bbpGuardedLo n (bbpCertGuard n)) (bbpGuardedHi n (bbpCertGuard n))

end FinitistProved
