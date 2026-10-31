import Thoughts.Research.BBPBaseQCert

/-!
# Fixed-depth base-`q` P-BBP-01

`baseq_floor_of_ge_depth`: for `q ≥ 2`, every rational BBP depth `N ≥ baseqDepth q n =
430499 + 658·n·(⌊log₁₆ q⌋+1)` gives `⌊q^n S_N⌋ = ⌊q^n π⌋` (the extra depth only shrinks the
error `q^n/16^N`).  Hence also `Lo = Hi` is not needed at such depths, and the digit follows.
-/

namespace FinitistProved
open Real

/-- **Base-`q` fixed depth**: every depth `N ≥ baseqDepth q n` gives `⌊q^n π⌋`. -/
theorem baseq_floor_of_ge_depth {q n N : ℕ} (hq : 2 ≤ q) (hN : baseqDepth q n ≤ N) :
    baseqLo q n N = ⌊(q : ℝ) ^ n * Real.pi⌋ := by
  obtain ⟨hl, hu⟩ := pi_bracket N
  have eL : baseqLo q n N = ⌊(q : ℝ) ^ n * (bbpHeadQ N : ℝ)⌋ := by
    unfold baseqLo; rw [← Rat.floor_cast (α := ℝ)]; congr 1; push_cast; ring
  rw [eL]
  have hqR : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have h16 : (0 : ℝ) < 16 ^ N := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: π is ≥ 0.14 from every integer and the error is < 16^-430499
    simp only [pow_zero, one_mul]
    have herr : 1 / (16 : ℝ) ^ N ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le (by norm_num)
      calc (16 : ℝ) = 16 ^ 1 := by norm_num
        _ ≤ 16 ^ N := pow_le_pow_right₀ (by norm_num) (by unfold baseqDepth at hN; omega)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h2 : (⌊(bbpHeadQ N : ℝ)⌋ : ℝ) + 1 ≤ ⌊Real.pi⌋ := by exact_mod_cast hlt
      have := Int.lt_floor_add_one (bbpHeadQ N : ℝ)
      have := Int.floor_le Real.pi
      have := pi_dist_int_gt ⌊Real.pi⌋
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    · have h2 : (⌊Real.pi⌋ : ℝ) + 1 ≤ ⌊(bbpHeadQ N : ℝ)⌋ := by exact_mod_cast hgt
      have := Int.lt_floor_add_one Real.pi
      have := Int.floor_le (bbpHeadQ N : ℝ)
      have := pi_dist_int_gt ⌊(bbpHeadQ N : ℝ)⌋
      rw [abs_of_neg (by linarith)] at this
      linarith
  · apply floor_eq_of_effective_measure MahlerSharp.pi_effective_measure6 hq hn
    -- |q^n S - q^n π| ≤ q^n / 16^N ≤ C q^n / (q^n)^658
    have hab : |(q : ℝ) ^ n * (bbpHeadQ N : ℝ) - (q : ℝ) ^ n * Real.pi| ≤ (q : ℝ) ^ n / 16 ^ N := by
      rw [← mul_sub, abs_mul, abs_of_pos hqR, div_eq_mul_one_div]
      gcongr
      rw [abs_of_nonpos (by linarith)]; linarith
    refine hab.trans ?_
    -- 2^1721993 · (q^n)^658 ≤ 16^N
    have hL : q < 16 ^ (Nat.log 16 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hnat0 : 2 ^ 1721993 * (q ^ n) ^ 658 ≤ 16 ^ baseqDepth q n := by
      have e : 16 ^ baseqDepth q n = 16 ^ 430499 * (16 ^ (Nat.log 16 q + 1)) ^ (n * 658) := by
        simp only [baseqDepth]; rw [pow_add, ← pow_mul]; ring_nf
      rw [e, ← pow_mul]
      apply Nat.mul_le_mul
      · rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
      · exact Nat.pow_le_pow_left hL.le _
    have hnat : 2 ^ 1721993 * (q ^ n) ^ 658 ≤ 16 ^ N :=
      hnat0.trans (Nat.pow_le_pow_right (by norm_num) hN)
    have hR : (2 : ℝ) ^ 1721993 * ((q : ℝ) ^ n) ^ 658 ≤ 16 ^ N := by exact_mod_cast hnat
    have hp : (0 : ℝ) < ((q : ℝ) ^ n) ^ 658 := by positivity
    rw [div_le_iff₀ h16]
    have : (1 / 2 ^ 1721993 : ℝ) * (q : ℝ) ^ n / ((q : ℝ) ^ n) ^ 658 * 16 ^ N
        = (q : ℝ) ^ n * (16 ^ N / (2 ^ 1721993 * ((q : ℝ) ^ n) ^ 658)) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ (16 : ℝ) ^ N / (2 ^ 1721993 * ((q : ℝ) ^ n) ^ 658) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith

/-- base-`q` digit at any depth `N ≥ baseqDepth q n`. -/
theorem baseq_digit_of_ge_depth {q n N : ℕ} (hq : 2 ≤ q) (hN : baseqDepth q n ≤ N) :
    baseqLo q n N % q = ⌊(q : ℝ) ^ n * Real.pi⌋ % q := by
  rw [baseq_floor_of_ge_depth hq hN]

/-- simple closed-form depth: `N ≥ 430499 + 658·n·q` always suffices (`⌊log₁₆ q⌋ + 1 ≤ q`). -/
theorem baseq_floor_fixed {q n N : ℕ} (hq : 2 ≤ q) (hN : 430499 + 658 * n * q ≤ N) :
    baseqLo q n N = ⌊(q : ℝ) ^ n * Real.pi⌋ := by
  apply baseq_floor_of_ge_depth hq
  have h1 : Nat.log 16 q + 1 ≤ q := by
    have := Nat.log_lt_self 16 (show q ≠ 0 by omega); omega
  have : 658 * n * (Nat.log 16 q + 1) ≤ 658 * n * q := Nat.mul_le_mul_left _ h1
  unfold baseqDepth; omega

end FinitistProved

#print axioms FinitistProved.baseq_floor_of_ge_depth
#print axioms FinitistProved.baseq_digit_of_ge_depth
#print axioms FinitistProved.baseq_floor_fixed
