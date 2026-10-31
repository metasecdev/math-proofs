import Thoughts.Research.MahlerSharp7
import Thoughts.Research.BBPConditionalAllN

/-
Research file (Thoughts/Research/MahlerSharpAllQ7.lean). Round 7.
Explicit irrationality measure for π at **every** denominator `q ≥ 2` (not only `q = 16^k`):
  |π − p/q| > 2^-9095658 / q^570,
i.e. `FinitistProved.PiEffectiveMeasure 570 (1/2^9095658)`.  Proof: take `k = ⌊log₁₆ q⌋ + 1`,
so `q < 16^k ≤ 16 q`, and run the `m = 141`, `n = 4k + 16000` Mahler system.
-/

set_option backward.isDefEq.respectTransparency false

namespace MahlerSharp7AllQ
open MahlerGeneral MahlerMignotte MahlerRemainder MahlerSharp

theorem pi_effective_measure7 : FinitistProved.PiEffectiveMeasure 570 (1 / 2 ^ 9095658) := by
  intro p q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : (0 : ℝ) < (q : ℝ) ^ 570 := by positivity
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log 16 q + 1 := ⟨_, rfl⟩
  have hqk : q < 16 ^ k := hk ▸ Nat.lt_pow_succ_log_self (by norm_num) q
  have hkq : 16 ^ (k - 1) ≤ q := by
    rw [hk, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 16 (by omega)
  have h16k : ((16 ^ k : ℕ) : ℝ) ≤ 16 * q := by
    have : 16 ^ k = 16 * 16 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2 : 16 ^ k ≤ 16 * q := by rw [this]; omega
    exact_mod_cast h2
  have hqk' : (q : ℝ) ≤ ((16 ^ k : ℕ) : ℝ) := by exact_mod_cast hqk.le
  rw [gt_iff_lt, div_lt_iff₀ hqpow]
  by_cases hclose : |Real.pi - p / q| ≤ 1
  · have hR : ∀ h ≤ 141, ‖(mahlerP (4 * k + 16000) 141 : ℂ) *
        Uval (4 * k + 16000) 141 h (Complex.I * (Real.pi / 2))‖ ≤ 1 / (2 * (2 * (q : ℝ)) ^ 141) := by
      intro h hh
      refine (MahlerSharp7.remainder_spec7 k h hh).trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    have hL := pi_lower_bound_sharp (4 * k + 16000) 141 q (by omega) (by omega) p hclose hR
    have hT := MahlerSharp7.T_spec7 k
    have hpos : 0 ≤ (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| :=
      mul_nonneg (pow_nonneg (by positivity) _) (abs_nonneg _)
    have h1 : 1 ≤ (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * 2 ^ (9093800 + 1716 * k) := by
      refine hL.trans (mul_le_mul_of_nonneg_left ?_ hpos)
      simpa using hT
    -- 2^(1716 k) = (16^k)^429 ≤ (16 q)^429
    have h2k : (2 : ℝ) ^ (1716 * k) ≤ 16 ^ 429 * (q : ℝ) ^ 429 := by
      have e : (2 : ℝ) ^ (1716 * k) = (((16 ^ k : ℕ) : ℝ)) ^ 429 := by
        push_cast
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
      rw [e, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h16k 429
    have e2 : (2 : ℝ) ^ 141 * 2 ^ 9093800 * 16 ^ 429 = 2 ^ 9095657 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    have h3 : (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * 2 ^ (9093800 + 1716 * k) ≤
        |Real.pi - p / q| * (q : ℝ) ^ 570 * 2 ^ 9095657 := by
      rw [pow_add]
      have hA : (0 : ℝ) ≤ (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * 2 ^ 9093800 :=
        mul_nonneg hpos (pow_nonneg (by norm_num) _)
      calc (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * (2 ^ 9093800 * 2 ^ (1716 * k))
          = ((2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * 2 ^ 9093800) * 2 ^ (1716 * k) := by ring
        _ ≤ ((2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * 2 ^ 9093800) * (16 ^ 429 * (q : ℝ) ^ 429) :=
            mul_le_mul_of_nonneg_left h2k hA
        _ = |Real.pi - p / q| * (q : ℝ) ^ 570 * (2 ^ 141 * 2 ^ 9093800 * 16 ^ 429) := by ring
        _ = |Real.pi - p / q| * (q : ℝ) ^ 570 * 2 ^ 9095657 := by rw [e2]
    have h4 := h1.trans h3
    have hA : (0 : ℝ) < 2 ^ 9095657 := by positivity
    have h5 : 1 / 2 ^ 9095657 ≤ |Real.pi - p / q| * (q : ℝ) ^ 570 := by
      rw [div_le_iff₀ hA]; linarith
    have h6 : (1 / 2 ^ 9095658 : ℝ) < 1 / 2 ^ 9095657 := by
      apply one_div_lt_one_div_of_lt (by positivity)
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  · push_neg at hclose
    have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 570 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by omega))
    have hC1 : (1 / 2 ^ 9095658 : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
    nlinarith

end MahlerSharp7AllQ

#print axioms MahlerSharp7AllQ.pi_effective_measure7
