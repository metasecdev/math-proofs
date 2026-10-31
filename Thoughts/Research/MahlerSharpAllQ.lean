import Thoughts.Research.MahlerSharp
import Thoughts.Research.BBPConditionalAllN

/-
Research file (Thoughts/Research/MahlerSharpAllQ.lean). Round 6.
Explicit irrationality measure for π at **every** denominator `q ≥ 2` (not only `q = 16^k`):
  |π − p/q| > 2^-1721993 / q^658,
i.e. `FinitistProved.PiEffectiveMeasure 658 (1/2^1721993)`.  Proof: take `k = ⌊log₁₆ q⌋ + 1`,
so `q < 16^k ≤ 16 q`, and run the `m = 160`, `n = 4k + 2600` Mahler system.
-/

set_option backward.isDefEq.respectTransparency false

namespace MahlerSharp
open MahlerGeneral MahlerMignotte MahlerRemainder

theorem pi_effective_measure6 : FinitistProved.PiEffectiveMeasure 658 (1 / 2 ^ 1721993) := by
  intro p q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : (0 : ℝ) < (q : ℝ) ^ 658 := by positivity
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
  · have hR : ∀ h ≤ 160, ‖(mahlerP (4 * k + 2600) 160 : ℂ) *
        Uval (4 * k + 2600) 160 h (Complex.I * (Real.pi / 2))‖ ≤ 1 / (2 * (2 * (q : ℝ)) ^ 160) := by
      intro h hh
      refine (remainder_spec6 k h hh).trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    have hL := pi_lower_bound_sharp (4 * k + 2600) 160 q (by omega) (by omega) p hclose hR
    have hT := T_spec6 k
    have hpos : 0 ≤ (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| :=
      mul_nonneg (pow_nonneg (by positivity) _) (abs_nonneg _)
    have h1 : 1 ≤ (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * 2 ^ (1719840 + 1992 * k) := by
      refine hL.trans (mul_le_mul_of_nonneg_left ?_ hpos)
      simpa using hT
    -- 2^(1992 k) = (16^k)^498 ≤ (16 q)^498
    have h2k : (2 : ℝ) ^ (1992 * k) ≤ 16 ^ 498 * (q : ℝ) ^ 498 := by
      have e : (2 : ℝ) ^ (1992 * k) = (((16 ^ k : ℕ) : ℝ)) ^ 498 := by
        push_cast
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
      rw [e, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h16k 498
    have e2 : (2 : ℝ) ^ 160 * 2 ^ 1719840 * 16 ^ 498 = 2 ^ 1721992 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    have h3 : (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * 2 ^ (1719840 + 1992 * k) ≤
        |Real.pi - p / q| * (q : ℝ) ^ 658 * 2 ^ 1721992 := by
      rw [pow_add]
      have hA : (0 : ℝ) ≤ (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * 2 ^ 1719840 :=
        mul_nonneg hpos (pow_nonneg (by norm_num) _)
      calc (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * (2 ^ 1719840 * 2 ^ (1992 * k))
          = ((2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * 2 ^ 1719840) * 2 ^ (1992 * k) := by ring
        _ ≤ ((2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * 2 ^ 1719840) * (16 ^ 498 * (q : ℝ) ^ 498) :=
            mul_le_mul_of_nonneg_left h2k hA
        _ = |Real.pi - p / q| * (q : ℝ) ^ 658 * (2 ^ 160 * 2 ^ 1719840 * 16 ^ 498) := by ring
        _ = |Real.pi - p / q| * (q : ℝ) ^ 658 * 2 ^ 1721992 := by rw [e2]
    have h4 := h1.trans h3
    have hA : (0 : ℝ) < 2 ^ 1721992 := by positivity
    have h5 : 1 / 2 ^ 1721992 ≤ |Real.pi - p / q| * (q : ℝ) ^ 658 := by
      rw [div_le_iff₀ hA]; linarith
    have h6 : (1 / 2 ^ 1721993 : ℝ) < 1 / 2 ^ 1721992 := by
      apply one_div_lt_one_div_of_lt (by positivity)
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  · push_neg at hclose
    have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 658 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by omega))
    have hC1 : (1 / 2 ^ 1721993 : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
    nlinarith

end MahlerSharp

#print axioms MahlerSharp.pi_effective_measure6
