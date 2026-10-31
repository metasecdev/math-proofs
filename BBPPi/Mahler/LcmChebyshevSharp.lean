import BBPPi.Mahler.LcmChebyshev

/-!
# A sharper Chebyshev bound with linear error

the μ = 658 bound.
Sharper Chebyshev bound with a *linear* error term, valid for all `x ≥ 1`:
  ψ(x) ≤ (log 4 + 0.07)·x + 1820,
obtained from Mathlib's `Chebyshev.psi_le` (ψ x ≤ log 4·x + 2√x log x) and the elementary
`log y ≤ δ y − 1 − log δ`.  Consequence: `lcm(1..n) ≤ exp((log 4 + 0.07) n + 1820)`, i.e.
≈ 2.10 bits per `n` instead of the 8 bits of `lcm ≤ 219^n ≤ 2^{8n}` used in `BBPPi.Mahler.PiMeasure`.
-/

namespace BBPPi.LcmChebyshevSharp
open Real Chebyshev Finset

/-- `log x ≤ δ x − 1 − log δ` for `x, δ > 0` (tangent-line bound). -/
lemma log_le_lin {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) : Real.log x ≤ δ * x - 1 - Real.log δ := by
  have := Real.log_le_sub_one_of_pos (mul_pos hδ hx)
  rw [Real.log_mul hδ.ne' hx.ne'] at this
  linarith

lemma log_two_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9

lemma log_200_lt : Real.log 200 < 5.5452 := by
  have h : Real.log 200 ≤ Real.log (2 ^ 8) := Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  have := log_two_lt
  push_cast at h
  linarith

/-- `2 √x log x ≤ 0.07 x + 1820` for `x ≥ 1`. -/
lemma two_sqrt_log_le {x : ℝ} (hx : 1 ≤ x) : 2 * Real.sqrt x * Real.log x ≤ 0.07 * x + 1820 := by
  set s := Real.sqrt x with hs
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hx
  have hs0 : 0 < s := by linarith
  have hss : s * s = x := Real.mul_self_sqrt hx0
  have hlog : Real.log x = 2 * Real.log s := by
    rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
  have hl := log_le_lin hs0 (show (0 : ℝ) < 1 / 200 by norm_num)
  have h200 : Real.log (1 / 200 : ℝ) = - Real.log 200 := by
    rw [one_div, Real.log_inv]
  rw [h200] at hl
  have hl2 : Real.log s ≤ s / 200 + 4.5452 := by have := log_200_lt; linarith
  rw [hlog]
  have hsq : 0 ≤ (s - 200) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hl2 hs0.le]

lemma log_four_lt : Real.log 4 < 1.3862943616 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := log_two_lt; linarith

/-- **Linear Chebyshev bound**: `ψ x ≤ (log 4 + 0.07) x + 1820` for `x ≥ 1`. -/
theorem psi_le_lin {x : ℝ} (hx : 1 ≤ x) : ψ x ≤ (Real.log 4 + 0.07) * x + 1820 := by
  have h1 := psi_le hx
  have h2 := two_sqrt_log_le hx
  nlinarith

/-- `lcm(1..n) ≤ exp((log 4 + 0.07) n + 1820)` for every `n`. -/
theorem lcm_le_exp_lin (n : ℕ) :
    (((Icc 1 n).lcm id : ℕ) : ℝ) ≤ Real.exp ((Real.log 4 + 0.07) * n + 1820) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine (LcmChebyshev.lcm_le_exp_psi n).trans (Real.exp_le_exp.mpr ?_)
    exact psi_le_lin (by exact_mod_cast hn)

/-- same bound with a clean rational per-`n` constant: `lcm(1..n) ≤ exp(1.4563 n + 1820)`. -/
theorem lcm_le_exp_lin' (n : ℕ) :
    (((Icc 1 n).lcm id : ℕ) : ℝ) ≤ Real.exp (1.4563 * n + 1820) := by
  refine (lcm_le_exp_lin n).trans (Real.exp_le_exp.mpr ?_)
  have := log_four_lt
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end BBPPi.LcmChebyshevSharp
