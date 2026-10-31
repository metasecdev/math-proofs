/-
  H-04: analytic proof plan for `BBPPiEqualsSeries : bbpSeries = Real.pi`.
  See `docs/H04_PROOF_PLAN.md` for the lemma table and status. All lemmas fully proved (no sorry).

  Route (integral representation, no √2 substitution needed thanks to the x^8/16 scaling):
    bbpSeries = ∑ₖ 16⁻ᵏ (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))
              = ∑ₖ ∫₀¹ (x^8/16)^k · p(x) dx           with p(x) = 4 - 2x³ - x⁴ - x⁵
              = ∫₀¹ p(x) / (1 - x^8/16) dx             (dominated convergence, geometric series)
              = F(1) - F(0) = π                          (FTC)
  where F(x) = 2 log(2 - x²) - 2 log(x² - 2x + 2) + 4 arctan(x - 1).
  Key algebra: 16 - x^8 = -(x²-2)(x²+2)(x²+2x+2)(x²-2x+2) and
               p(x) = -(x-1)(x²+2)(x²+2x+2), so p/(1-x^8/16) = 16(x-1)/((x²-2)(x²-2x+2)).
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Thoughts.Proved.BBPAlgebra
import Thoughts.Proved.BBPSeries

namespace FinitistProved

open Real Nat Finset MeasureTheory intervalIntegral

/-- Numerator polynomial `p(x) = 4 - 2x³ - x⁴ - x⁵` (coefficients `(4,-2,-1,-1)` at `x^(j-1)`,
`j ∈ {1,4,5,6}`). -/
noncomputable def bbpNum (x : ℝ) : ℝ := 4 - 2 * x ^ 3 - x ^ 4 - x ^ 5

/-- The BBP integrand `p(x) / (1 - x^8/16)`. -/
noncomputable def bbpKernel (x : ℝ) : ℝ := bbpNum x / (1 - x ^ 8 / 16)

/-- Explicit antiderivative of `bbpKernel` on `[0,1]`. -/
noncomputable def bbpAntideriv (x : ℝ) : ℝ :=
  2 * Real.log (2 - x ^ 2) - 2 * Real.log (x ^ 2 - 2 * x + 2) + 4 * Real.arctan (x - 1)

/-! ### (1) monomial integrals -/

theorem integral_pow_bbp (k j : ℕ) (hj : 1 ≤ j) :
    ∫ x in (0 : ℝ)..1, x ^ (8 * k + j - 1) = 1 / ((8 : ℝ) * k + j) := by
  rw [integral_pow]
  have h : 8 * k + j - 1 + 1 = 8 * k + j := by omega
  have hc : ((8 * k + j - 1 : ℕ) : ℝ) + 1 = 8 * k + j := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at this
    exact this
  rw [hc, one_pow, zero_pow (by omega : 8 * k + j - 1 + 1 ≠ 0), sub_zero]

/-- The four monomial integrals used below, in the exact shape `x ^ (8k + c)`. -/
private theorem integral_x8k_add (k c : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ (8 * k + c) = 1 / ((8 : ℝ) * k + c + 1) := by
  have := integral_pow_bbp k (c + 1) (by omega)
  rw [show 8 * k + (c + 1) - 1 = 8 * k + c by omega] at this
  rw [this]
  push_cast
  ring_nf

/-! ### (2) termwise integral of the combined integrand -/

private theorem term_integrand (k : ℕ) (x : ℝ) :
    (x ^ 8 / 16) ^ k * bbpNum x =
      (1 / 16 : ℝ) ^ k * (4 * x ^ (8 * k + 0) - 2 * x ^ (8 * k + 3)
        - x ^ (8 * k + 4) - x ^ (8 * k + 5)) := by
  have h : (x ^ 8 / 16) ^ k = (1 / 16 : ℝ) ^ k * x ^ (8 * k) := by
    rw [div_pow, ← pow_mul, one_div_pow]; ring
  rw [h]
  unfold bbpNum
  simp only [pow_add]
  ring

theorem term_integral (k : ℕ) :
    ∫ x in (0 : ℝ)..1, (x ^ 8 / 16) ^ k * bbpNum x = bbpSummand k := by
  simp_rw [term_integrand k]
  have hi : ∀ c : ℕ, IntervalIntegrable (fun x : ℝ => x ^ (8 * k + c)) volume 0 1 :=
    fun c => (continuous_pow _).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((((hi 0).const_mul 4).sub ((hi 3).const_mul 2)).sub (hi 4)) (hi 5),
    intervalIntegral.integral_sub (((hi 0).const_mul 4).sub ((hi 3).const_mul 2)) (hi 4),
    intervalIntegral.integral_sub ((hi 0).const_mul 4) ((hi 3).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_x8k_add, integral_x8k_add, integral_x8k_add, integral_x8k_add]
  unfold bbpSummand bbpCoeff
  push_cast
  have h16 : (16 : ℝ) ^ k ≠ 0 := by positivity
  have h1 : (8 : ℝ) * k + 0 + 1 ≠ 0 := by positivity
  have h2 : (8 : ℝ) * k + 3 + 1 ≠ 0 := by positivity
  have h3 : (8 : ℝ) * k + 4 + 1 ≠ 0 := by positivity
  have h4 : (8 : ℝ) * k + 5 + 1 ≠ 0 := by positivity
  rw [one_div_pow]
  field_simp
  ring

/-! ### (3) pointwise geometric sum and domination -/

private theorem ratio_bounds {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ x ^ 8 / 16 ∧ x ^ 8 / 16 ≤ 1 / 16 := by
  obtain ⟨h0, h1⟩ := hx
  have : x ^ 8 ≤ 1 := pow_le_one₀ h0 h1
  constructor
  · positivity
  · linarith

theorem hasSum_kernel {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun k : ℕ => (x ^ 8 / 16) ^ k * bbpNum x) (bbpKernel x) := by
  obtain ⟨h0, h1⟩ := ratio_bounds hx
  have hg := (hasSum_geometric_of_lt_one h0 (by linarith)).mul_right (bbpNum x)
  have e : bbpKernel x = (1 - x ^ 8 / 16)⁻¹ * bbpNum x := div_eq_inv_mul _ _
  rw [e]
  exact hg

theorem abs_bbpNum_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bbpNum x| ≤ 8 := by
  obtain ⟨h0, h1⟩ := hx
  unfold bbpNum
  have h3 : x ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have h4 : x ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have h5 : x ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have h3' : 0 ≤ x ^ 3 := by positivity
  have h4' : 0 ≤ x ^ 4 := by positivity
  have h5' : 0 ≤ x ^ 5 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-! ### (4) interchange: `bbpSeries = ∫₀¹ bbpKernel` -/

private theorem kernel_ae_bound (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖(x ^ 8 / 16) ^ k * bbpNum x‖ ≤ 8 * (1 / 16 : ℝ) ^ k := by
  obtain ⟨h0, h1⟩ := ratio_bounds hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)]
  calc (x ^ 8 / 16) ^ k * |bbpNum x| ≤ (1 / 16 : ℝ) ^ k * 8 :=
        mul_le_mul (pow_le_pow_left₀ h0 h1 k) (abs_bbpNum_le hx) (abs_nonneg _) (by positivity)
    _ = 8 * (1 / 16 : ℝ) ^ k := mul_comm _ _

theorem bbpSeries_eq_integral : bbpSeries = ∫ x in (0 : ℝ)..1, bbpKernel x := by
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  have hmem : ∀ {t : ℝ}, t ∈ Set.uIoc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    rw [hIoc] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hsum : HasSum (fun k : ℕ => ∫ x in (0 : ℝ)..1, (x ^ 8 / 16) ^ k * bbpNum x)
      (∫ x in (0 : ℝ)..1, bbpKernel x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => 8 * (1 / 16 : ℝ) ^ k) ?_ ?_ ?_ ?_ ?_
    · intro k
      exact (by unfold bbpNum; fun_prop : Continuous fun x : ℝ => (x ^ 8 / 16) ^ k * bbpNum x).aestronglyMeasurable
    · intro k
      exact Filter.Eventually.of_forall fun t ht => kernel_ae_bound k (hmem ht)
    · exact Filter.Eventually.of_forall fun t _ =>
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 8
    · exact _root_.intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t ht => hasSum_kernel (hmem ht)
  simp_rw [term_integral] at hsum
  exact hsum.tsum_eq

/-! ### (5) antiderivative -/

private theorem two_sub_sq_pos {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < 2 - x ^ 2 := by
  obtain ⟨h0, h1⟩ := hx
  nlinarith

private theorem quad_pos (x : ℝ) : 0 < x ^ 2 - 2 * x + 2 := by nlinarith [sq_nonneg (x - 1)]

private theorem den_pos {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 - x ^ 8 / 16 := by
  linarith [(ratio_bounds hx).2]

/-- Partial-fraction form of the kernel on `[0,1]`. -/
theorem bbpKernel_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    bbpKernel x = -(4 * x) / (2 - x ^ 2) - 4 * (x - 2) / (x ^ 2 - 2 * x + 2) := by
  have h1 := (two_sub_sq_pos hx).ne'
  have h2 := (quad_pos x).ne'
  have h3 := (den_pos hx).ne'
  unfold bbpKernel bbpNum
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff h3 (mul_ne_zero h1 h2)]
  ring

theorem hasDerivAt_bbpAntideriv {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt bbpAntideriv (bbpKernel x) x := by
  have h1 := (two_sub_sq_pos hx).ne'
  have h2 := (quad_pos x).ne'
  have hA : HasDerivAt (fun y : ℝ => 2 - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 2)
  have hB : HasDerivAt (fun y : ℝ => y ^ 2 - 2 * y + 2) (2 * x - 2) x := by
    have := (((hasDerivAt_pow 2 x).sub ((hasDerivAt_id x).const_mul 2)).add_const 2)
    simpa using this
  have hC : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have hd := (((hA.log h1).const_mul 2).sub ((hB.log h2).const_mul 2)).add (hC.arctan.const_mul 4)
  rw [bbpKernel_eq hx]
  convert hd using 1
  have h4 : 1 + (x - 1) ^ 2 = x ^ 2 - 2 * x + 2 := by ring
  rw [h4]
  field_simp
  ring

theorem intervalIntegrable_bbpKernel : IntervalIntegrable bbpKernel volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  unfold bbpKernel bbpNum
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro x hx
  exact (den_pos hx).ne'

/-! ### (6) FTC -/

theorem integral_bbpKernel : ∫ x in (0 : ℝ)..1, bbpKernel x = Real.pi := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := bbpAntideriv) (f' := bbpKernel) (a := 0) (b := 1)
    (fun x hx => hasDerivAt_bbpAntideriv (by rwa [Set.uIcc_of_le zero_le_one] at hx))
    intervalIntegrable_bbpKernel
  rw [h]
  unfold bbpAntideriv
  have e1 : Real.arctan ((1 : ℝ) - 1) = 0 := by simp
  have e0 : Real.arctan ((0 : ℝ) - 1) = -(Real.pi / 4) := by
    rw [show (0 : ℝ) - 1 = -1 by norm_num, Real.arctan_neg, Real.arctan_one]
  simp only [e1, e0]
  norm_num
  ring_nf

/-! ### (7) conclusion -/

theorem bbpSeries_eq_pi : bbpSeries = Real.pi := by
  rw [bbpSeries_eq_integral, integral_bbpKernel]

theorem bbpPiEqualsSeries_proved : BBPPiEqualsSeries := bbpSeries_eq_pi

end FinitistProved
