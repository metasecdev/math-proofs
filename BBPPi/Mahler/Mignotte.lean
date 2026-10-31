import Mathlib.Tactic
import BBPPi.Mahler.Det
import BBPPi.Mahler.Bounds
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered

/-!
# Mignotte's lower-bound inequality at `x = i`

Step 5a of the Mahler–Mignotte route: Gaussian-integer specialization at `x = i` and
Mignotte's lower-bound inequality. For `q ≥ 1`, `p ∈ ℤ`, `|π - p/q| ≤ 1`: if all
remainders satisfy `‖P · R_h(i)‖ ≤ 1/(2 (2q)^m)` then
  `1 ≤ (2q)^m · |π - p/q| · T`,  with `T` explicit from the coefficient bounds.
-/

set_option backward.isDefEq.respectTransparency false

namespace BBPPi.MahlerMignotte
open BBPPi.MahlerGeneral BBPPi.MahlerVanishing BBPPi.MahlerDet BBPPi.MahlerBounds Finset Polynomial

/-! ### Gaussian integers inside `ℂ` -/

/-- `z ∈ ℤ[i]`. -/
def IsGI (z : ℂ) : Prop := ∃ a b : ℤ, z = a + b * Complex.I

lemma IsGI.intCast (a : ℤ) : IsGI (a : ℂ) := ⟨a, 0, by simp⟩
lemma IsGI.natCast (a : ℕ) : IsGI (a : ℂ) := ⟨a, 0, by simp⟩
lemma IsGI.I : IsGI Complex.I := ⟨0, 1, by simp⟩
lemma IsGI.zero : IsGI 0 := ⟨0, 0, by simp⟩
lemma IsGI.one : IsGI 1 := ⟨1, 0, by simp⟩

lemma IsGI.add {z w : ℂ} (hz : IsGI z) (hw : IsGI w) : IsGI (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz; obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩

lemma IsGI.mul {z w : ℂ} (hz : IsGI z) (hw : IsGI w) : IsGI (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz; obtain ⟨c, d, rfl⟩ := hw
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  push_cast
  linear_combination (b * d : ℂ) * Complex.I_sq

lemma IsGI.pow {z : ℂ} (hz : IsGI z) (k : ℕ) : IsGI (z ^ k) := by
  induction k with
  | zero => simpa using IsGI.one
  | succ k ih => rw [pow_succ]; exact ih.mul hz

lemma IsGI.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IsGI (f i)) :
    IsGI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsGI.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- a nonzero Gaussian integer has norm `≥ 1`. -/
lemma IsGI.one_le_norm {z : ℂ} (hz : IsGI z) (h0 : z ≠ 0) : 1 ≤ ‖z‖ := by
  obtain ⟨a, b, rfl⟩ := hz
  have hab : (1 : ℤ) ≤ a ^ 2 + b ^ 2 := by
    by_contra hlt
    push_neg at hlt
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    apply h0; rw [ha, hb]; simp
  have hsq : ‖(a : ℂ) + b * Complex.I‖ ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    rw [Complex.sq_norm, show ((a : ℂ) + b * Complex.I) = ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I
      by push_cast; ring, Complex.normSq_add_mul_I]
  have h1 : (1 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by exact_mod_cast hab
  have hn := norm_nonneg ((a : ℂ) + b * Complex.I)
  nlinarith

/-! ### A power-difference estimate -/

lemma norm_pow_sub_pow_le (a b : ℂ) (M : ℝ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (k : ℕ) :
    ‖a ^ k - b ^ k‖ ≤ k * M ^ (k - 1) * ‖a - b‖ := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  rw [← (Commute.all a b).geom_sum₂_mul k, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range k, ‖a ^ i * b ^ (k - 1 - i)‖ ≤ ∑ _i ∈ range k, M ^ (k - 1) := by
        refine sum_le_sum fun i hi => ?_
        rw [mem_range] at hi
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖a‖ ^ i * ‖b‖ ^ (k - 1 - i) ≤ M ^ i * M ^ (k - 1 - i) := by gcongr
          _ = M ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    _ = k * M ^ (k - 1) := by simp

/-! ### Mignotte's inequality (abstract form) -/

/-- **Mignotte's step.** Let `a_k` (`k ≤ m`) be complex numbers with `P·a_k ∈ ℤ[i]`, let
`ℓ = iπ/2`, `y = i p/(2q)` with `|π - p/q| ≤ 1`. If `U(y) = Σ a_k y^k ≠ 0` and
`‖P·U(ℓ)‖ ≤ 1/(2(2q)^m)` then `1 ≤ (2q)^m · |π - p/q| · Σ_k ‖P a_k‖ k 3^k`. -/
theorem mignotte_step (m P q : ℕ) (hP : 1 ≤ P) (hq : 1 ≤ q) (p : ℤ) (a : ℕ → ℂ)
    (hint : ∀ k ≤ m, IsGI ((P : ℂ) * a k))
    (hclose : |Real.pi - p / q| ≤ 1)
    (hU : ∑ k ∈ range (m + 1), a k * (Complex.I * (p / (2 * q))) ^ k ≠ 0)
    (hR : ‖(P : ℂ) * ∑ k ∈ range (m + 1), a k * (Complex.I * (Real.pi / 2)) ^ k‖ ≤
      1 / (2 * (2 * (q : ℝ)) ^ m)) :
    1 ≤ (2 * (q : ℝ)) ^ m * |Real.pi - p / q| *
      ∑ k ∈ range (m + 1), ‖(P : ℂ) * a k‖ * k * 3 ^ k := by
  set ℓ : ℂ := Complex.I * (Real.pi / 2)
  set y : ℂ := Complex.I * (p / (2 * q))
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : (0 : ℝ) < (2 * (q : ℝ)) ^ m := by positivity
  -- integrality of (2q)^m P U(y)
  have hZ : IsGI ((2 * (q : ℂ)) ^ m * ((P : ℂ) * ∑ k ∈ range (m + 1), a k * y ^ k)) := by
    rw [mul_sum, mul_sum]
    refine IsGI.sum _ _ fun k hk => ?_
    rw [mem_range] at hk
    have e : (2 * (q : ℂ)) ^ m * ((P : ℂ) * (a k * y ^ k)) =
        ((P : ℂ) * a k) * ((Complex.I * p) ^ k * (2 * (q : ℂ)) ^ (m - k)) := by
      have hq' : (2 * (q : ℂ)) ≠ 0 := by
        have : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
        exact mul_ne_zero two_ne_zero this
      have hm : (2 * (q : ℂ)) ^ m = (2 * (q : ℂ)) ^ k * (2 * (q : ℂ)) ^ (m - k) := by
        rw [← pow_add]; congr 1; omega
      have hq1 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
      rw [hm]
      simp only [y, mul_pow, div_pow]
      field_simp
    rw [e]
    refine (hint k (by omega)).mul (IsGI.mul ((IsGI.I.mul (IsGI.intCast p)).pow k) ?_)
    exact ((IsGI.natCast 2).mul (IsGI.natCast q)).pow _ |>.mul IsGI.one |> fun h => by
      simpa using h
  have hZ0 : (2 * (q : ℂ)) ^ m * ((P : ℂ) * ∑ k ∈ range (m + 1), a k * y ^ k) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (mul_ne_zero ?_ hU)
    · have : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
      exact mul_ne_zero two_ne_zero this
    · exact_mod_cast (show P ≠ 0 by omega)
  have h1 := hZ.one_le_norm hZ0
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_natCast] at h1
  -- difference estimate
  have hℓ : ‖ℓ‖ ≤ 3 := by
    simp only [ℓ, norm_mul, Complex.norm_I, one_mul]
    rw [Complex.norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    linarith [Real.pi_lt_d2]
  have hpq : |(p : ℝ) / q| ≤ 5 := by
    have := abs_sub_abs_le_abs_sub ((p : ℝ) / q) Real.pi
    rw [abs_sub_comm] at this
    rw [abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_lt_d2]
  have hy : ‖y‖ ≤ 3 := by
    simp only [y, norm_mul, Complex.norm_I, one_mul]
    rw [show ((p : ℂ) / (2 * (q : ℂ))) = (((p : ℝ) / q / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    linarith
  have hdiff : ‖ℓ - y‖ = |Real.pi - p / q| / 2 := by
    have : ℓ - y = Complex.I * (((Real.pi - p / q) / 2 : ℝ) : ℂ) := by
      simp only [ℓ, y]; push_cast; ring
    rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_two]
  set T := ∑ k ∈ range (m + 1), ‖(P : ℂ) * a k‖ * k * 3 ^ k
  have hdiffU : ‖(P : ℂ) * ∑ k ∈ range (m + 1), a k * ℓ ^ k -
      (P : ℂ) * ∑ k ∈ range (m + 1), a k * y ^ k‖ ≤ T * ‖ℓ - y‖ := by
    rw [← mul_sub, ← sum_sub_distrib, mul_sum, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [← mul_sub, ← mul_assoc, norm_mul]
    have := norm_pow_sub_pow_le ℓ y 3 hℓ hy k
    have h3 : (k : ℝ) * 3 ^ (k - 1) ≤ k * 3 ^ k := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    calc ‖(P : ℂ) * a k‖ * ‖ℓ ^ k - y ^ k‖ ≤ ‖(P : ℂ) * a k‖ * (k * 3 ^ k * ‖ℓ - y‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact this.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
      _ = _ := by ring
  have htri : ‖(P : ℂ) * ∑ k ∈ range (m + 1), a k * y ^ k‖ ≤
      ‖(P : ℂ) * ∑ k ∈ range (m + 1), a k * ℓ ^ k‖ + T * ‖ℓ - y‖ := by
    have := norm_sub_norm_le ((P : ℂ) * ∑ k ∈ range (m + 1), a k * y ^ k)
      ((P : ℂ) * ∑ k ∈ range (m + 1), a k * ℓ ^ k)
    rw [norm_sub_rev] at this
    linarith
  rw [hdiff] at htri
  -- combine
  have hpos : 0 ≤ |Real.pi - p / q| := abs_nonneg _
  have key : 1 ≤ (2 * (q : ℝ)) ^ m * (1 / (2 * (2 * (q : ℝ)) ^ m) +
      T * (|Real.pi - p / q| / 2)) := by
    calc (1 : ℝ) ≤ (2 * (q : ℝ)) ^ m * ‖(P : ℂ) * ∑ k ∈ range (m + 1), a k * y ^ k‖ := by
          exact h1
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ h2q.le
          linarith
  have e1 : (2 * (q : ℝ)) ^ m * (1 / (2 * (2 * (q : ℝ)) ^ m)) = 1 / 2 := by
    field_simp
  rw [mul_add, e1] at key
  nlinarith

/-! ### Specialization to the Mahler system at `x = i` -/

/-- `U_h(w) = Σ_{k ≤ m} A_hk(i) w^k`. -/
noncomputable def Uval (n m h : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ range (m + 1), aeval Complex.I (Apoly n m h k) * w ^ k

/-- crude coefficient bound from `PA_abs_le_crude`. -/
noncomputable def crudeA (n m : ℕ) : ℝ :=
  (m.factorial : ℝ) * 219 ^ (n * m) * 2 ^ (n * (m + 1)) * 2 ^ (n * (m + 1) - 1 + m) *
    ((n : ℝ) + 1) ^ m

lemma aeval_Apoly (n m h k : ℕ) (z : ℂ) :
    aeval z (Apoly n m h k) = ∑ e ∈ range (n + 1), (rawACoeff n m h k e : ℂ) * z ^ e := by
  simp [Apoly, map_sum]

lemma isGI_P_Apoly (n m h k : ℕ) (hh : h ≤ m) (hk : k ≤ m) :
    IsGI ((mahlerP n m : ℂ) * aeval Complex.I (Apoly n m h k)) := by
  rw [aeval_Apoly, mul_sum]
  refine IsGI.sum _ _ fun e he => ?_
  rw [mem_range] at he
  have hden := integral_coeffs_general n m h k e hh hk (by omega)
  set r : ℚ := (mahlerP n m : ℚ) * rawACoeff n m h k e with hr
  have hnum : ((r.num : ℤ) : ℚ) = r := Rat.coe_int_num_of_den_eq_one hden
  have e1 : (mahlerP n m : ℂ) * ((rawACoeff n m h k e : ℂ) * Complex.I ^ e) =
      ((r.num : ℤ) : ℂ) * Complex.I ^ e := by
    have : ((r.num : ℤ) : ℂ) = ((r : ℚ) : ℂ) := by
      rw [← hnum]; push_cast; rfl
    rw [this, hr]; push_cast; ring
  rw [e1]
  exact (IsGI.intCast _).mul (IsGI.I.pow e)

lemma norm_P_Apoly_le (n m h k : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) (hk : k ≤ m) :
    ‖(mahlerP n m : ℂ) * aeval Complex.I (Apoly n m h k)‖ ≤ ((n : ℝ) + 1) * crudeA n m := by
  rw [aeval_Apoly, mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ e ∈ range (n + 1), ‖(mahlerP n m : ℂ) * ((rawACoeff n m h k e : ℂ) * Complex.I ^ e)‖
      ≤ ∑ _e ∈ range (n + 1), crudeA n m := by
        refine sum_le_sum fun e he => ?_
        rw [mem_range] at he
        rw [← mul_assoc, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
        have hb := PA_abs_le_crude n m h k e hn hh hk (by omega)
        have : ‖(mahlerP n m : ℂ) * (rawACoeff n m h k e : ℂ)‖ =
            ((|(mahlerP n m : ℚ) * rawACoeff n m h k e| : ℚ) : ℝ) := by
          rw [show (mahlerP n m : ℂ) * (rawACoeff n m h k e : ℂ) =
            (((mahlerP n m : ℚ) * rawACoeff n m h k e : ℚ) : ℂ) by push_cast; rfl,
            Complex.norm_ratCast, Rat.cast_abs]
        rw [this, crudeA]
        exact_mod_cast hb
    _ = ((n : ℝ) + 1) * crudeA n m := by simp

/-- **Lower bound for `|π - p/q|` from the Mahler system** (conditional only on the
remainder estimate `hR`, which is the remaining analytic/numeric input). -/
theorem pi_lower_bound (n m q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) (p : ℤ)
    (hclose : |Real.pi - p / q| ≤ 1)
    (hR : ∀ h ≤ m, ‖(mahlerP n m : ℂ) * Uval n m h (Complex.I * (Real.pi / 2))‖ ≤
      1 / (2 * (2 * (q : ℝ)) ^ m)) :
    1 ≤ (2 * (q : ℝ)) ^ m * |Real.pi - p / q| *
      (((m : ℝ) + 1) * m * 3 ^ m * (((n : ℝ) + 1) * crudeA n m)) := by
  obtain ⟨h, hU⟩ := exists_U_ne_zero n m Complex.I I_ne_one (Complex.I * (p / (2 * q)))
  have hP : 1 ≤ mahlerP n m := by
    unfold mahlerP
    have h1 := Nat.factorial_pos m
    have h2 : 0 < lcmUpto n := by
      rw [lcmUpto_eq_finset_lcm]
      exact Nat.pos_of_ne_zero (by
        rw [Ne, Finset.lcm_eq_zero_iff]; simp)
    have h3 := Nat.factorial_pos n
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hU' : ∑ k ∈ range (m + 1), aeval Complex.I (Apoly n m h k) *
      (Complex.I * (p / (2 * q))) ^ k ≠ 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => aeval Complex.I (Apoly n m h k) *
      (Complex.I * (p / (2 * q))) ^ k)]
    exact hU
  have hstep := mignotte_step m (mahlerP n m) q hP hq p (fun k => aeval Complex.I (Apoly n m h k))
    (fun k hk => isGI_P_Apoly n m h k (by omega) hk) hclose hU' (hR h (by omega))
  refine hstep.trans ?_
  have h2q : 0 ≤ (2 * (q : ℝ)) ^ m * |Real.pi - p / q| := by positivity
  apply mul_le_mul_of_nonneg_left _ h2q
  calc ∑ k ∈ range (m + 1), ‖(mahlerP n m : ℂ) * aeval Complex.I (Apoly n m h k)‖ * k * 3 ^ k
      ≤ ∑ _k ∈ range (m + 1), ((n : ℝ) + 1) * crudeA n m * m * 3 ^ m := by
        refine sum_le_sum fun k hk => ?_
        rw [mem_range] at hk
        have hb := norm_P_Apoly_le n m h k hn (by omega) (by omega)
        have hk' : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
        have h3 : (3 : ℝ) ^ k ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
        have hc : 0 ≤ ((n : ℝ) + 1) * crudeA n m := (norm_nonneg _).trans hb
        gcongr
    _ = _ := by simp; ring

end BBPPi.MahlerMignotte
