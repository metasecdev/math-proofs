import Thoughts.Research.MahlerPiMeasure
import Thoughts.Research.LcmChebyshevSharp

/-
Research file (Thoughts/Research/MahlerSharp.lean). Round 6: sharper bookkeeping of the
Mahler–Mignotte chain.  Replaces the crude estimates of `MahlerBounds.PA_abs_le_crude` /
`MahlerPiMeasure.remainder_closed`:
* `lcm(1..n) ≤ 219^n`              →  `lcm(1..n) ≤ exp(1.4563 n + 1820)` (LcmChebyshevSharp)
* `C(J−1+j, J−1) ≤ 2^{J+m}`         →  `≤ (m+1)^m (n+1)^m`  (polynomial in `n`)
* `(n+1)^h ≤ 2^{nm}`               →  kept as `(n+1)^m`   (polynomial in `n`)
* tail `r^J/J! ≤ (16/(m+1))^J`     →  `≤ (9/(m+1))^J`     (`n ≥ 10`)
-/

set_option backward.isDefEq.respectTransparency false

namespace MahlerSharp
open MahlerGeneral MahlerVanishing MahlerDet MahlerBounds MahlerMignotte MahlerRemainder Finset

/-- `C(J−1+j, J−1) ≤ ((m+1)(n+1))^m` for `j ≤ m`, `J = n(m+1)`. -/
lemma choose_le_poly (n m j : ℕ) (hj : j ≤ m) :
    (n * (m + 1) - 1 + j).choose (n * (m + 1) - 1) ≤ ((m + 1) * (n + 1)) ^ m := by
  rw [Nat.choose_symm_add]
  refine (Nat.choose_le_pow _ _).trans ?_
  calc (n * (m + 1) - 1 + j) ^ j ≤ ((m + 1) * (n + 1)) ^ j := by
        apply Nat.pow_le_pow_left
        have h1 : n * (m + 1) - 1 + j ≤ n * (m + 1) + m := by omega
        have h2 : (m + 1) * (n + 1) = n * (m + 1) + m + 1 := by ring
        omega
    _ ≤ ((m + 1) * (n + 1)) ^ m := Nat.pow_le_pow_right (by positivity) hj

lemma choose_le_poly_q (n m j : ℕ) (hj : j ≤ m) :
    (((n * (m + 1) - 1 + j).choose (n * (m + 1) - 1) : ℕ) : ℚ) ≤
      ((m : ℚ) + 1) ^ m * ((n : ℚ) + 1) ^ m := by
  have := choose_le_poly n m j hj
  rw [← mul_pow]
  exact_mod_cast this

/-- **sharp coefficient bound**. -/
theorem PA_abs_le_sharp (n m h k e : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) (hk : k ≤ m) (he : e ≤ n) :
    |(mahlerP n m : ℚ) * rawACoeff n m h k e| ≤
      (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m * 2 ^ (n * (m + 1)) *
        (((m : ℚ) + 1) ^ m * ((n : ℚ) + 1) ^ m) * ((n : ℚ) + 1) ^ m := by
  refine (PA_abs_le n m h k e hn hh hk he).trans ?_
  have hC : ((n.choose e : ℕ) : ℚ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n e
  have hB := choose_le_poly_q n m (m - k) (Nat.sub_le m k)
  have hk1 : (m.factorial : ℚ) / k.factorial ≤ m.factorial := by
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hN : ((n : ℚ) + 1) ^ h ≤ ((n : ℚ) + 1) ^ m :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℚ) ≤ n)]) hh
  rw [pow_mul (2 : ℚ) n (m + 1)]
  gcongr

/-- sharp replacement for `crudeA`. -/
noncomputable def sharpA (n m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (lcmUpto n : ℝ) ^ m * 2 ^ (n * (m + 1)) *
    (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m) * ((n : ℝ) + 1) ^ m

lemma norm_P_Apoly_le_sharp (n m h k : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) (hk : k ≤ m) :
    ‖(mahlerP n m : ℂ) * Polynomial.aeval Complex.I (Apoly n m h k)‖ ≤
      ((n : ℝ) + 1) * sharpA n m := by
  rw [aeval_Apoly, mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ e ∈ range (n + 1), ‖(mahlerP n m : ℂ) * ((rawACoeff n m h k e : ℂ) * Complex.I ^ e)‖
      ≤ ∑ _e ∈ range (n + 1), sharpA n m := by
        refine sum_le_sum fun e he => ?_
        rw [mem_range] at he
        rw [← mul_assoc, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
        have hb := PA_abs_le_sharp n m h k e hn hh hk (by omega)
        have : ‖(mahlerP n m : ℂ) * (rawACoeff n m h k e : ℂ)‖ =
            ((|(mahlerP n m : ℚ) * rawACoeff n m h k e| : ℚ) : ℝ) := by
          rw [show (mahlerP n m : ℂ) * (rawACoeff n m h k e : ℂ) =
            (((mahlerP n m : ℚ) * rawACoeff n m h k e : ℚ) : ℂ) by push_cast; rfl,
            Complex.norm_ratCast, Rat.cast_abs]
        rw [this, sharpA]
        exact_mod_cast hb
    _ = ((n : ℝ) + 1) * sharpA n m := by simp

/-- **Lower bound for `|π − p/q|`**, sharp coefficient version of `pi_lower_bound`. -/
theorem pi_lower_bound_sharp (n m q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) (p : ℤ)
    (hclose : |Real.pi - p / q| ≤ 1)
    (hR : ∀ h ≤ m, ‖(mahlerP n m : ℂ) * Uval n m h (Complex.I * (Real.pi / 2))‖ ≤
      1 / (2 * (2 * (q : ℝ)) ^ m)) :
    1 ≤ (2 * (q : ℝ)) ^ m * |Real.pi - p / q| *
      (((m : ℝ) + 1) * m * 3 ^ m * (((n : ℝ) + 1) * sharpA n m)) := by
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
  have hU' : ∑ k ∈ range (m + 1), Polynomial.aeval Complex.I (Apoly n m h k) *
      (Complex.I * (p / (2 * q))) ^ k ≠ 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => Polynomial.aeval Complex.I (Apoly n m h k) *
      (Complex.I * (p / (2 * q))) ^ k)]
    exact hU
  have hstep := mignotte_step m (mahlerP n m) q hP hq p
    (fun k => Polynomial.aeval Complex.I (Apoly n m h k))
    (fun k hk => isGI_P_Apoly n m h k (by omega) hk) hclose hU' (hR h (by omega))
  refine hstep.trans ?_
  have h2q : 0 ≤ (2 * (q : ℝ)) ^ m * |Real.pi - p / q| := by positivity
  apply mul_le_mul_of_nonneg_left _ h2q
  calc ∑ k ∈ range (m + 1), ‖(mahlerP n m : ℂ) * Polynomial.aeval Complex.I (Apoly n m h k)‖ *
        k * 3 ^ k
      ≤ ∑ _k ∈ range (m + 1), ((n : ℝ) + 1) * sharpA n m * m * 3 ^ m := by
        refine sum_le_sum fun k hk => ?_
        rw [mem_range] at hk
        have hb := norm_P_Apoly_le_sharp n m h k hn (by omega) (by omega)
        have hk' : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
        have h3 : (3 : ℝ) ^ k ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
        have hc : 0 ≤ ((n : ℝ) + 1) * sharpA n m := (norm_nonneg _).trans hb
        gcongr
    _ = _ := by simp; ring


/-- `r^J/J! ≤ (9/M)^J` for `r = (2n+1)π/2`, `J = n·M`, `n ≥ 10` (vs. `16/M` in round 4). -/
lemma tail_le9 (n M : ℕ) (hn : 10 ≤ n) (hM : 1 ≤ M) :
    ((2 * n + 1) * (Real.pi / 2)) ^ (n * M) / ((n * M).factorial : ℝ) ≤ (9 / (M : ℝ)) ^ (n * M) := by
  set J := n * M
  have hJpos : (0 : ℝ) < J := by
    have : 0 < J := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hJ := Real.pow_div_factorial_le_exp (x := (J : ℝ)) hJpos.le J
  set r : ℝ := (2 * n + 1) * (Real.pi / 2)
  have e1 : r ^ J / (J.factorial : ℝ) = (r / J) ^ J * ((J : ℝ) ^ J / (J.factorial : ℝ)) := by
    rw [div_pow]; field_simp
  rw [e1]
  have hexp : Real.exp (J : ℝ) = Real.exp 1 ^ J := (Real.exp_one_pow J).symm
  calc (r / J) ^ J * ((J : ℝ) ^ J / (J.factorial : ℝ)) ≤ (r / J) ^ J * Real.exp 1 ^ J := by
        rw [← hexp]; exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (r / J * Real.exp 1) ^ J := by rw [mul_pow]
    _ ≤ (9 / (M : ℝ)) ^ J := by
        apply pow_le_pow_left₀ (by positivity)
        have he := Real.exp_one_lt_d9
        have hpi := Real.pi_lt_d4
        have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
        have hM' : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hJpos hM']
        simp only [r, J]
        push_cast
        have he0 := Real.exp_pos 1
        have hpe : Real.pi * Real.exp 1 ≤ 8.54 := by
          have := mul_lt_mul'' hpi he Real.pi_pos.le he0.le
          norm_num at this; linarith
        have : (2 * (n : ℝ) + 1) * (Real.pi / 2) * Real.exp 1 ≤ 9 * n := by
          have e : (2 * (n : ℝ) + 1) * (Real.pi / 2) * Real.exp 1 =
              (2 * n + 1) * (Real.pi * Real.exp 1) / 2 := by ring
          rw [e]
          have h2n : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hpe h2n]
        nlinarith

/-- **Sharp remainder bound** (`n ≥ 10`). -/
theorem remainder_sharp (n m h : ℕ) (hn : 10 ≤ n) (hh : h ≤ m) :
    ‖(mahlerP n m : ℂ) * Uval n m h (Complex.I * (Real.pi / 2))‖ ≤
      (m : ℝ) ^ m * Real.exp (m * (1.4563 * n + 1820)) * ((m : ℝ) + 1) ^ m *
        ((n : ℝ) + 1) ^ (2 * m + 1) * 2 ^ (n * (m + 1)) * (9 / ((m : ℝ) + 1)) ^ (n * (m + 1)) *
          Real.exp ((2 * n + 1) * (Real.pi / 2)) := by
  refine (norm_P_Uval_le n m h (by omega) hh).trans ?_
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hL : (lcmUpto n : ℝ) ^ m ≤ Real.exp (m * (1.4563 * n + 1820)) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [lcmUpto_eq_finset_lcm]
    exact LcmChebyshevSharp.lcm_le_exp_lin' n
  have hB : (((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℕ) : ℝ) ≤
      ((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m := by
    have := choose_le_poly n m m le_rfl
    rw [← mul_pow]; exact_mod_cast this
  have hN : ((n : ℝ) + 1) ^ h ≤ ((n : ℝ) + 1) ^ m :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hh
  have hT := tail_le9 n (m + 1) hn (by omega)
  push_cast at hT
  unfold K0
  push_cast
  calc ((m.factorial : ℝ) * (lcmUpto n : ℝ) ^ m *
        (((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℕ) : ℝ) * ((n : ℝ) + 1) *
          2 ^ (n * (m + 1))) * ((n : ℝ) + 1) ^ h *
        (((2 * n + 1) * (Real.pi / 2)) ^ (n * (m + 1)) / ((n * (m + 1)).factorial : ℝ)) *
          Real.exp ((2 * n + 1) * (Real.pi / 2))
      ≤ ((m : ℝ) ^ m * Real.exp (m * (1.4563 * n + 1820)) *
        (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m) * ((n : ℝ) + 1) *
          2 ^ (n * (m + 1))) * ((n : ℝ) + 1) ^ m *
        (9 / ((m : ℝ) + 1)) ^ (n * (m + 1)) * Real.exp ((2 * n + 1) * (Real.pi / 2)) := by
        gcongr
    _ = _ := by ring


/-! ### Specialization: `m = 160`, `n = 4k + 2600` -/

lemma log_succ_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (x + 1) ≤ (x + 1) / 4096 - 1 + 12 * Real.log 2 := by
  have h := LcmChebyshevSharp.log_le_lin (x := x + 1) (δ := 1 / 4096) (by linarith) (by norm_num)
  have e : Real.log (1 / 4096 : ℝ) = - (12 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; push_cast; ring
  rw [e] at h; linarith

lemma log_160_le : Real.log 160 ≤ 8 * Real.log 2 := by
  have := Real.log_le_log (show (0:ℝ) < 160 by norm_num) (show (160:ℝ) ≤ 2 ^ 8 by norm_num)
  rw [Real.log_pow] at this; push_cast at this; linarith

lemma log_161_le : Real.log 161 ≤ 8 * Real.log 2 := by
  have := Real.log_le_log (show (0:ℝ) < 161 by norm_num) (show (161:ℝ) ≤ 2 ^ 8 by norm_num)
  rw [Real.log_pow] at this; push_cast at this; linarith

lemma log_3_le : Real.log 3 ≤ 2 * Real.log 2 := by
  have := Real.log_le_log (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ 2 ^ 2 by norm_num)
  rw [Real.log_pow] at this; push_cast at this; linarith

/-- `log(9/161) ≤ −4.16 log 2`, via `(9/161)^25 ≤ 2^-104`. -/
lemma log_9_161_le : Real.log (9 / 161) ≤ -(104 / 25) * Real.log 2 := by
  have h : ((9 : ℝ) / 161) ^ 25 ≤ (2 ^ 104)⁻¹ := by norm_num
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_inv, Real.log_pow] at h2
  push_cast at h2; linarith

theorem remainder_spec6 (k h : ℕ) (hh : h ≤ 160) :
    ‖(mahlerP (4 * k + 2600) 160 : ℂ) * Uval (4 * k + 2600) 160 h (Complex.I * (Real.pi / 2))‖ ≤
      1 / (2 * (2 * ((16 ^ k : ℕ) : ℝ)) ^ 160) := by
  refine (remainder_sharp (4 * k + 2600) 160 h (by omega) hh).trans ?_
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  set n : ℕ := 4 * k + 2600 with hn
  have hnR : (n : ℝ) = 4 * k + 2600 := by rw [hn]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  simp only [one_div, Real.log_inv]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_exp]
  simp only [Real.log_pow]
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  simp only [Real.log_pow]
  push_cast
  have e161 : (160 : ℝ) + 1 = 161 := by norm_num
  rw [e161, hnR]
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  rw [h16]
  have hl2 := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d4
  have hs := log_succ_le (x := 4 * (k : ℝ) + 2600) (by positivity)
  have h160 := log_160_le
  have h161 := log_161_le
  have h9 := log_9_161_le
  have hkl9 : (k : ℝ) * Real.log (9 / 161) ≤ (k : ℝ) * (-(104 / 25) * Real.log 2) :=
    mul_le_mul_of_nonneg_left h9 hk0
  have hkL : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hk0
  have hkpi : (k : ℝ) * Real.pi ≤ (k : ℝ) * 3.1416 := mul_le_mul_of_nonneg_left hpi.le hk0
  linarith

lemma sharpA_le (n m : ℕ) :
    sharpA n m ≤ (m : ℝ) ^ m * Real.exp (m * (1.4563 * n + 1820)) * 2 ^ (n * (m + 1)) *
      (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m) * ((n : ℝ) + 1) ^ m := by
  unfold sharpA
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hL : (lcmUpto n : ℝ) ^ m ≤ Real.exp (m * (1.4563 * n + 1820)) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [lcmUpto_eq_finset_lcm]
    exact LcmChebyshevSharp.lcm_le_exp_lin' n
  gcongr

/-- **`T` bound** for `m = 160`, `n = 4k + 2600`: `T ≤ 2^(1719840 + 1992 k)`. -/
theorem T_spec6 (k : ℕ) :
    ((160 : ℝ) + 1) * (160 : ℕ) * 3 ^ 160 * ((((4 * k + 2600 : ℕ) : ℝ) + 1) * sharpA (4 * k + 2600) 160)
      ≤ 2 ^ (1719840 + 1992 * k) := by
  have hA := sharpA_le (4 * k + 2600) 160
  have hpos : (0 : ℝ) ≤ ((160 : ℝ) + 1) * (160 : ℕ) * 3 ^ 160 * (((4 * k + 2600 : ℕ) : ℝ) + 1) := by
    positivity
  calc ((160 : ℝ) + 1) * (160 : ℕ) * 3 ^ 160 * ((((4 * k + 2600 : ℕ) : ℝ) + 1) * sharpA (4 * k + 2600) 160)
      = (((160 : ℝ) + 1) * (160 : ℕ) * 3 ^ 160 * (((4 * k + 2600 : ℕ) : ℝ) + 1)) *
          sharpA (4 * k + 2600) 160 := by ring
    _ ≤ (((160 : ℝ) + 1) * (160 : ℕ) * 3 ^ 160 * (((4 * k + 2600 : ℕ) : ℝ) + 1)) *
          ((((160 : ℕ) : ℝ)) ^ 160 * Real.exp (((160 : ℕ) : ℝ) * (1.4563 * ((4 * k + 2600 : ℕ) : ℝ) + 1820)) *
            2 ^ ((4 * k + 2600) * (160 + 1)) *
            (((((160 : ℕ) : ℝ)) + 1) ^ 160 * ((((4 * k + 2600 : ℕ) : ℝ)) + 1) ^ 160) *
              ((((4 * k + 2600 : ℕ) : ℝ)) + 1) ^ 160) := mul_le_mul_of_nonneg_left hA hpos
    _ ≤ 2 ^ (1719840 + 1992 * k) := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      repeat rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_exp]
      simp only [Real.log_pow]
      push_cast
      have e161 : (160 : ℝ) + 1 = 161 := by norm_num
      rw [e161]
      have hl2 := Real.log_two_gt_d9
      have hl2' := Real.log_two_lt_d9
      have hs := log_succ_le (x := 4 * (k : ℝ) + 2600) (by positivity)
      have h160 := log_160_le
      have h161 := log_161_le
      have h3 := log_3_le
      have hkL : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hl2'.le hk0
      have hkL' : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le hk0
      linarith

/-- **Round-6 explicit irrationality measure for π at `q = 16^k`**:
`|16^k π − p| · 16^(658 k) > 2^-1720001 · 16^k` for all `k ≥ 1`, `p ∈ ℤ`. -/
theorem pi_pow16_measure6 :
    ∀ k : ℕ, 1 ≤ k → ∀ p : ℤ,
      |(16 : ℝ) ^ k * Real.pi - p| * (16 : ℝ) ^ (k * 658) > (1 / 2 ^ (1720000 + 1)) * (16 : ℝ) ^ k := by
  intro k hk p
  set q : ℕ := 16 ^ k with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  have hqR : (q : ℝ) = (16 : ℝ) ^ k := by rw [hqdef]; push_cast; rfl
  have h16 : (0 : ℝ) < (16 : ℝ) ^ k := by positivity
  have hdist : |(16 : ℝ) ^ k * Real.pi - p| = (16 : ℝ) ^ k * |Real.pi - p / q| := by
    rw [hqR, ← abs_of_pos h16, ← abs_mul, abs_of_pos h16]
    congr 1; field_simp
  rw [hdist]
  have hC : (1 / 2 ^ (1720000 + 1) : ℝ) < 1 / 2 ^ 1720000 := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hmu : (16 : ℝ) ^ (k * 658) = 2 ^ (4 * k * 658) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]; ring_nf
  by_cases hclose : |Real.pi - p / q| ≤ 1
  · have hL := pi_lower_bound_sharp (4 * k + 2600) 160 q (by omega) hq1 p hclose
      (fun h hh => remainder_spec6 k h hh)
    have hT := T_spec6 k
    have hpos : 0 ≤ (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| :=
      mul_nonneg (pow_nonneg (by positivity) _) (abs_nonneg _)
    have h1 : 1 ≤ (2 * (q : ℝ)) ^ 160 * |Real.pi - p / q| * 2 ^ (1719840 + 1992 * k) := by
      refine hL.trans (mul_le_mul_of_nonneg_left ?_ hpos)
      simpa using hT
    have h2q : (2 * (q : ℝ)) ^ 160 = 2 ^ (160 + 640 * k) := by
      rw [hqR, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ', ← pow_mul]
      congr 1; ring
    rw [h2q] at h1
    have hcomb : (2 : ℝ) ^ (160 + 640 * k) * |Real.pi - p / q| * 2 ^ (1719840 + 1992 * k) =
        |Real.pi - p / q| * 2 ^ (4 * k * 658) * 2 ^ 1720000 := by
      rw [mul_comm ((2 : ℝ) ^ (160 + 640 * k)), mul_assoc, ← pow_add, mul_assoc, ← pow_add]
      congr 2; ring
    rw [hcomb] at h1
    have hA : (0 : ℝ) < 2 ^ 1720000 := by positivity
    have h3 : 1 / 2 ^ 1720000 ≤ |Real.pi - p / q| * 2 ^ (4 * k * 658) := by
      rw [div_le_iff₀ hA]; linarith
    rw [hmu]
    calc (1 / 2 ^ (1720000 + 1) : ℝ) * (16 : ℝ) ^ k < 1 / 2 ^ 1720000 * (16 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hC h16
      _ ≤ |Real.pi - p / q| * 2 ^ (4 * k * 658) * (16 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h3 h16.le
      _ = _ := by ring
  · push_neg at hclose
    have h1 : (1 : ℝ) ≤ 2 ^ (4 * k * 658) := one_le_pow₀ (by norm_num)
    have hC1 : (1 / 2 ^ (1720000 + 1) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
    rw [hmu]
    calc (1 / 2 ^ (1720000 + 1) : ℝ) * (16 : ℝ) ^ k < 1 * (16 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hC1 h16
      _ ≤ (16 : ℝ) ^ k * |Real.pi - p / q| * 2 ^ (4 * k * 658) := by
          rw [one_mul, mul_assoc]
          refine le_mul_of_one_le_right h16.le ?_
          nlinarith
      _ = _ := by ring

end MahlerSharp

#print axioms MahlerSharp.remainder_spec6
#print axioms MahlerSharp.T_spec6
#print axioms MahlerSharp.pi_pow16_measure6
