import Thoughts.Research.MahlerSharp

/-
Research file (Thoughts/Research/MahlerSharp7.lean). Round 7: μ 658 → 570.
* `psi_le_lin7`: ψ(x) ≤ (log 4 + 0.02)x + 11000  (round 6: +0.07, +1820), hence
  `lcm(1..n) ≤ exp(1.4063 n + 11000)`.
* tail `r^J/J! ≤ (8.55/(m+1))^J` for `n ≥ 1000` (uses π·e < 8.5398; round 6: 9/(m+1)).
* `log(n+1) ≤ (n+1)/2^17 − 1 + 17 log 2` (round 6: 2^-12).
* specialization `m = 141`, `n = 4k + 16000`; parameter search in `research/round7/params7.py`
  of the source repository metasecdev/irrational-gap-mobius (not copied here).
* superseded by `MahlerSharp7b.lean` (same μ = 570, constant `2^-7182802`).
-/

set_option backward.isDefEq.respectTransparency false

namespace LcmChebyshevSharp7
open Real Chebyshev Finset

lemma log_400_lt : Real.log 400 < 6.2384 := by
  have h : Real.log 400 ≤ Real.log (2 ^ 9) := Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  have := LcmChebyshevSharp.log_two_lt
  push_cast at h
  linarith

/-- `2 √x log x ≤ 0.02 x + 11000` for `x ≥ 1`. -/
lemma two_sqrt_log_le7 {x : ℝ} (hx : 1 ≤ x) : 2 * Real.sqrt x * Real.log x ≤ 0.02 * x + 11000 := by
  set s := Real.sqrt x with hs
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hx
  have hs0 : 0 < s := by linarith
  have hss : s * s = x := Real.mul_self_sqrt hx0
  have hlog : Real.log x = 2 * Real.log s := by
    rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
  have hl := LcmChebyshevSharp.log_le_lin hs0 (show (0 : ℝ) < 1 / 400 by norm_num)
  have h400 : Real.log (1 / 400 : ℝ) = - Real.log 400 := by
    rw [one_div, Real.log_inv]
  rw [h400] at hl
  have hl2 : Real.log s ≤ s / 400 + 5.2384 := by have := log_400_lt; linarith
  rw [hlog]
  have hsq : 0 ≤ (s - 1047.68) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hl2 hs0.le]

theorem psi_le_lin7 {x : ℝ} (hx : 1 ≤ x) : ψ x ≤ (Real.log 4 + 0.02) * x + 11000 := by
  have h1 := psi_le hx
  have h2 := two_sqrt_log_le7 hx
  nlinarith

theorem lcm_le_exp_lin7 (n : ℕ) :
    (((Icc 1 n).lcm id : ℕ) : ℝ) ≤ Real.exp (1.4063 * n + 11000) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine (LcmChebyshev.lcm_le_exp_psi n).trans (Real.exp_le_exp.mpr ?_)
    have := psi_le_lin7 (x := (n : ℝ)) (by exact_mod_cast hn)
    have := LcmChebyshevSharp.log_four_lt
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

end LcmChebyshevSharp7

namespace MahlerSharp7
open MahlerGeneral MahlerVanishing MahlerDet MahlerBounds MahlerMignotte MahlerRemainder MahlerSharp Finset


/-- `r^J/J! ≤ (8.55/M)^J` for `r = (2n+1)π/2`, `J = n·M`, `n ≥ 1000`, `M ≥ 1`
(round 6, `MahlerSharp.tail_le9`: `9/M` for `n ≥ 10`). -/
lemma tail_le855 (n M : ℕ) (hn : 1000 ≤ n) (hM : 1 ≤ M) :
    ((2 * n + 1) * (Real.pi / 2)) ^ (n * M) / ((n * M).factorial : ℝ) ≤ (8.55 / (M : ℝ)) ^ (n * M) := by
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
    _ ≤ (8.55 / (M : ℝ)) ^ J := by
        apply pow_le_pow_left₀ (by positivity)
        have he := Real.exp_one_lt_d9
        have hpi := Real.pi_lt_d4
        have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
        have hM' : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hJpos hM']
        simp only [r, J]
        push_cast
        have he0 := Real.exp_pos 1
        have hpe : Real.pi * Real.exp 1 ≤ 8.5398 := by
          have := mul_lt_mul'' hpi he Real.pi_pos.le he0.le
          norm_num at this; linarith
        have : (2 * (n : ℝ) + 1) * (Real.pi / 2) * Real.exp 1 ≤ 8.55 * n := by
          have e : (2 * (n : ℝ) + 1) * (Real.pi / 2) * Real.exp 1 =
              (2 * n + 1) * (Real.pi * Real.exp 1) / 2 := by ring
          rw [e]
          have h2n : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hpe h2n]
        nlinarith

/-- **Sharp remainder bound** (`n ≥ 1000`; tail factor `8.55/(m+1)`, `lcm` bound
`exp(1.4063 n + 11000)`). -/
theorem remainder_sharp7 (n m h : ℕ) (hn : 1000 ≤ n) (hh : h ≤ m) :
    ‖(mahlerP n m : ℂ) * Uval n m h (Complex.I * (Real.pi / 2))‖ ≤
      (m : ℝ) ^ m * Real.exp (m * (1.4063 * n + 11000)) * ((m : ℝ) + 1) ^ m *
        ((n : ℝ) + 1) ^ (2 * m + 1) * 2 ^ (n * (m + 1)) * (8.55 / ((m : ℝ) + 1)) ^ (n * (m + 1)) *
          Real.exp ((2 * n + 1) * (Real.pi / 2)) := by
  refine (norm_P_Uval_le n m h (by omega) hh).trans ?_
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hL : (lcmUpto n : ℝ) ^ m ≤ Real.exp (m * (1.4063 * n + 11000)) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [lcmUpto_eq_finset_lcm]
    exact LcmChebyshevSharp7.lcm_le_exp_lin7 n
  have hB : (((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℕ) : ℝ) ≤
      ((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m := by
    have := choose_le_poly n m m le_rfl
    rw [← mul_pow]; exact_mod_cast this
  have hN : ((n : ℝ) + 1) ^ h ≤ ((n : ℝ) + 1) ^ m :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hh
  have hT := tail_le855 n (m + 1) hn (by omega)
  push_cast at hT
  unfold K0
  push_cast
  calc ((m.factorial : ℝ) * (lcmUpto n : ℝ) ^ m *
        (((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℕ) : ℝ) * ((n : ℝ) + 1) *
          2 ^ (n * (m + 1))) * ((n : ℝ) + 1) ^ h *
        (((2 * n + 1) * (Real.pi / 2)) ^ (n * (m + 1)) / ((n * (m + 1)).factorial : ℝ)) *
          Real.exp ((2 * n + 1) * (Real.pi / 2))
      ≤ ((m : ℝ) ^ m * Real.exp (m * (1.4063 * n + 11000)) *
        (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m) * ((n : ℝ) + 1) *
          2 ^ (n * (m + 1))) * ((n : ℝ) + 1) ^ m *
        (8.55 / ((m : ℝ) + 1)) ^ (n * (m + 1)) * Real.exp ((2 * n + 1) * (Real.pi / 2)) := by
        gcongr
    _ = _ := by ring


/-! ### Specialization: `m = 141`, `n = 4k + 16000` -/

lemma log_succ_le7 {x : ℝ} (hx : 0 ≤ x) :
    Real.log (x + 1) ≤ (x + 1) / 131072 - 1 + 17 * Real.log 2 := by
  have h := LcmChebyshevSharp.log_le_lin (x := x + 1) (δ := 1 / 131072) (by linarith) (by norm_num)
  have e : Real.log (1 / 131072 : ℝ) = - (17 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (131072 : ℝ) = 2 ^ 17 by norm_num, Real.log_pow]; push_cast; ring
  rw [e] at h; linarith

lemma log_141_le : Real.log 141 ≤ 8 * Real.log 2 := by
  have := Real.log_le_log (show (0:ℝ) < 141 by norm_num) (show (141:ℝ) ≤ 2 ^ 8 by norm_num)
  rw [Real.log_pow] at this; push_cast at this; linarith

lemma log_142_le : Real.log 142 ≤ 8 * Real.log 2 := by
  have := Real.log_le_log (show (0:ℝ) < 142 by norm_num) (show (142:ℝ) ≤ 2 ^ 8 by norm_num)
  rw [Real.log_pow] at this; push_cast at this; linarith

lemma log_3_le : Real.log 3 ≤ 2 * Real.log 2 := by
  have := Real.log_le_log (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ 2 ^ 2 by norm_num)
  rw [Real.log_pow] at this; push_cast at this; linarith

/-- `log(8.55/142) ≤ −(81/20) log 2`, via `(8.55/142)^20 ≤ 2^-81`. -/
lemma log_855_142_le : Real.log (8.55 / 142) ≤ -(81 / 20) * Real.log 2 := by
  have h : ((8.55 : ℝ) / 142) ^ 20 ≤ (2 ^ 81)⁻¹ := by norm_num
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_inv, Real.log_pow] at h2
  push_cast at h2; linarith

theorem remainder_spec7 (k h : ℕ) (hh : h ≤ 141) :
    ‖(mahlerP (4 * k + 16000) 141 : ℂ) * Uval (4 * k + 16000) 141 h (Complex.I * (Real.pi / 2))‖ ≤
      1 / (2 * (2 * ((16 ^ k : ℕ) : ℝ)) ^ 141) := by
  refine (remainder_sharp7 (4 * k + 16000) 141 h (by omega) hh).trans ?_
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  set n : ℕ := 4 * k + 16000 with hn
  have hnR : (n : ℝ) = 4 * k + 16000 := by rw [hn]; push_cast; ring
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
  have e142 : (141 : ℝ) + 1 = 142 := by norm_num
  rw [e142, hnR]
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  rw [h16]
  have hl2 := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d4
  have hs := log_succ_le7 (x := 4 * (k : ℝ) + 16000) (by positivity)
  have h141 := log_141_le
  have h142 := log_142_le
  have h9 := log_855_142_le
  have hkl9 : (k : ℝ) * Real.log (8.55 / 142) ≤ (k : ℝ) * (-(81 / 20) * Real.log 2) :=
    mul_le_mul_of_nonneg_left h9 hk0
  have hkL : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hk0
  have hkpi : (k : ℝ) * Real.pi ≤ (k : ℝ) * 3.1416 := mul_le_mul_of_nonneg_left hpi.le hk0
  linarith

lemma sharpA_le7 (n m : ℕ) :
    sharpA n m ≤ (m : ℝ) ^ m * Real.exp (m * (1.4063 * n + 11000)) * 2 ^ (n * (m + 1)) *
      (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m) * ((n : ℝ) + 1) ^ m := by
  unfold sharpA
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hL : (lcmUpto n : ℝ) ^ m ≤ Real.exp (m * (1.4063 * n + 11000)) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [lcmUpto_eq_finset_lcm]
    exact LcmChebyshevSharp7.lcm_le_exp_lin7 n
  gcongr

/-- **`T` bound** for `m = 141`, `n = 4k + 16000`: `T ≤ 2^(9093800 + 1716 k)`. -/
theorem T_spec7 (k : ℕ) :
    ((141 : ℝ) + 1) * (141 : ℕ) * 3 ^ 141 * ((((4 * k + 16000 : ℕ) : ℝ) + 1) * sharpA (4 * k + 16000) 141)
      ≤ 2 ^ (9093800 + 1716 * k) := by
  have hA := sharpA_le7 (4 * k + 16000) 141
  have hpos : (0 : ℝ) ≤ ((141 : ℝ) + 1) * (141 : ℕ) * 3 ^ 141 * (((4 * k + 16000 : ℕ) : ℝ) + 1) := by
    positivity
  calc ((141 : ℝ) + 1) * (141 : ℕ) * 3 ^ 141 * ((((4 * k + 16000 : ℕ) : ℝ) + 1) * sharpA (4 * k + 16000) 141)
      = (((141 : ℝ) + 1) * (141 : ℕ) * 3 ^ 141 * (((4 * k + 16000 : ℕ) : ℝ) + 1)) *
          sharpA (4 * k + 16000) 141 := by ring
    _ ≤ (((141 : ℝ) + 1) * (141 : ℕ) * 3 ^ 141 * (((4 * k + 16000 : ℕ) : ℝ) + 1)) *
          ((((141 : ℕ) : ℝ)) ^ 141 * Real.exp (((141 : ℕ) : ℝ) * (1.4063 * ((4 * k + 16000 : ℕ) : ℝ) + 11000)) *
            2 ^ ((4 * k + 16000) * (141 + 1)) *
            (((((141 : ℕ) : ℝ)) + 1) ^ 141 * ((((4 * k + 16000 : ℕ) : ℝ)) + 1) ^ 141) *
              ((((4 * k + 16000 : ℕ) : ℝ)) + 1) ^ 141) := mul_le_mul_of_nonneg_left hA hpos
    _ ≤ 2 ^ (9093800 + 1716 * k) := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      repeat rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_exp]
      simp only [Real.log_pow]
      push_cast
      have e142 : (141 : ℝ) + 1 = 142 := by norm_num
      rw [e142]
      have hl2 := Real.log_two_gt_d9
      have hl2' := Real.log_two_lt_d9
      have hs := log_succ_le7 (x := 4 * (k : ℝ) + 16000) (by positivity)
      have h141 := log_141_le
      have h142 := log_142_le
      have h3 := log_3_le
      have hkL : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hl2'.le hk0
      have hkL' : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le hk0
      linarith

/-- **Round-7 explicit irrationality measure for π at `q = 16^k`**:
`|16^k π − p| · 16^(570 k) > 2^-9093942 · 16^k` for all `k ≥ 1`, `p ∈ ℤ`. -/
theorem pi_pow16_measure7 :
    ∀ k : ℕ, 1 ≤ k → ∀ p : ℤ,
      |(16 : ℝ) ^ k * Real.pi - p| * (16 : ℝ) ^ (k * 570) > (1 / 2 ^ (9093941 + 1)) * (16 : ℝ) ^ k := by
  intro k hk p
  set q : ℕ := 16 ^ k with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  have hqR : (q : ℝ) = (16 : ℝ) ^ k := by rw [hqdef]; push_cast; rfl
  have h16 : (0 : ℝ) < (16 : ℝ) ^ k := by positivity
  have hdist : |(16 : ℝ) ^ k * Real.pi - p| = (16 : ℝ) ^ k * |Real.pi - p / q| := by
    rw [hqR, ← abs_of_pos h16, ← abs_mul, abs_of_pos h16]
    congr 1; field_simp
  rw [hdist]
  have hC : (1 / 2 ^ (9093941 + 1) : ℝ) < 1 / 2 ^ 9093941 := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hmu : (16 : ℝ) ^ (k * 570) = 2 ^ (4 * k * 570) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]; ring_nf
  by_cases hclose : |Real.pi - p / q| ≤ 1
  · have hL := pi_lower_bound_sharp (4 * k + 16000) 141 q (by omega) hq1 p hclose
      (fun h hh => remainder_spec7 k h hh)
    have hT := T_spec7 k
    have hpos : 0 ≤ (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| :=
      mul_nonneg (pow_nonneg (by positivity) _) (abs_nonneg _)
    have h1 : 1 ≤ (2 * (q : ℝ)) ^ 141 * |Real.pi - p / q| * 2 ^ (9093800 + 1716 * k) := by
      refine hL.trans (mul_le_mul_of_nonneg_left ?_ hpos)
      simpa using hT
    have h2q : (2 * (q : ℝ)) ^ 141 = 2 ^ (141 + 564 * k) := by
      rw [hqR, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ', ← pow_mul]
      congr 1; ring
    rw [h2q] at h1
    have hcomb : (2 : ℝ) ^ (141 + 564 * k) * |Real.pi - p / q| * 2 ^ (9093800 + 1716 * k) =
        |Real.pi - p / q| * 2 ^ (4 * k * 570) * 2 ^ 9093941 := by
      rw [mul_comm ((2 : ℝ) ^ (141 + 564 * k)), mul_assoc, ← pow_add, mul_assoc, ← pow_add]
      congr 2; ring
    rw [hcomb] at h1
    have hA : (0 : ℝ) < 2 ^ 9093941 := by positivity
    have h3 : 1 / 2 ^ 9093941 ≤ |Real.pi - p / q| * 2 ^ (4 * k * 570) := by
      rw [div_le_iff₀ hA]; linarith
    rw [hmu]
    calc (1 / 2 ^ (9093941 + 1) : ℝ) * (16 : ℝ) ^ k < 1 / 2 ^ 9093941 * (16 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hC h16
      _ ≤ |Real.pi - p / q| * 2 ^ (4 * k * 570) * (16 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h3 h16.le
      _ = _ := by ring
  · push_neg at hclose
    have h1 : (1 : ℝ) ≤ 2 ^ (4 * k * 570) := one_le_pow₀ (by norm_num)
    have hC1 : (1 / 2 ^ (9093941 + 1) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
    rw [hmu]
    calc (1 / 2 ^ (9093941 + 1) : ℝ) * (16 : ℝ) ^ k < 1 * (16 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hC1 h16
      _ ≤ (16 : ℝ) ^ k * |Real.pi - p / q| * 2 ^ (4 * k * 570) := by
          rw [one_mul, mul_assoc]
          refine le_mul_of_one_le_right h16.le ?_
          nlinarith
      _ = _ := by ring

end MahlerSharp7

#print axioms LcmChebyshevSharp7.lcm_le_exp_lin7
#print axioms MahlerSharp7.pi_pow16_measure7
