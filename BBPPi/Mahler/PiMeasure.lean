import BBPPi.Mahler.Remainder

/-!
# An explicit irrationality measure for π at denominators `16^k` (μ = 851967)

Step 5c of the Mahler–Mignotte route: choice of parameters and an **explicit, unconditional
irrationality-measure statement for π at denominators 16^k**:
  for all k ≥ 1 and p ∈ ℤ:  |16^k π − p| · 16^(k·μ) > C · 16^k,
with μ = 851967 and C = 1 / 2^17170446.  (Parameters: m = 2^17 − 1, n = 2k + 10.)
The statement is literally the body of `BBPPi.PiPow16Measure μ C`.
Constants are deliberately crude (Mathlib's ψ(x) ≤ (log 4 + 4) x, i.e. lcm(1..n) ≤ 219^n).
-/

set_option backward.isDefEq.respectTransparency false

namespace BBPPi.MahlerPiMeasure
open BBPPi.MahlerGeneral BBPPi.MahlerVanishing BBPPi.MahlerDet BBPPi.MahlerBounds BBPPi.MahlerMignotte BBPPi.MahlerRemainder Finset

lemma succ_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ 2 ^ n := by
  have := Nat.lt_pow_self (n := n) (by norm_num : 1 < 2)
  exact_mod_cast this

lemma lcm_le_two_pow (n : ℕ) : (lcmUpto n : ℝ) ≤ 2 ^ (8 * n) := by
  have h := LcmChebyshev.lcm_le_219_pow n
  rw [← lcmUpto_eq_finset_lcm] at h
  have h2 : 219 ^ n ≤ 2 ^ (8 * n) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) n
  exact_mod_cast h.trans h2

lemma fact_le (m : ℕ) : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
  exact_mod_cast Nat.factorial_le_pow m

/-- `K0 ≤ m^m 2^{8nm} 2^{J+m} 2^n 2^J`. -/
lemma K0_le (n m : ℕ) :
    (K0 n m : ℝ) ≤ (m : ℝ) ^ m * 2 ^ (8 * n * m) * 2 ^ (n * (m + 1) + m) * 2 ^ n *
      2 ^ (n * (m + 1)) := by
  unfold K0
  push_cast
  have hB : (((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℕ) : ℝ) ≤
      2 ^ (n * (m + 1) + m) := by
    have := Nat.choose_le_two_pow (n * (m + 1) - 1 + m) (n * (m + 1) - 1)
    have h2 : 2 ^ (n * (m + 1) - 1 + m) ≤ 2 ^ (n * (m + 1) + m) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this.trans h2
  have hL : (lcmUpto n : ℝ) ^ m ≤ 2 ^ (8 * n * m) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (lcm_le_two_pow n) m
  gcongr
  · exact fact_le m
  · exact succ_le_two_pow n

/-- `r^J/J! ≤ (16/M)^J` for `r = (2n+1)π/2`, `J = n·M`. -/
lemma tail_le (n M : ℕ) (hn : 1 ≤ n) (hM : 1 ≤ M) :
    ((2 * n + 1) * (Real.pi / 2)) ^ (n * M) / ((n * M).factorial : ℝ) ≤ (16 / (M : ℝ)) ^ (n * M) := by
  set J := n * M
  have hJpos : (0 : ℝ) < J := by positivity
  have hJ := Real.pow_div_factorial_le_exp (x := (J : ℝ)) hJpos.le J
  have hfac : (0 : ℝ) < (J.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos J
  set r : ℝ := (2 * n + 1) * (Real.pi / 2)
  have hr0 : 0 ≤ r := by positivity
  have e1 : r ^ J / (J.factorial : ℝ) = (r / J) ^ J * ((J : ℝ) ^ J / (J.factorial : ℝ)) := by
    rw [div_pow]; field_simp
  rw [e1]
  have hexp : Real.exp (J : ℝ) = Real.exp 1 ^ J := (Real.exp_one_pow J).symm
  calc (r / J) ^ J * ((J : ℝ) ^ J / (J.factorial : ℝ)) ≤ (r / J) ^ J * Real.exp 1 ^ J := by
        rw [← hexp]; exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (r / J * Real.exp 1) ^ J := by rw [mul_pow]
    _ ≤ (16 / (M : ℝ)) ^ J := by
        apply pow_le_pow_left₀ (by positivity)
        have he := Real.exp_one_lt_d9
        have hpi := Real.pi_lt_d2
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hM' : (0 : ℝ) < M := by exact_mod_cast hM
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hJpos hM']
        simp only [r, J]
        push_cast
        have he0 := Real.exp_pos 1
        have hpe : Real.pi * Real.exp 1 ≤ 9 := by
          have := mul_lt_mul'' hpi he Real.pi_pos.le he0.le
          norm_num at this; linarith
        have : (2 * (n : ℝ) + 1) * (Real.pi / 2) * Real.exp 1 ≤ 16 * n := by
          have e : (2 * (n : ℝ) + 1) * (Real.pi / 2) * Real.exp 1 =
              (2 * n + 1) * (Real.pi * Real.exp 1) / 2 := by ring
          rw [e]
          have h2n : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hpe h2n]
        nlinarith

lemma exp_le (n : ℕ) (hn : 1 ≤ n) : Real.exp ((2 * n + 1) * (Real.pi / 2)) ≤ 2 ^ (8 * n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := Real.pi_lt_d2
  have h1 : (2 * (n : ℝ) + 1) * (Real.pi / 2) ≤ (n : ℝ) * 5 := by nlinarith [Real.pi_pos]
  have h5 : Real.exp 5 ≤ 2 ^ 8 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp 1 ^ 5 = Real.exp 5 := by rw [Real.exp_one_pow]; norm_num
    rw [← this]
    have h0 := Real.exp_pos 1
    have : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ h0.le he.le 5
    norm_num at this ⊢
    linarith
  calc Real.exp ((2 * n + 1) * (Real.pi / 2)) ≤ Real.exp ((n : ℝ) * 5) := Real.exp_le_exp.mpr h1
    _ = Real.exp 5 ^ n := Real.exp_nat_mul 5 n
    _ ≤ (2 ^ 8) ^ n := pow_le_pow_left₀ (Real.exp_pos 5).le h5 n
    _ = 2 ^ (8 * n) := by rw [pow_mul]

/-- **Generic remainder bound in closed form**: `‖P·R_h(i)‖ ≤ m^m 2^m (2^15/(m+1))^{n(m+1)}`. -/
theorem remainder_closed (n m h : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) :
    ‖(mahlerP n m : ℂ) * Uval n m h (Complex.I * (Real.pi / 2))‖ ≤
      (m : ℝ) ^ m * 2 ^ m * ((2 : ℝ) ^ 15 / ((m : ℝ) + 1)) ^ (n * (m + 1)) := by
  refine (norm_P_Uval_le n m h hn hh).trans ?_
  set J := n * (m + 1)
  have hK := K0_le n m
  have hH : ((n : ℝ) + 1) ^ h ≤ 2 ^ (n * m) := by
    calc ((n : ℝ) + 1) ^ h ≤ ((n : ℝ) + 1) ^ m :=
          pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hh
      _ ≤ (2 ^ n) ^ m := pow_le_pow_left₀ (by positivity) (succ_le_two_pow n) m
      _ = 2 ^ (n * m) := by rw [pow_mul]
  have hT := tail_le n (m + 1) hn (by omega)
  have hE := exp_le n hn
  have hK0 : (0 : ℝ) ≤ (K0 n m : ℝ) := by exact_mod_cast K0_nonneg n m
  push_cast at hT
  calc (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h *
        (((2 * n + 1) * (Real.pi / 2)) ^ J / (J.factorial : ℝ)) *
          Real.exp ((2 * n + 1) * (Real.pi / 2))
      ≤ ((m : ℝ) ^ m * 2 ^ (8 * n * m) * 2 ^ (J + m) * 2 ^ n * 2 ^ J) * 2 ^ (n * m) *
          (16 / ((m : ℝ) + 1)) ^ J * 2 ^ (8 * n) := by
        gcongr
    _ = (m : ℝ) ^ m * 2 ^ m * ((2 : ℝ) ^ 15 / ((m : ℝ) + 1)) ^ J := by
        rw [div_pow, div_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]
        have hpow : (2 : ℝ) ^ (8 * n * m) * 2 ^ (J + m) * 2 ^ n * 2 ^ J * 2 ^ (n * m) *
            2 ^ (4 * J) * 2 ^ (8 * n) = 2 ^ m * 2 ^ (15 * J) := by
          simp only [← pow_add]
          congr 1
          simp only [J]; ring
        have hM : ((m : ℝ) + 1) ^ J ≠ 0 := by positivity
        field_simp
        linear_combination (m : ℝ) ^ m * hpow

/-- **Generic bound for Mignotte's `T`**: `(m+1) m 3^m ((n+1) crudeA) ≤ (m+1)^2 2^{2m} m^m 2^{n+9nm+2J+m}`. -/
theorem T_closed (n m : ℕ) :
    ((m : ℝ) + 1) * m * 3 ^ m * (((n : ℝ) + 1) * crudeA n m) ≤
      ((m : ℝ) + 1) ^ 2 * 2 ^ (2 * m) * (m : ℝ) ^ m *
        2 ^ (n + 8 * n * m + n * (m + 1) + (n * (m + 1) + m) + n * m) := by
  unfold crudeA
  have h3 : (3 : ℝ) ^ m ≤ 2 ^ (2 * m) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have h219 : (219 : ℝ) ^ (n * m) ≤ 2 ^ (8 * n * m) := by
    calc (219 : ℝ) ^ (n * m) ≤ (2 ^ 8) ^ (n * m) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = 2 ^ (8 * n * m) := by rw [← pow_mul]; ring_nf
  have h2 : (2 : ℝ) ^ (n * (m + 1) - 1 + m) ≤ 2 ^ (n * (m + 1) + m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hn1 : ((n : ℝ) + 1) ^ m ≤ 2 ^ (n * m) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (succ_le_two_pow n) m
  have hm : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  calc ((m : ℝ) + 1) * m * 3 ^ m * (((n : ℝ) + 1) * ((m.factorial : ℝ) * 219 ^ (n * m) *
        2 ^ (n * (m + 1)) * 2 ^ (n * (m + 1) - 1 + m) * ((n : ℝ) + 1) ^ m))
      ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) * 2 ^ (2 * m) * (2 ^ n * ((m : ℝ) ^ m * 2 ^ (8 * n * m) *
        2 ^ (n * (m + 1)) * 2 ^ (n * (m + 1) + m) * 2 ^ (n * m))) := by
        gcongr
        · exact succ_le_two_pow n
        · exact fact_le m
    _ = _ := by
        simp only [pow_add]; ring

/-! ### Specialization: `m = 2^17 - 1`, `n = 2k + 10` -/

/-- `m = 2^17 - 1`. -/
irreducible_def mm : ℕ := 131071

/-- the irrationality exponent `μ = m + 11·2^16`. -/
irreducible_def muPi : ℕ := 851967

/-- the exponent `A` in `C = 2^{-(A+1)}`. -/
irreducible_def Aexp : ℕ := 17170445

lemma mm_succ : (mm : ℝ) + 1 = 2 ^ 17 := by rw [mm_def]; norm_num

lemma mm_le : (mm : ℝ) ≤ 2 ^ 17 := by rw [mm_def]; norm_num

theorem remainder_spec (k h : ℕ) (hh : h ≤ mm) :
    ‖(mahlerP (2 * k + 10) mm : ℂ) * Uval (2 * k + 10) mm h (Complex.I * (Real.pi / 2))‖ ≤
      1 / (2 * (2 * ((16 ^ k : ℕ) : ℝ)) ^ mm) := by
  refine (remainder_closed (2 * k + 10) mm h (by omega) hh).trans ?_
  rw [mm_succ]
  have hq : (2 : ℝ) ^ 15 / 2 ^ 17 = (2 ^ 2)⁻¹ := by norm_num
  rw [hq]
  have hmm : (mm : ℝ) ^ mm ≤ (2 ^ 17) ^ mm := pow_le_pow_left₀ (by positivity) mm_le mm
  have h16 : (2 * ((16 ^ k : ℕ) : ℝ)) ^ mm = 2 ^ (mm + 4 * k * mm) := by
    push_cast
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ', ← pow_mul]
    congr 1; ring
  rw [h16, inv_pow, ← pow_mul]
  have hexp : 17 * mm + mm + (1 + (mm + 4 * k * mm)) ≤ 2 * ((2 * k + 10) * (mm + 1)) := by
    rw [mm_def]; ring_nf; omega
  have hpos : (0 : ℝ) < 2 ^ (2 * ((2 * k + 10) * (mm + 1))) := by positivity
  rw [le_div_iff₀ (by positivity)]
  calc (mm : ℝ) ^ mm * 2 ^ mm * ((2 : ℝ) ^ (2 * ((2 * k + 10) * (mm + 1))))⁻¹ *
        (2 * 2 ^ (mm + 4 * k * mm))
      ≤ (2 ^ 17) ^ mm * 2 ^ mm * ((2 : ℝ) ^ (2 * ((2 * k + 10) * (mm + 1))))⁻¹ *
        (2 * 2 ^ (mm + 4 * k * mm)) := by gcongr
    _ = 2 ^ (17 * mm + mm + (1 + (mm + 4 * k * mm))) *
          ((2 : ℝ) ^ (2 * ((2 * k + 10) * (mm + 1))))⁻¹ := by
        rw [← pow_mul]; simp only [pow_add, pow_one]; ring
    _ ≤ 2 ^ (2 * ((2 * k + 10) * (mm + 1))) * ((2 : ℝ) ^ (2 * ((2 * k + 10) * (mm + 1))))⁻¹ := by
        gcongr
        · norm_num
    _ = 1 := by field_simp

theorem T_spec (k : ℕ) :
    ((mm : ℝ) + 1) * mm * 3 ^ mm * ((((2 * k + 10 : ℕ) : ℝ) + 1) * crudeA (2 * k + 10) mm) ≤
      2 ^ (Aexp - mm + 4 * k * muPi - 4 * k * mm) := by
  refine (T_closed (2 * k + 10) mm).trans ?_
  rw [mm_succ]
  have hmm : (mm : ℝ) ^ mm ≤ (2 ^ 17) ^ mm := pow_le_pow_left₀ (by positivity) mm_le mm
  calc ((2 : ℝ) ^ 17) ^ 2 * 2 ^ (2 * mm) * (mm : ℝ) ^ mm * 2 ^ ((2 * k + 10) +
        8 * (2 * k + 10) * mm + (2 * k + 10) * (mm + 1) + ((2 * k + 10) * (mm + 1) + mm) +
        (2 * k + 10) * mm)
      ≤ ((2 : ℝ) ^ 17) ^ 2 * 2 ^ (2 * mm) * (2 ^ 17) ^ mm * 2 ^ ((2 * k + 10) +
        8 * (2 * k + 10) * mm + (2 * k + 10) * (mm + 1) + ((2 * k + 10) * (mm + 1) + mm) +
        (2 * k + 10) * mm) := by gcongr
    _ = 2 ^ (34 + 2 * mm + 17 * mm + ((2 * k + 10) +
        8 * (2 * k + 10) * mm + (2 * k + 10) * (mm + 1) + ((2 * k + 10) * (mm + 1) + mm) +
        (2 * k + 10) * mm)) := by
        simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (Aexp - mm + 4 * k * muPi - 4 * k * mm) := by
        apply pow_le_pow_right₀ (by norm_num)
        rw [mm_def, muPi_def, Aexp_def]
        ring_nf
        omega

/-- **Explicit irrationality measure for π at `q = 16^k`** (unconditional):
`|16^k π − p| · 16^(k μ) > C · 16^k` with `μ = 851967`, `C = 1/2^17170446`.
This is exactly `BBPPi.PiPow16Measure muPi (1 / 2 ^ (Aexp + 1))`. -/
theorem pi_pow16_measure :
    ∀ k : ℕ, 1 ≤ k → ∀ p : ℤ,
      |(16 : ℝ) ^ k * Real.pi - p| * (16 : ℝ) ^ (k * muPi) > (1 / 2 ^ (Aexp + 1)) * (16 : ℝ) ^ k := by
  intro k hk p
  set q : ℕ := 16 ^ k with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  have hqR : (q : ℝ) = (16 : ℝ) ^ k := by rw [hqdef]; push_cast; rfl
  have h16 : (0 : ℝ) < (16 : ℝ) ^ k := by positivity
  have hdist : |(16 : ℝ) ^ k * Real.pi - p| = (16 : ℝ) ^ k * |Real.pi - p / q| := by
    rw [hqR, ← abs_of_pos h16, ← abs_mul, abs_of_pos h16]
    congr 1; field_simp
  rw [hdist]
  have hC : (1 / 2 ^ (Aexp + 1) : ℝ) < 1 / 2 ^ Aexp := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hmu : (16 : ℝ) ^ (k * muPi) = 2 ^ (4 * k * muPi) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]; ring_nf
  by_cases hclose : |Real.pi - p / q| ≤ 1
  · -- Mahler–Mignotte
    have hL := pi_lower_bound (2 * k + 10) mm q (by omega) hq1 p hclose
      (fun h hh => remainder_spec k h hh)
    have hT := T_spec k
    have hpos : 0 ≤ (2 * (q : ℝ)) ^ mm * |Real.pi - p / q| :=
      mul_nonneg (pow_nonneg (by positivity) _) (abs_nonneg _)
    have h1 : 1 ≤ (2 * (q : ℝ)) ^ mm * |Real.pi - p / q| *
        2 ^ (Aexp - mm + 4 * k * muPi - 4 * k * mm) :=
      hL.trans (mul_le_mul_of_nonneg_left hT hpos)
    have h2q : (2 * (q : ℝ)) ^ mm = 2 ^ (mm + 4 * k * mm) := by
      rw [hqR, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ', ← pow_mul]
      congr 1; ring
    rw [h2q] at h1
    have hcomb : (2 : ℝ) ^ (mm + 4 * k * mm) * |Real.pi - p / q| *
        2 ^ (Aexp - mm + 4 * k * muPi - 4 * k * mm) =
        |Real.pi - p / q| * 2 ^ (4 * k * muPi) * 2 ^ Aexp := by
      have e : mm + 4 * k * mm + (Aexp - mm + 4 * k * muPi - 4 * k * mm) = 4 * k * muPi + Aexp := by
        rw [mm_def, muPi_def, Aexp_def]; ring_nf; omega
      calc (2 : ℝ) ^ (mm + 4 * k * mm) * |Real.pi - p / q| *
            2 ^ (Aexp - mm + 4 * k * muPi - 4 * k * mm)
          = |Real.pi - p / q| * 2 ^ (mm + 4 * k * mm + (Aexp - mm + 4 * k * muPi - 4 * k * mm)) := by
            rw [pow_add (2 : ℝ) (mm + 4 * k * mm)]; ring
        _ = |Real.pi - p / q| * 2 ^ (4 * k * muPi + Aexp) := by rw [e]
        _ = _ := by rw [pow_add]; ring
    rw [hcomb] at h1
    have hA : (0 : ℝ) < 2 ^ Aexp := by positivity
    have h3 : 1 / 2 ^ Aexp ≤ |Real.pi - p / q| * 2 ^ (4 * k * muPi) := by
      rw [div_le_iff₀ hA]; linarith
    rw [hmu]
    calc (1 / 2 ^ (Aexp + 1) : ℝ) * (16 : ℝ) ^ k < 1 / 2 ^ Aexp * (16 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hC h16
      _ ≤ |Real.pi - p / q| * 2 ^ (4 * k * muPi) * (16 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h3 h16.le
      _ = _ := by ring
  · -- far approximations are trivial
    push_neg at hclose
    have h1 : (1 : ℝ) ≤ 2 ^ (4 * k * muPi) := one_le_pow₀ (by norm_num)
    have hC1 : (1 / 2 ^ (Aexp + 1) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
    rw [hmu]
    calc (1 / 2 ^ (Aexp + 1) : ℝ) * (16 : ℝ) ^ k < 1 * (16 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hC1 h16
      _ ≤ (16 : ℝ) ^ k * |Real.pi - p / q| * 2 ^ (4 * k * muPi) := by
          rw [one_mul, mul_assoc]
          refine le_mul_of_one_le_right h16.le ?_
          nlinarith
      _ = _ := by ring

end BBPPi.MahlerPiMeasure
