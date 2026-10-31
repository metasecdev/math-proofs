import BBPPi.Mahler.Mignotte

/-!
# The analytic remainder estimate at `x = i`

Step 5b of the Mahler–Mignotte route: the analytic remainder estimate at `x = i`
(`log x = iπ/2`):
  ‖P · R_h(i)‖ ≤ Kc · r^J / J! · e^r,   r = (2n+1)·π/2,  J = n(m+1),
where `R_h(i) = Σ_k A_hk(i) (iπ/2)^k = Uval n m h (iπ/2)` and `Kc` is explicit.
-/

set_option backward.isDefEq.respectTransparency false

namespace BBPPi.MahlerRemainder
open BBPPi.MahlerGeneral BBPPi.MahlerVanishing BBPPi.MahlerDet BBPPi.MahlerBounds BBPPi.MahlerMignotte Finset

/-! ### Evaluating formal power series (finite combinations of exponentials) -/

/-- `v` is the value at `z` of the power series `F` (as a convergent series). -/
def HasEval (F : PowerSeries ℚ) (z v : ℂ) : Prop :=
  HasSum (fun N => ((PowerSeries.coeff N F : ℚ) : ℂ) * z ^ N) v

lemma HasEval.sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ) (z : ℂ) (v : ι → ℂ)
    (h : ∀ i ∈ s, HasEval (F i) z (v i)) : HasEval (∑ i ∈ s, F i) z (∑ i ∈ s, v i) := by
  unfold HasEval
  simp only [map_sum, Rat.cast_sum, sum_mul]
  exact hasSum_sum h

lemma HasEval.C_mul {F : PowerSeries ℚ} {z v : ℂ} (r : ℚ) (h : HasEval F z v) :
    HasEval (PowerSeries.C r * F) z (r * v) := by
  unfold HasEval
  convert h.mul_left (r : ℂ) using 1
  ext N
  rw [PowerSeries.coeff_C_mul]; push_cast; ring

lemma HasEval.mul_X_pow {F : PowerSeries ℚ} {z v : ℂ} (k : ℕ) (h : HasEval F z v) :
    HasEval (F * PowerSeries.X ^ k) z (v * z ^ k) := by
  unfold HasEval
  rw [← hasSum_nat_add_iff' k]
  have hz : ∑ i ∈ range k, ((PowerSeries.coeff i (F * PowerSeries.X ^ k) : ℚ) : ℂ) * z ^ i = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [mem_range] at hi
    rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]; simp
  rw [hz, sub_zero]
  convert h.mul_right (z ^ k) using 1
  ext N
  rw [PowerSeries.coeff_mul_X_pow', if_pos (by omega), Nat.add_sub_cancel, pow_add]; ring

lemma hasEval_rescale_exp (e : ℚ) (z : ℂ) :
    HasEval (PowerSeries.rescale e (PowerSeries.exp ℚ)) z (Complex.exp (e * z)) := by
  unfold HasEval
  rw [Complex.exp_eq_exp_ℂ]
  convert NormedSpace.expSeries_div_hasSum_exp ((e : ℂ) * z) using 1
  ext N
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [mul_pow, div_eq_mul_inv]
  ring

/-- `R_h(e^z) = Σ_{k ≤ m} Σ_{e ≤ n} A_hk[e] e^{ez} z^k`. -/
noncomputable def Rval (n m h : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range (m + 1), ∑ e ∈ range (n + 1),
    (rawACoeff n m h k e : ℂ) * Complex.exp (e * z) * z ^ k

theorem hasEval_RA (n m h : ℕ) (z : ℂ) : HasEval (RA n m h) z (Rval n m h z) := by
  unfold RA Rval
  refine HasEval.sum _ _ z _ fun k _ => HasEval.sum _ _ z _ fun e _ => ?_
  have := ((hasEval_rescale_exp (e : ℚ) z).C_mul (rawACoeff n m h k e)).mul_X_pow k
  convert this using 1

lemma exp_I_pi_div_two : Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
  rw [mul_comm, show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- at `z = iπ/2` (i.e. `x = e^z = i`), `Rval = Uval`. -/
theorem Rval_eq_Uval (n m h : ℕ) :
    Rval n m h (Complex.I * (Real.pi / 2)) = Uval n m h (Complex.I * (Real.pi / 2)) := by
  unfold Rval Uval
  refine sum_congr rfl fun k _ => ?_
  rw [aeval_Apoly, sum_mul]
  refine sum_congr rfl fun e _ => ?_
  rw [Complex.exp_nat_mul, exp_I_pi_div_two]

/-! ### Coefficient bound for `RA` -/

lemma binom_exp (x y : ℚ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, x ^ p.1 / (p.1.factorial : ℚ) * (y ^ p.2 / (p.2.factorial : ℚ)) =
      (x + y) ^ N / (N.factorial : ℚ) := by
  have := congrArg (PowerSeries.coeff N)
    (PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) x y)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at this
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, Algebra.algebraMap_self,
    RingHom.id_apply] at this
  convert this using 1
  · refine sum_congr rfl fun p _ => ?_; ring
  · ring

lemma coeff_RA (n m h N : ℕ) (hh : h ≤ m) :
    PowerSeries.coeff N (RA n m h) = ∑ p ∈ antidiagonal N,
      (n : ℚ) ^ p.1 / (p.1.factorial : ℚ) * (resSum n m (h + p.2) / (p.2.factorial : ℚ)) := by
  rw [RA_eq n m h hh, RSer_eq, PowerSeries.coeff_mul]
  refine sum_congr rfl fun p _ => ?_
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_mk]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- `K0 = m!·lcm(1..n)^m·C(n(m+1)-1+m, n(m+1)-1)·(n+1)·2^{n(m+1)}`. -/
noncomputable def K0 (n m : ℕ) : ℚ :=
  (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m *
    ((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℚ) * ((n : ℚ) + 1) * 2 ^ (n * (m + 1))

lemma K0_nonneg (n m : ℕ) : 0 ≤ K0 n m := by unfold K0; positivity

lemma P_resSum_abs_le' (n m s : ℕ) (hn : 1 ≤ n) :
    |(mahlerP n m : ℚ) * resSum n m s| ≤ K0 n m * ((n : ℚ) + 1) ^ s := by
  refine (P_resSum_abs_le n m s hn).trans ?_
  unfold K0
  have hsum : ∑ lam ∈ range (n + 1), ((n.choose lam : ℕ) : ℚ) ^ (m + 1) * ((1 : ℚ) + lam) ^ s ≤
      ((n : ℚ) + 1) * 2 ^ (n * (m + 1)) * ((n : ℚ) + 1) ^ s := by
    calc _ ≤ ∑ _lam ∈ range (n + 1), (2 : ℚ) ^ (n * (m + 1)) * ((n : ℚ) + 1) ^ s := by
          refine sum_le_sum fun lam hlam => ?_
          rw [mem_range] at hlam
          have h1 : ((n.choose lam : ℕ) : ℚ) ^ (m + 1) ≤ (2 : ℚ) ^ (n * (m + 1)) := by
            rw [pow_mul]
            exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.choose_le_two_pow n lam) _
          have h2 : ((1 : ℚ) + lam) ^ s ≤ ((n : ℚ) + 1) ^ s := by
            apply pow_le_pow_left₀ (by positivity)
            have : (lam : ℚ) ≤ n := by exact_mod_cast (show lam ≤ n by omega)
            linarith
          gcongr
      _ = _ := by simp; ring
  have hA : (0 : ℚ) ≤ (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m *
      ((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℚ) := by positivity
  calc _ ≤ (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m *
        ((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℚ) *
        (((n : ℚ) + 1) * 2 ^ (n * (m + 1)) * ((n : ℚ) + 1) ^ s) :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = _ := by ring

/-- `|P · [L^N] RA| ≤ K0 (n+1)^h (2n+1)^N / N!`, and it vanishes for `N < n(m+1)`. -/
lemma P_coeff_RA_abs_le (n m h N : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) :
    |(mahlerP n m : ℚ) * PowerSeries.coeff N (RA n m h)| ≤
      K0 n m * ((n : ℚ) + 1) ^ h * ((2 * n + 1 : ℚ) ^ N / (N.factorial : ℚ)) := by
  rw [coeff_RA n m h N hh, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hb := binom_exp (n : ℚ) ((n : ℚ) + 1) N
  rw [show (n : ℚ) + ((n : ℚ) + 1) = 2 * n + 1 by ring] at hb
  rw [← hb, mul_sum]
  refine sum_le_sum fun p _ => ?_
  have hr := P_resSum_abs_le' n m (h + p.2) hn
  have hf1 : (0 : ℚ) < (p.1.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  have hf2 : (0 : ℚ) < (p.2.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  have e1 : (mahlerP n m : ℚ) * ((n : ℚ) ^ p.1 / (p.1.factorial : ℚ) *
      (resSum n m (h + p.2) / (p.2.factorial : ℚ))) =
      ((n : ℚ) ^ p.1 / (p.1.factorial : ℚ) / (p.2.factorial : ℚ)) *
        ((mahlerP n m : ℚ) * resSum n m (h + p.2)) := by ring
  rw [e1, abs_mul, abs_of_nonneg (by positivity)]
  calc (n : ℚ) ^ p.1 / (p.1.factorial : ℚ) / (p.2.factorial : ℚ) *
        |(mahlerP n m : ℚ) * resSum n m (h + p.2)|
      ≤ (n : ℚ) ^ p.1 / (p.1.factorial : ℚ) / (p.2.factorial : ℚ) *
        (K0 n m * ((n : ℚ) + 1) ^ (h + p.2)) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by rw [pow_add]; field_simp

/-! ### The tail estimate -/

lemma hasSum_exp_shift (r : ℝ) (J : ℕ) (c : ℝ) :
    HasSum (fun N => if J ≤ N then c * (r ^ (N - J) / ((N - J).factorial : ℝ)) else 0)
      (c * Real.exp r) := by
  rw [← hasSum_nat_add_iff' J]
  have hz : ∑ i ∈ range J, (if J ≤ i then c * (r ^ (i - J) / ((i - J).factorial : ℝ)) else 0) = 0 :=
    sum_eq_zero fun i hi => by rw [mem_range] at hi; rw [if_neg (by omega)]
  rw [hz, sub_zero]
  have he : HasSum (fun N => r ^ N / (N.factorial : ℝ)) (Real.exp r) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp r
  convert he.mul_left c using 1
  ext N
  rw [if_pos (by omega), Nat.add_sub_cancel]

/-- **Remainder estimate.** For `n ≥ 1`, `h ≤ m`, and any `z`, with `r = (2n+1)‖z‖`,
`J = n(m+1)`:  `‖P · R_h(e^z)‖ ≤ K0·(n+1)^h · r^J/J! · e^r`. -/
theorem norm_P_Rval_le (n m h : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) (z : ℂ) :
    ‖(mahlerP n m : ℂ) * Rval n m h z‖ ≤
      (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h *
        (((2 * n + 1) * ‖z‖) ^ (n * (m + 1)) / ((n * (m + 1)).factorial : ℝ)) *
          Real.exp ((2 * n + 1) * ‖z‖) := by
  set J := n * (m + 1)
  set r : ℝ := (2 * n + 1) * ‖z‖ with hr
  set c : ℝ := (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h * (r ^ J / (J.factorial : ℝ)) with hc
  have hE := (hasEval_RA n m h z).mul_left (mahlerP n m : ℂ)
  have hg := hasSum_exp_shift r J c
  have hr0 : 0 ≤ r := by positivity
  have hc0 : 0 ≤ c := by
    have := K0_nonneg n m
    have : (0 : ℝ) ≤ (K0 n m : ℝ) := by exact_mod_cast this
    positivity
  refine hE.norm_le_of_bounded hg fun N => ?_
  by_cases hN : J ≤ N
  · rw [if_pos hN]
    have hb := P_coeff_RA_abs_le n m h N hn hh
    have hb' : ‖((mahlerP n m : ℚ) : ℂ) * ((PowerSeries.coeff N (RA n m h) : ℚ) : ℂ)‖ ≤
        (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h * ((2 * n + 1 : ℝ) ^ N / (N.factorial : ℝ)) := by
      rw [← Rat.cast_mul, Complex.norm_ratCast]
      have := (Rat.cast_le (K := ℝ)).mpr hb
      push_cast at this ⊢
      exact this
    rw [← mul_assoc, norm_mul, norm_pow]
    push_cast at hb' ⊢
    have hfac : (J.factorial : ℝ) * ((N - J).factorial : ℝ) ≤ (N.factorial : ℝ) := by
      have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add J (N - J))
      rw [show J + (N - J) = N by omega] at this
      exact_mod_cast this
    have hpos1 : (0 : ℝ) < (J.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos2 : (0 : ℝ) < ((N - J).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos3 : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hK : (0 : ℝ) ≤ (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h := by
      have : (0 : ℝ) ≤ (K0 n m : ℝ) := by exact_mod_cast K0_nonneg n m
      positivity
    calc ‖(mahlerP n m : ℂ) * ((PowerSeries.coeff N (RA n m h) : ℚ) : ℂ)‖ * ‖z‖ ^ N
        ≤ (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h * ((2 * n + 1 : ℝ) ^ N / (N.factorial : ℝ)) * ‖z‖ ^ N :=
          mul_le_mul_of_nonneg_right hb' (by positivity)
      _ = (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h * (r ^ N / (N.factorial : ℝ)) := by
          rw [hr, mul_pow]; ring
      _ ≤ (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h *
            (r ^ J / (J.factorial : ℝ) * (r ^ (N - J) / ((N - J).factorial : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hK
          rw [div_mul_div_comm, ← pow_add, show J + (N - J) = N by omega]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = c * (r ^ (N - J) / ((N - J).factorial : ℝ)) := by rw [hc]; ring
  · rw [if_neg hN]
    have h0 := RA_coeff_eq_zero n m h N hh (by omega)
    rw [h0]; simp

/-- **Remainder estimate at `x = i`**: `‖P · U_h(iπ/2)‖ ≤ K0 (n+1)^h r^J/J! e^r`,
`r = (2n+1)π/2`. -/
theorem norm_P_Uval_le (n m h : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) :
    ‖(mahlerP n m : ℂ) * Uval n m h (Complex.I * (Real.pi / 2))‖ ≤
      (K0 n m : ℝ) * ((n : ℝ) + 1) ^ h *
        (((2 * n + 1) * (Real.pi / 2)) ^ (n * (m + 1)) / ((n * (m + 1)).factorial : ℝ)) *
          Real.exp ((2 * n + 1) * (Real.pi / 2)) := by
  have hz : ‖Complex.I * ((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have := norm_P_Rval_le n m h hn hh (Complex.I * (Real.pi / 2))
  rw [Rval_eq_Uval, hz] at this
  exact this

end BBPPi.MahlerRemainder
