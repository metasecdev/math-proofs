import BBPPi.Mahler.Vanishing
import BBPPi.Mahler.LcmChebyshev

/-!
# Hermite–Padé approximants: coefficient bounds

Step 2 of the Mahler–Mignotte route: explicit size bounds (coefficientwise majorants) for the
local series `Wser · (X-λ)^s`, hence for the Hermite–Padé coefficients `P · A_hk[e]` and for the
remainder coefficients `P · resSum(s)`.
-/

set_option backward.isDefEq.respectTransparency false

namespace BBPPi.MahlerBounds
open BBPPi.MahlerGeneral BBPPi.MahlerVanishing PowerSeries Finset

/-- coefficientwise majorant: `|[X^j] F| ≤ [X^j] G` for all `j`. -/
def Maj (F G : PowerSeries ℚ) : Prop := ∀ j, |coeff j F| ≤ coeff j G

lemma Maj.nonneg {F G : PowerSeries ℚ} (h : Maj F G) (j : ℕ) : 0 ≤ coeff j G :=
  (abs_nonneg _).trans (h j)

lemma Maj.mul {F G F' G' : PowerSeries ℚ} (h : Maj F G) (h' : Maj F' G') :
    Maj (F * F') (G * G') := by
  intro j
  rw [coeff_mul, coeff_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) (h.nonneg _)

lemma Maj.one : Maj 1 1 := by
  intro j; rw [coeff_one]; split_ifs <;> simp

lemma Maj.prod {ι : Type*} (s : Finset ι) (F G : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, Maj (F i) (G i)) : Maj (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Maj.one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- `(1-X)^{-(m+1)} = Σ_j C(m+j, m) X^j`. -/
noncomputable def chooseSer (m : ℕ) : PowerSeries ℚ := mk fun j => ((m + j).choose m : ℚ)

lemma chooseSer_mul (m : ℕ) : chooseSer m * (1 - X) ^ (m + 1) = 1 :=
  mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := m)

lemma coeff_chooseSer (m j : ℕ) : coeff j (chooseSer m) = ((m + j).choose m : ℚ) := coeff_mk _ _

/-- `chooseSer m ^ n = chooseSer (n(m+1) - 1)` for `n ≥ 1`. -/
lemma chooseSer_pow (m n : ℕ) (hn : 1 ≤ n) : chooseSer m ^ n = chooseSer (n * (m + 1) - 1) := by
  have hK : n * (m + 1) - 1 + 1 = n * (m + 1) := by
    have : 1 ≤ n * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h1 : chooseSer m ^ n * (1 - X) ^ (n * (m + 1)) = 1 := by
    rw [pow_mul', ← mul_pow, chooseSer_mul, one_pow]
  have h2 := chooseSer_mul (n * (m + 1) - 1)
  rw [hK] at h2
  have hne : ((1 : PowerSeries ℚ) - X) ^ (n * (m + 1)) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := congrArg (coeff 0) h0
    simp at this
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

lemma invPow_maj (m : ℕ) (c : ℚ) (hc : 1 ≤ |c|) :
    Maj (invPow m c) (C (|c| ^ (m + 1))⁻¹ * chooseSer m) := by
  intro j
  rw [invPow, coeff_C_mul, coeff_mk, coeff_C_mul, coeff_chooseSer, Nat.choose_symm_add,
    abs_mul, abs_mul, abs_inv, abs_pow, abs_pow, abs_neg, abs_inv, Nat.abs_cast]
  have h0 : 0 < |c| := by linarith
  have hj : (|c|⁻¹) ^ j ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hc)
  have hch : (0 : ℚ) ≤ ((m + j).choose j : ℚ) := by positivity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_of_le_one_left hch hj

lemma prod_abs_dist (n lam : ℕ) (hlam : lam ≤ n) :
    ∏ μ ∈ (range (n + 1)).erase lam, |((μ : ℚ) - lam)| =
      ((lam.factorial * (n - lam).factorial : ℕ) : ℚ) := by
  rw [← natAbs_prod_dist n lam hlam, Nat.cast_natAbs, Int.cast_abs, Int.cast_prod, abs_prod]
  push_cast; rfl

/-- majorant of the local inverse series `W_λ`. -/
lemma Wser_maj (n m lam : ℕ) (hlam : lam ≤ n) :
    Maj (Wser n m lam)
      (C ((((lam.factorial * (n - lam).factorial : ℕ) : ℚ)) ^ (m + 1))⁻¹ * chooseSer m ^ n) := by
  have h := Maj.prod ((range (n + 1)).erase lam) (fun μ => invPow m ((μ : ℚ) - lam))
    (fun μ => C (|((μ : ℚ) - lam)| ^ (m + 1))⁻¹ * chooseSer m) (fun μ hμ => by
      apply invPow_maj
      have hne : μ ≠ lam := Finset.ne_of_mem_erase hμ
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · rw [abs_of_neg (by rw [sub_neg]; exact_mod_cast h)]
        have : (μ : ℚ) + 1 ≤ lam := by exact_mod_cast h
        linarith
      · rw [abs_of_pos (by rw [sub_pos]; exact_mod_cast h)]
        have : (lam : ℚ) + 1 ≤ μ := by exact_mod_cast h
        linarith)
  have hcard : ((range (n + 1)).erase lam).card = n := by
    rw [card_erase_of_mem (by rw [mem_range]; omega), card_range]; rfl
  rw [Wser]
  convert h using 1
  rw [prod_mul_distrib, prod_const, hcard, ← map_prod, ← prod_abs_dist n lam hlam]
  congr 2
  rw [← prod_pow, prod_inv_distrib]

lemma coeff_X_add_C_pow' (r : ℚ) (h j : ℕ) :
    coeff j ((X + C r) ^ h : PowerSeries ℚ) = r ^ (h - j) * (h.choose j : ℚ) := by
  have : ((X + C r) ^ h : PowerSeries ℚ) =
      Polynomial.coeToPowerSeries.ringHom ((Polynomial.X + Polynomial.C r) ^ h) := by
    rw [map_pow, map_add, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]
  rw [this, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
    Polynomial.coeff_X_add_C_pow]

lemma shiftX_pow_maj (lam s : ℕ) : Maj (shiftX lam ^ s) ((X + C (lam : ℚ)) ^ s) := by
  intro j
  rw [shiftX, coeff_X_add_C_pow', coeff_X_add_C_pow', abs_mul, abs_pow, abs_neg, Nat.abs_cast,
    Nat.abs_cast]

/-- `[X^j] (chooseSer (K) · (X+λ)^s) ≤ C(K+j, K) · (1+λ)^s`. -/
lemma coeff_chooseSer_mul_le (K lam s j : ℕ) :
    coeff j (chooseSer K * (X + C (lam : ℚ)) ^ s) ≤
      ((K + j).choose K : ℚ) * ((1 : ℚ) + lam) ^ s := by
  rw [coeff_mul]
  set c : ℕ → ℚ := fun i => (lam : ℚ) ^ (s - i) * (s.choose i : ℚ) with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by positivity
  calc ∑ p ∈ antidiagonal j, coeff p.1 (chooseSer K) * coeff p.2 ((X + C (lam : ℚ)) ^ s)
      ≤ ∑ p ∈ antidiagonal j, ((K + j).choose K : ℚ) * c p.2 := by
        refine sum_le_sum fun p hp => ?_
        rw [mem_antidiagonal] at hp
        rw [coeff_chooseSer, coeff_X_add_C_pow']
        apply mul_le_mul_of_nonneg_right _ (hc0 _)
        exact_mod_cast Nat.choose_le_choose K (by omega)
    _ = ((K + j).choose K : ℚ) * ∑ i ∈ range (j + 1), c i := by
        rw [← mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ b => c b)]
        congr 1
        rw [← Finset.sum_range_reflect c (j + 1)]
        refine sum_congr rfl fun k _ => ?_
        congr 1
    _ ≤ ((K + j).choose K : ℚ) * ((1 : ℚ) + lam) ^ s := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsum0 : ((1 : ℚ) + lam) ^ s = ∑ i ∈ range (s + 1), c i := by
          rw [add_pow]; refine sum_congr rfl fun i _ => ?_; simp [hc]
        have hsub : ∑ i ∈ range (s + 1), c i = ∑ i ∈ range (j + s + 1), c i :=
          sum_subset (range_subset_range.mpr (by omega)) fun i _ hi => by
            rw [mem_range] at hi; simp [hc, Nat.choose_eq_zero_of_lt (show s < i by omega)]
        rw [hsum0, hsub]
        exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun i _ _ => hc0 i

/-- **Core coefficient bound** (any `s`, `n ≥ 1`):
`|[X^j] (W_λ · (X-λ)^s)| ≤ C(n(m+1)-1+j, n(m+1)-1) · (1+λ)^s / (λ!(n-λ)!)^{m+1}`. -/
theorem coeff_Wser_shift_abs_le (n m lam s j : ℕ) (hn : 1 ≤ n) (hlam : lam ≤ n) :
    |coeff j (Wser n m lam * shiftX lam ^ s)| ≤
      ((n * (m + 1) - 1 + j).choose (n * (m + 1) - 1) : ℚ) * ((1 : ℚ) + lam) ^ s /
        (((lam.factorial * (n - lam).factorial : ℕ) : ℚ)) ^ (m + 1) := by
  have h := ((Wser_maj n m lam hlam).mul (shiftX_pow_maj lam s)) j
  set a : ℚ := (((lam.factorial * (n - lam).factorial : ℕ) : ℚ) ^ (m + 1))⁻¹ with ha
  have e : coeff j (C a * chooseSer m ^ n * (X + C (lam : ℚ)) ^ s) =
      a * coeff j (chooseSer (n * (m + 1) - 1) * (X + C (lam : ℚ)) ^ s) := by
    rw [mul_assoc, coeff_C_mul, chooseSer_pow m n hn]
  rw [e] at h
  have h2 := coeff_chooseSer_mul_le (n * (m + 1) - 1) lam s j
  have ha0 : 0 ≤ a := by positivity
  calc _ ≤ _ := h
    _ ≤ a * (((n * (m + 1) - 1 + j).choose (n * (m + 1) - 1) : ℚ) * ((1 : ℚ) + lam) ^ s) :=
        mul_le_mul_of_nonneg_left h2 ha0
    _ = _ := by rw [ha, div_eq_inv_mul]

/-- **Explicit bound on the Hermite–Padé coefficients** `P · A_hk[e]`
(the integers of `integral_coeffs_general`):
`|P·A_hk[e]| ≤ (m!/k!) · lcm(1..n)^m · C(n,e)^{m+1} · C(n(m+1)-1+(m-k), n(m+1)-1) · (n+1)^h`. -/
theorem PA_abs_le (n m h k e : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) (hk : k ≤ m) (he : e ≤ n) :
    |(mahlerP n m : ℚ) * rawACoeff n m h k e| ≤
      (m.factorial : ℚ) / k.factorial * (lcmUpto n : ℚ) ^ m * ((n.choose e : ℕ) : ℚ) ^ (m + 1) *
        ((n * (m + 1) - 1 + (m - k)).choose (n * (m + 1) - 1) : ℚ) * ((n : ℚ) + 1) ^ h := by
  have hlam : n - e ≤ n := by omega
  have hb := coeff_Wser_shift_abs_le n m (n - e) h (m - k) hn hlam
  rw [rawACoeff, if_pos ⟨hh, hk, he⟩]
  simp only
  rw [gSeries_eq_coeff]
  simp only
  have hfac : ((n.choose e : ℕ) : ℚ) * (((n - e).factorial * (n - (n - e)).factorial : ℕ) : ℚ) =
      (n.factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial he
    rw [show n - (n - e) = e by omega]
    push_cast
    rw [← this]; push_cast; ring
  have hk0 : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hD : (0 : ℚ) < (((n - e).factorial * (n - (n - e)).factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hlam1 : ((1 : ℚ) + ((n - e : ℕ) : ℚ)) ^ h ≤ ((n : ℚ) + 1) ^ h := by
    apply pow_le_pow_left₀ (by positivity)
    have : ((n - e : ℕ) : ℚ) ≤ n := by exact_mod_cast hlam
    linarith
  rw [mahlerP, abs_mul, abs_div, Nat.abs_cast, Nat.abs_cast]
  push_cast
  set G := coeff (m - k) (Wser n m (n - e) * shiftX (n - e) ^ h)
  set D : ℚ := (((n - e).factorial * (n - (n - e)).factorial : ℕ) : ℚ)
  set B : ℚ := ((n * (m + 1) - 1 + (m - k)).choose (n * (m + 1) - 1) : ℚ)
  have hB : 0 ≤ B := by positivity
  have hnf : (n.factorial : ℚ) ^ (m + 1) = ((n.choose e : ℕ) : ℚ) ^ (m + 1) * D ^ (m + 1) := by
    rw [← hfac, mul_pow]
  rw [hnf]
  have hG : |G| * D ^ (m + 1) ≤ B * ((n : ℚ) + 1) ^ h := by
    have := hb
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [hlam1]
  have hL : (0 : ℚ) ≤ (lcmUpto n : ℚ) ^ m := by positivity
  have hC : (0 : ℚ) ≤ ((n.choose e : ℕ) : ℚ) ^ (m + 1) := by positivity
  have hm : (0 : ℚ) ≤ (m.factorial : ℚ) := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hki : (0 : ℚ) ≤ (k.factorial : ℚ)⁻¹ := by positivity
  calc (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m * (((n.choose e : ℕ) : ℚ) ^ (m + 1) * D ^ (m + 1)) *
        (|G| * (k.factorial : ℚ)⁻¹)
      = (m.factorial : ℚ) * (k.factorial : ℚ)⁻¹ * (lcmUpto n : ℚ) ^ m *
          ((n.choose e : ℕ) : ℚ) ^ (m + 1) * (|G| * D ^ (m + 1)) := by ring
    _ ≤ (m.factorial : ℚ) * (k.factorial : ℚ)⁻¹ * (lcmUpto n : ℚ) ^ m *
          ((n.choose e : ℕ) : ℚ) ^ (m + 1) * (B * ((n : ℚ) + 1) ^ h) := by
        apply mul_le_mul_of_nonneg_left hG; positivity
    _ = _ := by ring

/-- **Remainder-coefficient bound** (any `s`, `n ≥ 1`):
`|P · resSum(s)| ≤ m! · lcm(1..n)^m · C(n(m+1)-1+m, n(m+1)-1) · Σ_λ C(n,λ)^{m+1} (1+λ)^s`. -/
theorem P_resSum_abs_le (n m s : ℕ) (hn : 1 ≤ n) :
    |(mahlerP n m : ℚ) * resSum n m s| ≤
      (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m *
        ((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℚ) *
          ∑ lam ∈ range (n + 1), ((n.choose lam : ℕ) : ℚ) ^ (m + 1) * ((1 : ℚ) + lam) ^ s := by
  rw [resSum_eq_sum, mul_sum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun lam hlam => ?_)
  rw [mem_range] at hlam
  have hl : lam ≤ n := by omega
  have hb := coeff_Wser_shift_abs_le n m lam s m hn hl
  set D : ℚ := (((lam.factorial * (n - lam).factorial : ℕ) : ℚ))
  have hD : 0 < D := by positivity
  have hfac : ((n.choose lam : ℕ) : ℚ) * D = (n.factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial hl
    simp only [D]; push_cast; rw [← this]; push_cast; ring
  rw [abs_mul, Nat.abs_cast, mahlerP]
  push_cast
  rw [← hfac, mul_pow]
  set G := coeff m (Wser n m lam * shiftX lam ^ s)
  set B : ℚ := ((n * (m + 1) - 1 + m).choose (n * (m + 1) - 1) : ℚ)
  have hG : |G| * D ^ (m + 1) ≤ B * ((1 : ℚ) + lam) ^ s := by
    rw [le_div_iff₀ (by positivity)] at hb; exact hb
  calc (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m *
        (((n.choose lam : ℕ) : ℚ) ^ (m + 1) * D ^ (m + 1)) * |G|
      = (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m * ((n.choose lam : ℕ) : ℚ) ^ (m + 1) *
          (|G| * D ^ (m + 1)) := by ring
    _ ≤ (m.factorial : ℚ) * (lcmUpto n : ℚ) ^ m * ((n.choose lam : ℕ) : ℚ) ^ (m + 1) *
          (B * ((1 : ℚ) + lam) ^ s) := by
        apply mul_le_mul_of_nonneg_left hG; positivity
    _ = _ := by ring

/-- crude closed form: `|P · A_hk[e]| ≤ m! · 219^{nm} · 2^{n(m+1)} · 2^{n(m+1)+m-1} · (n+1)^m`. -/
theorem PA_abs_le_crude (n m h k e : ℕ) (hn : 1 ≤ n) (hh : h ≤ m) (hk : k ≤ m) (he : e ≤ n) :
    |(mahlerP n m : ℚ) * rawACoeff n m h k e| ≤
      (m.factorial : ℚ) * 219 ^ (n * m) * 2 ^ (n * (m + 1)) * 2 ^ (n * (m + 1) - 1 + m) *
        ((n : ℚ) + 1) ^ m := by
  refine (PA_abs_le n m h k e hn hh hk he).trans ?_
  have hL : (lcmUpto n : ℚ) ≤ 219 ^ n := by
    rw [lcmUpto_eq_finset_lcm]; exact_mod_cast LcmChebyshev.lcm_le_219_pow n
  have hC : ((n.choose e : ℕ) : ℚ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n e
  have hB : ((n * (m + 1) - 1 + (m - k)).choose (n * (m + 1) - 1) : ℚ) ≤
      2 ^ (n * (m + 1) - 1 + m) := by
    have := Nat.choose_le_two_pow (n * (m + 1) - 1 + (m - k)) (n * (m + 1) - 1)
    have h2 : 2 ^ (n * (m + 1) - 1 + (m - k)) ≤ 2 ^ (n * (m + 1) - 1 + m) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this.trans h2
  have hk1 : (m.factorial : ℚ) / k.factorial ≤ m.factorial := by
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hN : ((n : ℚ) + 1) ^ h ≤ ((n : ℚ) + 1) ^ m :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℚ) ≤ n)]) hh
  rw [pow_mul, pow_mul (2 : ℚ) n (m + 1)]
  gcongr

end BBPPi.MahlerBounds
