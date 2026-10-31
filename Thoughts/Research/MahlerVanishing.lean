import Thoughts.Research.MahlerGeneral

/-
Research file (Thoughts/Research/MahlerVanishing.lean). Imports Thoughts.Research.MahlerGeneral.
Step 1 of the Mahler–Mignotte route: the formal order-of-vanishing identity
  R_h(e^L) = e^{nL} · Σ_N resSum(h+N) L^N / N!
and hence `ord_{L=0} R_h(e^L) = n(m+1) + m - h ≥ n(m+1)`.
-/

set_option backward.isDefEq.respectTransparency false

namespace MahlerVanishing
open MahlerGeneral PowerSeries Finset

/-- the power series `X - λ` (= `(X + C(-λ))`). -/
noncomputable abbrev shiftX (lam : ℕ) : PowerSeries ℚ := X + C (-(lam : ℚ))

lemma coe_taylor_X_pow (lam h : ℕ) :
    Polynomial.coeToPowerSeries.ringHom (Polynomial.taylor (-(lam : ℚ)) (Polynomial.X ^ h)) =
      shiftX lam ^ h := by
  rw [Polynomial.taylor_X_pow, map_pow, map_add, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]

/-- `gSeries` coefficients are power-series coefficients of `Wser · (X-λ)^h`. -/
lemma gSeries_eq_coeff (n m lam h : ℕ) (j : Fin (m + 1)) :
    gSeries n m lam h j = coeff j.1 (Wser n m lam * shiftX lam ^ h) := by
  rw [gSeries_repr n m lam h j, coe_taylor_X_pow]

/-- `resSum` as a sum of power-series coefficients (valid for every `s`). -/
lemma resSum_eq_sum (n m s : ℕ) :
    resSum n m s = ∑ lam ∈ range (n + 1), coeff m (Wser n m lam * shiftX lam ^ s) := by
  rw [resSum, Fin.sum_univ_eq_sum_range (fun l => gSeries n m l s ⟨m, by omega⟩)]
  exact sum_congr rfl fun lam _ => gSeries_eq_coeff n m lam s ⟨m, by omega⟩

/-- binomial/Leibniz expansion of `coeff_m (F · (X + c)^N) / N!`. -/
lemma coeff_mul_X_add_C_pow_div (F : PowerSeries ℚ) (c : ℚ) (m N : ℕ) :
    coeff m (F * (X + C c) ^ N) / (N.factorial : ℚ) =
      ∑ p ∈ antidiagonal N, c ^ p.1 / (p.1.factorial : ℚ) *
        (if p.2 ≤ m then coeff (m - p.2) F / (p.2.factorial : ℚ) else 0) := by
  rw [add_pow, mul_sum, map_sum, sum_div,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun b a => coeff m (F * (X ^ b * C c ^ a * ((N.choose b : ℕ) : PowerSeries ℚ))) /
        (N.factorial : ℚ)),
    ← Finset.Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  simp only [Prod.fst_swap, Prod.snd_swap]
  have e : F * (X ^ p.2 * C c ^ p.1 * ((N.choose p.2 : ℕ) : PowerSeries ℚ)) =
      C (c ^ p.1 * (N.choose p.2 : ℚ)) * (X ^ p.2 * F) := by
    rw [map_mul, map_pow, map_natCast]; ring
  rw [e, coeff_C_mul, coeff_X_pow_mul']
  have hfac : ((N.choose p.2 : ℕ) : ℚ) * (p.2.factorial : ℚ) * (p.1.factorial : ℚ) =
      (N.factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := N) (k := p.2) (by omega)
    rw [show N - p.2 = p.1 by omega] at this
    exact_mod_cast this
  have h1 : (p.1.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (p.2.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (N.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h4 : ((N.choose p.2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  split_ifs
  · rw [← hfac]; field_simp
  · simp

/-- The truncated local factor `Σ_{k ≤ m} g_{m-k} L^k / k!` (as a power series in `L`). -/
noncomputable def locPoly (n m lam h : ℕ) : PowerSeries ℚ :=
  mk fun k => if k ≤ m then coeff (m - k) (Wser n m lam * shiftX lam ^ h) / (k.factorial : ℚ)
    else 0

/-- `e^{-nL} R_h(e^L)` written as a sum over the poles `z = -λ`. -/
noncomputable def RSer (n m h : ℕ) : PowerSeries ℚ :=
  ∑ lam ∈ range (n + 1), rescale (-(lam : ℚ)) (exp ℚ) * locPoly n m lam h

/-- **Order-of-vanishing identity (formal)**: `e^{-nL} R_h(e^L) = Σ_N resSum(h+N) L^N/N!`. -/
theorem RSer_eq (n m h : ℕ) :
    RSer n m h = mk fun N => resSum n m (h + N) / (N.factorial : ℚ) := by
  ext N
  rw [coeff_mk, resSum_eq_sum, sum_div, RSer, map_sum]
  refine sum_congr rfl fun lam _ => ?_
  rw [pow_add, ← mul_assoc, coeff_mul_X_add_C_pow_div, coeff_mul]
  refine sum_congr rfl fun p _ => ?_
  rw [coeff_rescale, coeff_exp, locPoly, coeff_mk]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

lemma resSum_coeff_zero (n m h N : ℕ) (hh : h ≤ m) (hN : N < n * (m + 1)) :
    resSum n m (h + N) = 0 := by
  apply resSum_vanish_general
  have : (n + 1) * (m + 1) = n * (m + 1) + m + 1 := by ring
  omega

/-- `RSer` vanishes to order `≥ n(m+1)` at `L = 0`. -/
theorem RSer_coeff_eq_zero (n m h N : ℕ) (hh : h ≤ m) (hN : N < n * (m + 1)) :
    coeff N (RSer n m h) = 0 := by
  rw [RSer_eq, coeff_mk, resSum_coeff_zero n m h N hh hN, zero_div]

theorem X_pow_dvd_RSer (n m h : ℕ) (hh : h ≤ m) : X ^ (n * (m + 1)) ∣ RSer n m h :=
  (X_pow_dvd_iff).mpr fun N hN => RSer_coeff_eq_zero n m h N hh hN

/-- the first nonzero coefficient: order exactly `n(m+1) + m - h`. -/
theorem RSer_coeff_order (n m h : ℕ) (hh : h ≤ m) :
    coeff (n * (m + 1) + m - h) (RSer n m h) = 1 / ((n * (m + 1) + m - h).factorial : ℚ) := by
  rw [RSer_eq, coeff_mk]
  have : h + (n * (m + 1) + m - h) = (n + 1) * (m + 1) - 1 := by
    have : (n + 1) * (m + 1) = n * (m + 1) + m + 1 := by ring
    omega
  rw [this, resSum_top_general]

/-! ### The `A_hk` form: `R_h(e^L) = Σ_{k,e} A_hk[e] e^{eL} L^k` -/

/-- formal `R_h(e^L)/P = Σ_{k ≤ m} Σ_{e ≤ n} rawACoeff(h,k,e) · e^{eL} · L^k`. -/
noncomputable def RA (n m h : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ range (m + 1), ∑ e ∈ range (n + 1),
    C (rawACoeff n m h k e) * rescale (e : ℚ) (exp ℚ) * X ^ k

lemma locPoly_eq_sum (n m lam h : ℕ) :
    locPoly n m lam h = ∑ k ∈ range (m + 1),
      C (coeff (m - k) (Wser n m lam * shiftX lam ^ h) / (k.factorial : ℚ)) * X ^ k := by
  ext N
  rw [locPoly, coeff_mk, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  by_cases hN : N ≤ m
  · rw [if_pos hN, if_pos (by rw [mem_range]; omega)]
  · rw [if_neg hN, if_neg (by rw [mem_range]; omega)]

/-- **`A_hk` form of the identity**: `R_h(e^L)/P = e^{nL} · Σ_N resSum(h+N) L^N/N!`. -/
theorem RA_eq (n m h : ℕ) (hh : h ≤ m) :
    RA n m h = rescale (n : ℚ) (exp ℚ) * RSer n m h := by
  rw [RSer, mul_sum, ← Finset.sum_range_reflect, RA, sum_comm]
  refine sum_congr rfl fun e he => ?_
  rw [mem_range] at he
  rw [← mul_assoc, exp_mul_exp_eq_exp_add, locPoly_eq_sum, mul_sum]
  have hne : (n : ℚ) + -((n + 1 - 1 - e : ℕ) : ℚ) = (e : ℚ) := by
    rw [show n + 1 - 1 - e = n - e by omega, Nat.cast_sub (by omega)]; ring
  rw [hne]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [rawACoeff, if_pos ⟨hh, by omega, by omega⟩, show n + 1 - 1 - e = n - e by omega]
  simp only
  rw [gSeries_eq_coeff]
  ring

/-- **Order of vanishing**: `R_h(e^L)` has a zero of order `≥ n(m+1)` at `L = 0`
(i.e. `R_h(x)` vanishes to order `≥ n(m+1)` at `x = 1`). -/
theorem RA_coeff_eq_zero (n m h N : ℕ) (hh : h ≤ m) (hN : N < n * (m + 1)) :
    coeff N (RA n m h) = 0 := by
  have hd : X ^ (n * (m + 1)) ∣ RA n m h := by
    rw [RA_eq n m h hh]; exact Dvd.dvd.mul_left (X_pow_dvd_RSer n m h hh) _
  exact (X_pow_dvd_iff.mp hd) N hN

end MahlerVanishing

#print axioms MahlerVanishing.RSer_eq
#print axioms MahlerVanishing.RSer_coeff_order
#print axioms MahlerVanishing.RA_eq
#print axioms MahlerVanishing.RA_coeff_eq_zero
