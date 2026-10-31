import BBPPi.Mahler.Vanishing

/-!
# Hermite–Padé approximants: the determinant and non-vanishing

Step 4 of the Mahler–Mignotte route: the Hermite–Padé determinant
  D(x) = det [A_hk(x)]_{h,k ≤ m} = c₀ · (x - 1)^{n(m+1)},   c₀ = det [A_hk[x^n]] ≠ 0,
hence `D(z) ≠ 0` for every complex `z ≠ 1` (in particular `z = i`), and Mignotte's
non-vanishing: for every `y`, some `U_h(y) = Σ_k A_hk(z) y^k` is nonzero.
-/

set_option backward.isDefEq.respectTransparency false

namespace BBPPi.MahlerDet
open BBPPi.MahlerGeneral BBPPi.MahlerVanishing Polynomial Finset Matrix

/-! ### General lemmas on polynomial matrices -/

lemma natDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X]) (d : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d) : M.det.natDegree ≤ Fintype.card ι * d := by
  rw [det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_mul_le).trans ?_
  rw [show ((Equiv.Perm.sign σ : ℤ) : ℚ[X]) = C ((Equiv.Perm.sign σ : ℤ) : ℚ) by simp,
    natDegree_C, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (M (σ i) i).natDegree ≤ ∑ _i : ι, d := sum_le_sum fun i _ => hM _ _
    _ = Fintype.card ι * d := by simp

lemma coeff_det_top {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X]) (d : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.coeff (Fintype.card ι * d) = (M.map fun p => p.coeff d).det := by
  rw [det_apply', det_apply', finset_sum_coeff]
  refine sum_congr rfl fun σ _ => ?_
  rw [show ((Equiv.Perm.sign σ : ℤ) : ℚ[X]) = C ((Equiv.Perm.sign σ : ℤ) : ℚ) by simp,
    coeff_C_mul, ← card_univ,
    coeff_prod_of_natDegree_le (s := univ) (f := fun i => M (σ i) i) (n := d) (h := fun i _ => hM _ _)]
  simp [Matrix.map_apply]

/-! ### Formal substitution `x = e^L` and vanishing at `x = 1` -/

/-- `p ↦ p(e^L) ∈ ℚ⟦L⟧`. -/
noncomputable def expSubst : ℚ[X] →+* PowerSeries ℚ :=
  eval₂RingHom PowerSeries.C (PowerSeries.exp ℚ)

lemma constantCoeff_exp : PowerSeries.constantCoeff (PowerSeries.exp ℚ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_exp]; simp

lemma constantCoeff_expSubst (p : ℚ[X]) :
    PowerSeries.constantCoeff (expSubst p) = p.eval 1 := by
  rw [expSubst, coe_eval₂RingHom, hom_eval₂, constantCoeff_exp]
  have h1 : (PowerSeries.constantCoeff (R := ℚ)).comp PowerSeries.C = RingHom.id ℚ := by
    ext; simp
  rw [h1]; rfl

/-- `(e^L - 1)/L`. -/
noncomputable def expm1Div : PowerSeries ℚ := PowerSeries.mk fun j => 1 / ((j + 1).factorial : ℚ)

lemma exp_sub_one : PowerSeries.exp ℚ - 1 = PowerSeries.X * expm1Div := by
  ext j
  rcases j with _ | j
  · simp
  · rw [map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_succ_X_mul, expm1Div,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    simp

lemma isUnit_expm1Div : IsUnit expm1Div := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    expm1Div, PowerSeries.coeff_mk]
  simp

/-- If `p(e^L) = O(L^J)` then `(x - 1)^J ∣ p`. -/
theorem X_sub_one_pow_dvd_of_expSubst (J : ℕ) :
    ∀ p : ℚ[X], PowerSeries.X ^ J ∣ expSubst p → (X - C 1) ^ J ∣ p := by
  induction J with
  | zero => intro p _; simp
  | succ J ih =>
    intro p hp
    have hroot : p.IsRoot 1 := by
      have h0 : PowerSeries.constantCoeff (expSubst p) = 0 := by
        obtain ⟨q, hq⟩ := hp
        rw [hq, pow_succ, map_mul, map_mul, PowerSeries.constantCoeff_X]; simp
      rw [constantCoeff_expSubst] at h0
      exact h0
    have hfac := mul_divByMonic_eq_iff_isRoot.mpr hroot
    set q := p /ₘ (X - C 1)
    have hsub : expSubst (X - C 1) = PowerSeries.X * expm1Div := by
      rw [map_sub, ← exp_sub_one]; simp [expSubst]
    rw [← hfac, map_mul, hsub, pow_succ', mul_assoc] at hp
    have hp2 : PowerSeries.X ^ J ∣ expm1Div * expSubst q :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hp
    have hp3 : PowerSeries.X ^ J ∣ expSubst q := (isUnit_expm1Div.dvd_mul_left).mp hp2
    rw [← hfac, pow_succ']
    exact mul_dvd_mul_left _ (ih q hp3)

/-! ### The Hermite–Padé polynomials `A_hk(x)` and their determinant -/

/-- `A_hk(x) = Σ_{e ≤ n} rawACoeff(h,k,e) x^e` (without the integrality factor `P`). -/
noncomputable def Apoly (n m h k : ℕ) : ℚ[X] :=
  ∑ e ∈ range (n + 1), C (rawACoeff n m h k e) * X ^ e

noncomputable def Amat (n m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ[X] :=
  fun h k => Apoly n m h k

lemma natDegree_Apoly (n m h k : ℕ) : (Apoly n m h k).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun e he =>
    (natDegree_C_mul_X_pow_le _ _).trans (by rw [mem_range] at he; omega)

lemma coeff_Apoly (n m h k e : ℕ) (he : e ≤ n) : (Apoly n m h k).coeff e = rawACoeff n m h k e := by
  rw [Apoly, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq, if_pos (by rw [mem_range]; omega)]

lemma expSubst_Apoly (n m h k : ℕ) : expSubst (Apoly n m h k) =
    ∑ e ∈ range (n + 1),
      PowerSeries.C (rawACoeff n m h k e) * PowerSeries.rescale (e : ℚ) (PowerSeries.exp ℚ) := by
  rw [Apoly, map_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [map_mul, map_pow, expSubst, coe_eval₂RingHom, eval₂_C, eval₂_X,
    PowerSeries.exp_pow_eq_rescale_exp]

lemma RA_eq_sum_expSubst (n m h : ℕ) :
    RA n m h = ∑ k : Fin (m + 1), PowerSeries.X ^ (k : ℕ) * expSubst (Apoly n m h k) := by
  rw [RA, Fin.sum_univ_eq_sum_range (fun k => PowerSeries.X ^ k * expSubst (Apoly n m h k))]
  refine sum_congr rfl fun k _ => ?_
  rw [expSubst_Apoly, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  ring

/-- `(x - 1)^{n(m+1)} ∣ det A(x)` (from the order-of-vanishing identity and a column operation). -/
theorem X_sub_one_pow_dvd_det (n m : ℕ) : (X - C 1) ^ (n * (m + 1)) ∣ (Amat n m).det := by
  apply X_sub_one_pow_dvd_of_expSubst
  rw [RingHom.map_det]
  set M := expSubst.mapMatrix (Amat n m)
  have hcol : (M.updateCol 0 fun h => ∑ k, (fun k : Fin (m + 1) => (PowerSeries.X : PowerSeries ℚ) ^ (k : ℕ)) k •
      M h k).det = M.det := by
    rw [det_updateCol_sum]; simp
  have hdiv : ∀ h : Fin (m + 1), PowerSeries.X ^ (n * (m + 1)) ∣
      ∑ k, (fun k : Fin (m + 1) => (PowerSeries.X : PowerSeries ℚ) ^ (k : ℕ)) k • M h k := by
    intro h
    have e : ∑ k, (fun k : Fin (m + 1) => (PowerSeries.X : PowerSeries ℚ) ^ (k : ℕ)) k • M h k = RA n m h := by
      rw [RA_eq_sum_expSubst]; rfl
    rw [e]
    exact PowerSeries.X_pow_dvd_iff.mpr fun N hN => RA_coeff_eq_zero n m h N (by omega) hN
  choose w hw using hdiv
  rw [← hcol]
  have e2 : (fun h => ∑ k, (fun k : Fin (m + 1) => (PowerSeries.X : PowerSeries ℚ) ^ (k : ℕ)) k • M h k) =
      (PowerSeries.X : PowerSeries ℚ) ^ (n * (m + 1)) • w := by
    ext1 h; rw [hw h]; rfl
  rw [e2, det_updateCol_smul]
  exact dvd_mul_right _ _

lemma coeff_zero_Wser_zero_ne (n m : ℕ) : PowerSeries.coeff 0 (Wser n m 0) ≠ 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Wser, map_prod, prod_ne_zero_iff]
  intro μ hμ
  have hμ0 : μ ≠ 0 := Finset.ne_of_mem_erase hμ
  rw [invPow, map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_mk]
  simpa using hμ0

lemma lead_entry (n m : ℕ) (h k : Fin (m + 1)) :
    rawACoeff n m h k n = if (h : ℕ) + k ≤ m then
      PowerSeries.coeff (m - k - h) (Wser n m 0) / ((k : ℕ).factorial : ℚ) else 0 := by
  rw [rawACoeff, if_pos ⟨by omega, by omega, le_rfl⟩]
  simp only [Nat.sub_self]
  rw [gSeries_eq_coeff]
  have : shiftX 0 = PowerSeries.X := by simp [shiftX]
  simp only
  rw [this, PowerSeries.coeff_mul_X_pow']
  split_ifs <;> first | rfl | omega | simp

/-- the leading-coefficient matrix `[A_hk[x^n]]` (anti-triangular). -/
noncomputable def leadMat (n m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  fun h k => rawACoeff n m h k n

theorem det_leadMat_ne_zero (n m : ℕ) : (leadMat n m).det ≠ 0 := by
  have hperm := det_permute' (Fin.revPerm) (leadMat n m)
  have htri : ((leadMat n m).submatrix id Fin.revPerm).BlockTriangular id := by
    intro i j hji
    simp only [submatrix_apply, id, Fin.revPerm_apply, leadMat]
    rw [lead_entry, if_neg]
    rw [Fin.val_rev]
    have : (j : ℕ) < i := hji
    omega
  have hdiag : ∏ i, ((leadMat n m).submatrix id Fin.revPerm) i i ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro i _
    simp only [submatrix_apply, id, Fin.revPerm_apply, leadMat]
    rw [lead_entry, if_pos (by rw [Fin.val_rev]; omega)]
    have e : m - (Fin.rev i : ℕ) - i = 0 := by rw [Fin.val_rev]; omega
    rw [e]
    exact div_ne_zero (coeff_zero_Wser_zero_ne n m) (by exact_mod_cast (Nat.factorial_pos _).ne')
  intro h0
  apply hdiag
  rw [← det_of_upperTriangular htri, hperm, h0, mul_zero]

/-- **Determinant identity**: `det A(x) = c₀ · (x - 1)^{n(m+1)}` with `c₀ = det leadMat ≠ 0`. -/
theorem det_Amat_eq (n m : ℕ) :
    (Amat n m).det = C (leadMat n m).det * (X - C 1) ^ (n * (m + 1)) := by
  set D := (Amat n m).det with hD
  set J := n * (m + 1) with hJ
  have hdeg : D.natDegree ≤ J := by
    have := natDegree_det_le (Amat n m) n (fun h k => natDegree_Apoly n m h k)
    rw [Fintype.card_fin] at this
    rw [hJ, mul_comm]; exact this
  have htop : D.coeff J = (leadMat n m).det := by
    have := coeff_det_top (Amat n m) n (fun h k => natDegree_Apoly n m h k)
    rw [Fintype.card_fin] at this
    rw [hJ, mul_comm, this]
    congr 1
    ext h k
    simp only [Matrix.map_apply, Amat, leadMat]
    exact coeff_Apoly n m h k n le_rfl
  obtain ⟨q, hq⟩ := X_sub_one_pow_dvd_det n m
  rw [← hJ, ← hD] at hq
  have hmon : ((X - C (1 : ℚ)) ^ J).Monic := (monic_X_sub_C 1).pow J
  have hpdeg : ((X - C (1 : ℚ)) ^ J).natDegree = J := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    have := det_leadMat_ne_zero n m
    rw [← htop, hq, coeff_zero] at this
    exact this rfl
  have hqdeg : q.natDegree = 0 := by
    have := hmon.natDegree_mul' hq0
    rw [← hq, hpdeg] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hqdeg] at hq
  have hc : q.coeff 0 = (leadMat n m).det := by
    have hlead : ((X - C (1 : ℚ)) ^ J).coeff J = 1 := by
      have := hmon.coeff_natDegree; rwa [hpdeg] at this
    rw [← htop, hq, coeff_mul_C, hlead, one_mul]
  rw [hq, hc, mul_comm]

theorem det_Amat_ne_zero (n m : ℕ) : (Amat n m).det ≠ 0 := by
  rw [det_Amat_eq]
  exact mul_ne_zero (by simpa using det_leadMat_ne_zero n m)
    (pow_ne_zero _ (X_sub_C_ne_zero 1))

/-- `det A(z) ≠ 0` for every complex `z ≠ 1` (e.g. `z = i`). -/
theorem det_Amat_eval_ne_zero (n m : ℕ) (z : ℂ) (hz : z ≠ 1) :
    ((Amat n m).map (aeval z)).det ≠ 0 := by
  rw [show ((Amat n m).map (aeval z)) = (aeval z).toRingHom.mapMatrix (Amat n m) from rfl,
    ← RingHom.map_det, det_Amat_eq]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, map_sub, aeval_C,
    aeval_X, map_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ (sub_ne_zero.mpr hz))
  simpa using det_leadMat_ne_zero n m

lemma I_ne_one : Complex.I ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem det_Amat_at_I_ne_zero (n m : ℕ) : ((Amat n m).map (aeval Complex.I)).det ≠ 0 :=
  det_Amat_eval_ne_zero n m Complex.I I_ne_one

/-- **Mignotte non-vanishing**: for `z ≠ 1` and any `y`, some
`U_h(y) = Σ_k A_hk(z) y^k` is nonzero. -/
theorem exists_U_ne_zero (n m : ℕ) (z : ℂ) (hz : z ≠ 1) (y : ℂ) :
    ∃ h : Fin (m + 1), ∑ k : Fin (m + 1), aeval z (Apoly n m h k) * y ^ (k : ℕ) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hv : ((Amat n m).map (aeval z)) *ᵥ (fun k : Fin (m + 1) => y ^ (k : ℕ)) = 0 := by
    ext h
    simp only [mulVec, dotProduct, Matrix.map_apply, Amat, Pi.zero_apply]
    exact hcon h
  have h0 := congrFun (eq_zero_of_mulVec_eq_zero (det_Amat_eval_ne_zero n m z hz) hv) 0
  simp at h0

end BBPPi.MahlerDet
