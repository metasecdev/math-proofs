import Mathlib

/-
Research file (Thoughts/Research/MahlerGeneral.lean). Sorry-free; axioms: propext,
Classical.choice, Quot.sound. Standalone (imports only Mathlib). Proves the general residue
identity, integrality of P*A_hk, the gSeries PowerSeries bridge, and lcmUpto = Finset lcm.
This is a step toward an explicit irrationality measure for pi, NOT the measure itself.
-/

/-!
# Mahler–Mignotte Hermite–Padé — general `(n,m)` algebraic core (LOCAL SCRATCH, Round 3)

**Not imported by `Thoughts.lean`.** (Originally local scratch.)

Sorry-free. Main results (all `n m`, axioms `[propext, Classical.choice, Quot.sound]`):
* `sum_locRes_eq_coeff` — algebraic residue theorem: for distinct nodes `a i` (i ∈ s) and
  `deg f < |s|(m+1)`, `Σ_i Res_{z=a_i} f/∏(z-a_j)^{m+1} = coeff_{|s|(m+1)-1} f`
  (= −Res_∞), proved via Mathlib partial fractions `eq_quo_mul_prod_add_sum_rem_mul_prod`.
* `gSeries_repr` — the prototype's computable truncated `gSeries` equals the `ℚ⟦X⟧` coefficients
  of `(X-λ)^h · ∏_{μ≠λ} (X+(μ-λ))^{-(m+1)}` (general, all indices `≤ m`).
* `resSum_eq_ite`, `resSum_vanish_general`, `resSum_top_general` — general residue identity.
* `lagrange_m0` — `m = 0` closed form `Σ_λ (-λ)^s / ∏_{μ≠λ}(μ-λ) = [s = n]` (`s ≤ n`).
* `lcmUpto_eq_finset_lcm` — `lcmUpto n = (Finset.Icc 1 n).lcm id`.
* `integral_coeffs_general` — L2 integrality `(P · A_hk).den = 1` for all `n, m, h, k, e`.

The definitions `Coeffs, seriesMul, invPowLinSeries, powShiftSeries, gSeries, resSum, lcmUpto,
mahlerP, rawACoeff` are verbatim copies of `MahlerTinyPrototype.lean` (checked by script), so the
statements apply to the prototype's objects.
-/

set_option backward.isDefEq.respectTransparency false

namespace MahlerGeneral
open Polynomial Finset

/-- Local residue functional at the node `a`, with local inverse series `W`:
`coeff_m ( f(X + a) · W )`. For `W = (Q(X+a)/X^{m+1})⁻¹` this is `Res_{z=a} f/Q`. -/
noncomputable def locRes (m : ℕ) (a : ℚ) (W : PowerSeries ℚ) (f : ℚ[X]) : ℚ :=
  PowerSeries.coeff m (Polynomial.coeToPowerSeries.ringHom (taylor a f) * W)

lemma locRes_add (m : ℕ) (a : ℚ) (W : PowerSeries ℚ) (f g : ℚ[X]) :
    locRes m a W (f + g) = locRes m a W f + locRes m a W g := by
  simp only [locRes, map_add (taylor a), map_add Polynomial.coeToPowerSeries.ringHom, add_mul,
    map_add (PowerSeries.coeff m)]

lemma locRes_sum {ι : Type*} (m : ℕ) (a : ℚ) (W : PowerSeries ℚ) (t : Finset ι) (f : ι → ℚ[X]) :
    locRes m a W (∑ i ∈ t, f i) = ∑ i ∈ t, locRes m a W (f i) := by
  simp only [locRes, map_sum (taylor a), map_sum Polynomial.coeToPowerSeries.ringHom,
    Finset.sum_mul, map_sum (PowerSeries.coeff m)]

/-- multiples of `(X - a)^{m+1}` have zero local residue at `a`. -/
lemma locRes_mul_pow_eq_zero (m : ℕ) (a : ℚ) (W : PowerSeries ℚ) (h : ℚ[X]) :
    locRes m a W ((X - C a) ^ (m + 1) * h) = 0 := by
  simp only [locRes, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right,
    map_mul Polynomial.coeToPowerSeries.ringHom, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
  simp

/-- `coeff_m` is invariant under Taylor shift when `natDegree ≤ m`. -/
lemma coeff_taylor_of_natDegree_le (a : ℚ) (p : ℚ[X]) (m : ℕ) (hp : p.natDegree ≤ m) :
    (taylor a p).coeff m = p.coeff m := by
  rcases hp.lt_or_eq with h | h
  · rw [coeff_eq_zero_of_natDegree_lt h, coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_taylor])]
  · subst h
    have := leadingCoeff_taylor (r := a) (f := p)
    rw [leadingCoeff, leadingCoeff, natDegree_taylor] at this
    exact this

/-- **Algebraic residue theorem** (sum of finite residues = − residue at ∞) for
`f / ∏_{i∈s} (X - a_i)^{m+1}` with `deg f < deg Q`. -/
theorem sum_locRes_eq_coeff {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ)
    (ha : Set.InjOn a s) (m : ℕ) (W : ι → PowerSeries ℚ)
    (hW : ∀ i ∈ s, Polynomial.coeToPowerSeries.ringHom
        (∏ j ∈ s.erase i, (X + C (a i - a j)) ^ (m + 1)) * W i = 1)
    (f : ℚ[X]) (hf : f.natDegree < s.card * (m + 1)) :
    ∑ i ∈ s, locRes m (a i) (W i) f = f.coeff (s.card * (m + 1) - 1) := by
  set g : ι → ℚ[X] := fun i => (X - C (a i)) ^ (m + 1) with hg_def
  have hmon : ∀ i ∈ s, (g i).Monic := fun i _ => (monic_X_sub_C _).pow _
  have hcop : Set.Pairwise (s : Set ι) fun i j => IsCoprime (g i) (g j) := by
    intro i hi j hj hij
    exact (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero_of_ne (fun h => hij (ha hi hj h))).isUnit).pow
  obtain ⟨q, r, hr, hfq⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod f hmon hcop
  have hgdeg : ∀ i, (g i).natDegree = m + 1 := fun i => by simp [hg_def]
  have hrdeg : ∀ i ∈ s, (r i).natDegree ≤ m := by
    intro i hi
    have := hr i hi
    rw [degree_eq_natDegree (hmon i hi).ne_zero, hgdeg] at this
    have h2 := natDegree_le_of_degree_le (le_of_lt (lt_of_lt_of_le this (by
      exact_mod_cast le_refl _)))
    by_cases h0 : r i = 0
    · simp [h0]
    · rw [degree_eq_natDegree h0] at this
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hcard : 1 ≤ s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h] at hf; simp at hf
    · exact h
  have herase_mon : ∀ i ∈ s, (∏ k ∈ s.erase i, g k).Monic :=
    fun i _ => monic_prod_of_monic _ _ (fun k hk => hmon k (mem_of_mem_erase hk))
  have herase_deg : ∀ i ∈ s, (∏ k ∈ s.erase i, g k).natDegree = (s.card - 1) * (m + 1) := by
    intro i hi
    rw [natDegree_prod_of_monic _ _ (fun k hk => hmon k (mem_of_mem_erase hk))]
    simp [hgdeg, card_erase_of_mem hi]
  set D := s.card * (m + 1) with hD
  have hDsplit : D - 1 = m + (s.card - 1) * (m + 1) := by
    obtain ⟨c, hc⟩ : ∃ c, s.card = c + 1 := ⟨s.card - 1, by omega⟩
    rw [hD, hc]; simp; ring_nf; omega
  set S := ∑ i ∈ s, r i * ∏ k ∈ s.erase i, g k with hS
  have hSdeg : S.natDegree ≤ D - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    refine (natDegree_mul_le).trans ?_
    rw [herase_deg i hi, hDsplit]
    exact Nat.add_le_add_right (hrdeg i hi) _
  have hQmon : (∏ i ∈ s, g i).Monic := monic_prod_of_monic _ _ hmon
  have hQdeg : (∏ i ∈ s, g i).natDegree = D := by
    rw [natDegree_prod_of_monic _ _ hmon]; simp [hgdeg, hD]
  have hq0 : q = 0 := by
    by_contra hq
    have h1 : (q * ∏ i ∈ s, g i) = f - S := by rw [hfq]; ring
    have h2 : (q * ∏ i ∈ s, g i).natDegree = q.natDegree + D := by
      rw [mul_comm, hQmon.natDegree_mul' hq, hQdeg, add_comm]
    have h3 : (f - S).natDegree ≤ D - 1 :=
      (natDegree_sub_le _ _).trans (max_le (by omega) hSdeg)
    rw [← h1, h2] at h3
    omega
  rw [hq0, zero_mul, zero_add] at hfq
  -- top coefficient side
  have htop : f.coeff (D - 1) = ∑ i ∈ s, (r i).coeff m := by
    rw [hfq, finset_sum_coeff]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hDsplit, coeff_mul_add_eq_of_natDegree_le (hrdeg i hi) (herase_deg i hi).le,
      ← herase_deg i hi, (herase_mon i hi).coeff_natDegree, mul_one]
  rw [htop]
  -- residue side
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hfq, locRes_sum, Finset.sum_eq_single_of_mem i hi]
  · -- diagonal term
    have hprod : taylor (a i) (∏ k ∈ s.erase i, g k) =
        ∏ k ∈ s.erase i, (X + C (a i - a k)) ^ (m + 1) := by
      rw [show taylor (a i) (∏ k ∈ s.erase i, g k) = taylorAlgHom (a i) (∏ k ∈ s.erase i, g k)
        from rfl, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      show taylor (a i) (g k) = _
      simp only [hg_def, taylor_pow, map_sub, taylor_X, taylor_C, map_sub]
      ring
    simp only [locRes]
    rw [taylor_mul, hprod, map_mul Polynomial.coeToPowerSeries.ringHom, mul_assoc, hW i hi, mul_one,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
    exact coeff_taylor_of_natDegree_le _ _ _ (hrdeg i hi)
  · -- off-diagonal terms vanish
    intro j hj hji
    have hi' : i ∈ s.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
    rw [← Finset.mul_prod_erase _ _ hi']
    have : r j * (g i * ∏ k ∈ (s.erase j).erase i, g k) =
        (X - C (a i)) ^ (m + 1) * (r j * ∏ k ∈ (s.erase j).erase i, g k) := by
      simp only [hg_def]; ring
    rw [this]
    exact locRes_mul_pow_eq_zero _ _ _ _

/-! ## Part B: prototype definitions (verbatim copies) and the PowerSeries bridge -/

abbrev Coeffs (m : ℕ) := Fin (m + 1) → ℚ

def seriesMul {m : ℕ} (a b : Coeffs m) : Coeffs m := fun k =>
  ∑ i : Fin (m + 1), if i.1 ≤ k.1 then a i * b ⟨k.1 - i.1, by omega⟩ else 0

def invPowLinSeries (m : ℕ) (c : ℤ) : Coeffs m := fun j =>
  ((-1 : ℚ) ^ (j.1 : ℕ) * Nat.choose (m + j.1) j.1) / (c : ℚ) ^ (m + 1 + j.1)

def powShiftSeries (m lam h : ℕ) : Coeffs m := fun i =>
  if i.1 ≤ h then
    (Nat.choose h i.1 : ℚ) * ((- (lam : ℤ) : ℚ) ^ (h - i.1))
  else
    0

def gSeries (n m lam h : ℕ) : Coeffs m :=
  Id.run do
    let mut base : Coeffs m := fun i => if i.1 = 0 then 1 else 0
    for μ in List.range (n + 1) do
      if μ ≠ lam then
        base := seriesMul base (invPowLinSeries m ((μ : ℤ) - (lam : ℤ)))
    pure (seriesMul base (powShiftSeries m lam h))

def resSum (n m s : ℕ) : ℚ :=
  ∑ lam : Fin (n + 1), gSeries n m lam.1 s ⟨m, by omega⟩

/-- `a` lists the first `m+1` coefficients of the power series `A`. -/
def Repr {m : ℕ} (a : Coeffs m) (A : PowerSeries ℚ) : Prop :=
  ∀ i : Fin (m + 1), a i = PowerSeries.coeff i.1 A

lemma seriesMul_repr {m : ℕ} {a b : Coeffs m} {A B : PowerSeries ℚ}
    (ha : Repr a A) (hb : Repr b B) : Repr (seriesMul a b) (A * B) := by
  intro k
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [seriesMul, show ∀ i, a i = PowerSeries.coeff i.1 A from ha,
    show ∀ i, b i = PowerSeries.coeff i.1 B from hb]
  rw [Fin.sum_univ_eq_sum_range
    (fun x => if x ≤ k.1 then PowerSeries.coeff x A * PowerSeries.coeff (k.1 - x) B else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext x; simp only [mem_filter, mem_range]; omega
  · intros; rfl

/-- explicit inverse of `(X + c)^(m+1)` in `ℚ⟦X⟧`. -/
noncomputable def invPow (m : ℕ) (c : ℚ) : PowerSeries ℚ :=
  PowerSeries.C (c ^ (m + 1))⁻¹ * PowerSeries.mk fun j => (-c⁻¹) ^ j * (Nat.choose (m + j) m : ℚ)

lemma invPow_spec (m : ℕ) (c : ℚ) (hc : c ≠ 0) :
    (PowerSeries.X + PowerSeries.C c) ^ (m + 1) * invPow m c = 1 := by
  have h1 := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := m)
  have h2 := congrArg (PowerSeries.rescale (-c⁻¹)) h1
  rw [map_mul, PowerSeries.rescale_mk, map_pow, map_sub, map_one, PowerSeries.rescale_X] at h2
  have hX : PowerSeries.X + PowerSeries.C c =
      PowerSeries.C c * (1 - PowerSeries.C (-c⁻¹) * (PowerSeries.X : PowerSeries ℚ)) := by
    have : PowerSeries.C c * PowerSeries.C c⁻¹ = (1 : PowerSeries ℚ) := by
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    rw [map_neg]; linear_combination (-PowerSeries.X) * this
  rw [hX, mul_pow, invPow, ← map_pow]
  have h3 : PowerSeries.C (c ^ (m + 1)) * PowerSeries.C (c ^ (m + 1))⁻¹ = (1 : PowerSeries ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hc), map_one]
  linear_combination (PowerSeries.mk fun j => (-c⁻¹) ^ j * (Nat.choose (m + j) m : ℚ)) *
      (1 - PowerSeries.C (-c⁻¹) * PowerSeries.X) ^ (m + 1) * h3 + h2

lemma invPowLinSeries_repr (m : ℕ) (c : ℤ) : Repr (invPowLinSeries m c) (invPow m (c : ℚ)) := by
  intro j
  rw [invPow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, invPowLinSeries,
    Nat.choose_symm_add]
  ring

lemma powShiftSeries_repr (m lam h : ℕ) :
    Repr (powShiftSeries m lam h)
      (Polynomial.coeToPowerSeries.ringHom (taylor (-(lam : ℚ)) (X ^ h))) := by
  intro i
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, taylor_X_pow,
    coeff_X_add_C_pow, powShiftSeries]
  split_ifs with hi
  · push_cast; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma one_repr (m : ℕ) : Repr (fun i : Fin (m + 1) => if i.1 = 0 then (1 : ℚ) else 0) 1 := by
  intro i
  rw [PowerSeries.coeff_one]

lemma forIn_ite_eq_foldl {β : Type} (L : List ℕ) (init : β) (lam : ℕ) (F : β → ℕ → β) :
    (forIn (m := Id) L init fun μ r =>
        if μ = lam then pure (ForInStep.yield r) else pure (ForInStep.yield (F r μ))).run =
      L.foldl (fun b μ => if μ = lam then b else F b μ) init := by
  induction L generalizing init with
  | nil => rfl
  | cons μ L ih => by_cases hμ : μ = lam <;> simp [hμ, ih]

lemma gSeries_eq_foldl (n m lam h : ℕ) :
    gSeries n m lam h = seriesMul ((List.range (n + 1)).foldl
      (fun base μ => if μ = lam then base
        else seriesMul base (invPowLinSeries m ((μ : ℤ) - (lam : ℤ))))
      (fun i => if i.1 = 0 then 1 else 0)) (powShiftSeries m lam h) := by
  unfold gSeries
  simp
  exact congrArg (fun b => seriesMul b (powShiftSeries m lam h)) (forIn_ite_eq_foldl _ _ lam _)

lemma foldl_repr (m lam : ℕ) (L : List ℕ) (base : Coeffs m) (B : PowerSeries ℚ)
    (hB : Repr base B) :
    Repr (L.foldl (fun base μ => if μ = lam then base
        else seriesMul base (invPowLinSeries m ((μ : ℤ) - (lam : ℤ)))) base)
      (B * (L.map fun μ => if μ = lam then 1 else invPow m ((μ : ℚ) - lam)).prod) := by
  induction L generalizing base B with
  | nil => simpa using hB
  | cons μ L ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [← mul_assoc]
    apply ih
    split_ifs with hμ
    · simpa using hB
    · have := invPowLinSeries_repr m ((μ : ℤ) - (lam : ℤ))
      push_cast at this
      exact seriesMul_repr hB this

/-- local inverse series at the pole `-λ`. -/
noncomputable def Wser (n m lam : ℕ) : PowerSeries ℚ :=
  ∏ μ ∈ (range (n + 1)).erase lam, invPow m ((μ : ℚ) - lam)

lemma list_prod_range_eq {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.prod_coe]

lemma gSeries_repr (n m lam h : ℕ) :
    Repr (gSeries n m lam h)
      (Wser n m lam * Polynomial.coeToPowerSeries.ringHom (taylor (-(lam : ℚ)) (X ^ h))) := by
  rw [gSeries_eq_foldl]
  refine seriesMul_repr ?_ (powShiftSeries_repr m lam h)
  have := foldl_repr m lam (List.range (n + 1)) _ 1 (one_repr m)
  rw [one_mul, list_prod_range_eq] at this
  convert this using 1
  rw [Wser, ← Finset.filter_ne', Finset.prod_filter]
  refine Finset.prod_congr rfl fun μ _ => ?_
  by_cases hμ : μ = lam <;> simp [hμ]

lemma gSeries_top_eq_locRes (n m lam h : ℕ) :
    gSeries n m lam h ⟨m, by omega⟩ = locRes m (-(lam : ℚ)) (Wser n m lam) (X ^ h) := by
  rw [gSeries_repr n m lam h ⟨m, by omega⟩, locRes, mul_comm]

lemma Wser_spec (n m lam : ℕ) :
    Polynomial.coeToPowerSeries.ringHom
        (∏ j ∈ (range (n + 1)).erase lam, (X + C (-(lam : ℚ) - -(j : ℚ))) ^ (m + 1)) *
      Wser n m lam = 1 := by
  rw [map_prod, Wser, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j hj => ?_
  have hne : (j : ℚ) - lam ≠ 0 := by
    have := Finset.ne_of_mem_erase hj
    intro h; apply this; exact_mod_cast (sub_eq_zero.mp h)
  rw [map_pow, map_add, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C,
    show -(lam : ℚ) - -(j : ℚ) = (j : ℚ) - lam by ring]
  exact invPow_spec m _ hne

/-- **General residue identity** for the prototype's `resSum`. -/
theorem resSum_eq_ite (n m s : ℕ) (hs : s < (n + 1) * (m + 1)) :
    resSum n m s = if s = (n + 1) * (m + 1) - 1 then 1 else 0 := by
  rw [resSum, Fin.sum_univ_eq_sum_range (fun l => gSeries n m l s ⟨m, by omega⟩)]
  simp_rw [gSeries_top_eq_locRes]
  have hinj : Set.InjOn (fun l : ℕ => -(l : ℚ)) (range (n + 1) : Set ℕ) := by
    intro x _ y _ hxy; simpa using hxy
  have := sum_locRes_eq_coeff (range (n + 1)) (fun l : ℕ => -(l : ℚ)) hinj m (Wser n m)
    (fun i _ => Wser_spec n m i) (X ^ s) (by rw [natDegree_X_pow, card_range]; exact hs)
  rw [card_range] at this
  rw [this, coeff_X_pow]
  by_cases h : s = (n + 1) * (m + 1) - 1
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem resSum_vanish_general (n m s : ℕ) (hs : s + 2 ≤ (n + 1) * (m + 1)) :
    resSum n m s = 0 := by
  rw [resSum_eq_ite n m s (by omega), if_neg (by omega)]

theorem resSum_top_general (n m : ℕ) :
    resSum n m ((n + 1) * (m + 1) - 1) = 1 := by
  have : 0 < (n + 1) * (m + 1) := Nat.mul_pos (by omega) (by omega)
  rw [resSum_eq_ite n m _ (by omega), if_pos rfl]


/-! ## Part C: `lcmUpto` (verbatim copy) ↔ `Finset.lcm` bridge -/

def lcmUpto : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUpto n) (n + 1)

theorem lcmUpto_eq_finset_lcm (n : ℕ) : lcmUpto n = (Finset.Icc 1 n).lcm id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lcmUpto, ih, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert,
      id, lcm_eq_nat_lcm, Nat.lcm_comm]

theorem dvd_lcmUpto {n c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ n) : c ∣ lcmUpto n := by
  rw [lcmUpto_eq_finset_lcm]
  exact Finset.dvd_lcm (by simp; omega)

/-! ## Part D: general L2 integrality of `P · A_hk` -/

def mahlerP (n m : ℕ) : ℕ :=
  Nat.factorial m * (lcmUpto n) ^ m * (Nat.factorial n) ^ (m + 1)

def rawACoeff (n m h k e : ℕ) : ℚ :=
  if h ≤ m ∧ k ≤ m ∧ e ≤ n then
    let lam := n - e
    (gSeries n m lam h ⟨m - k, by omega⟩) / (Nat.factorial k : ℚ)
  else
    0

/-- the subring `ℤ ⊆ ℚ`. -/
def ZZ : Subring ℚ := (Int.castRingHom ℚ).range

lemma intCast_mem_ZZ (z : ℤ) : (z : ℚ) ∈ ZZ := ⟨z, rfl⟩

/-- `F` has coefficients with denominators dividing `D · N^j` at degree `j`. -/
def IntScaled (N : ℕ) (D : ℚ) (F : PowerSeries ℚ) : Prop :=
  ∀ j, D * (N : ℚ) ^ j * PowerSeries.coeff j F ∈ ZZ

lemma IntScaled.mul {N : ℕ} {D1 D2 : ℚ} {F G : PowerSeries ℚ}
    (hF : IntScaled N D1 F) (hG : IntScaled N D2 G) : IntScaled N (D1 * D2) (F * G) := by
  intro j
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine Subring.sum_mem _ fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have := Subring.mul_mem _ (hF p.1) (hG p.2)
  convert this using 1
  rw [← hp, pow_add]; ring

lemma IntScaled.prod {N : ℕ} {ι : Type*} (s : Finset ι) (D : ι → ℚ) (F : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, IntScaled N (D i) (F i)) :
    IntScaled N (∏ i ∈ s, D i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j
    rw [prod_empty, prod_empty, one_mul, PowerSeries.coeff_one]
    split_ifs
    · convert intCast_mem_ZZ ((N : ℤ) ^ j) using 1; push_cast; ring
    · rw [mul_zero]; exact Subring.zero_mem _
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

lemma invPow_intScaled (N m : ℕ) (d : ℤ) (hd : d ≠ 0) (hdN : d ∣ (N : ℤ)) :
    IntScaled N ((d : ℚ) ^ (m + 1)) (invPow m d) := by
  intro j
  obtain ⟨t, ht⟩ := hdN
  rw [invPow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hN : (N : ℚ) = d * t := by exact_mod_cast ht
  rw [hN]
  convert intCast_mem_ZZ ((-1) ^ j * t ^ j * (Nat.choose (m + j) m : ℤ)) using 1
  push_cast
  have e1 : (d : ℚ) ^ (m + 1) * ((d : ℚ) ^ (m + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hdq)
  have e2 : (d : ℚ) ^ j * ((d : ℚ)⁻¹) ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hdq, one_pow]
  linear_combination
    ((-1) ^ j * (t : ℚ) ^ j * (Nat.choose (m + j) m : ℚ) * ((d : ℚ) ^ j * ((d : ℚ)⁻¹) ^ j)) * e1 +
    ((-1) ^ j * (t : ℚ) ^ j * (Nat.choose (m + j) m : ℚ)) * e2

lemma taylorXpow_intScaled (N lam h : ℕ) :
    IntScaled N 1 (Polynomial.coeToPowerSeries.ringHom (taylor (-(lam : ℚ)) (X ^ h))) := by
  intro j
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, taylor_X_pow,
    coeff_X_add_C_pow]
  convert intCast_mem_ZZ ((N : ℤ) ^ j * (-(lam : ℤ)) ^ (h - j) * (h.choose j : ℤ)) using 1
  push_cast; ring

/-- `D_λ := ∏_{μ≠λ} (μ-λ)^{m+1}` (as an integer). -/
def distProd (n m lam : ℕ) : ℤ := ∏ μ ∈ (range (n + 1)).erase lam, ((μ : ℤ) - lam) ^ (m + 1)

lemma gSeries_intScaled (n m lam h : ℕ) (hlam : lam ≤ n) (j : Fin (m + 1)) :
    (distProd n m lam : ℚ) * (lcmUpto n : ℚ) ^ j.1 * gSeries n m lam h j ∈ ZZ := by
  rw [gSeries_repr n m lam h j]
  have hW : IntScaled (lcmUpto n)
      (∏ μ ∈ (range (n + 1)).erase lam, (((μ : ℤ) - lam : ℤ) : ℚ) ^ (m + 1)) (Wser n m lam) := by
    unfold Wser
    apply IntScaled.prod
    intro μ hμ
    have hne : μ ≠ lam := Finset.ne_of_mem_erase hμ
    have hμn : μ ≤ n := by have := Finset.mem_of_mem_erase hμ; simp at this; omega
    have hd : ((μ : ℤ) - lam) ≠ 0 := by omega
    have hdvd : ((μ : ℤ) - lam) ∣ (lcmUpto n : ℤ) := by
      rw [← Int.natAbs_dvd]
      exact_mod_cast dvd_lcmUpto (c := ((μ : ℤ) - lam).natAbs) (by omega) (by omega)
    have := invPow_intScaled (lcmUpto n) m _ hd hdvd
    push_cast at this ⊢
    exact this
  have := hW.mul (taylorXpow_intScaled (lcmUpto n) lam h) j.1
  convert this using 2
  simp [distProd]

lemma prod_left (lam : ℕ) : ∏ μ ∈ range lam, (lam - μ) = lam.factorial := by
  rw [← Finset.prod_range_reflect]
  have : ∀ j ∈ range lam, lam - (lam - 1 - j) = j + 1 := by
    intro j hj; simp at hj; omega
  rw [Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]

lemma natAbs_prod_dist (n lam : ℕ) (hlam : lam ≤ n) :
    (∏ μ ∈ (range (n + 1)).erase lam, ((μ : ℤ) - lam)).natAbs =
      lam.factorial * (n - lam).factorial := by
  rw [show (∏ μ ∈ (range (n + 1)).erase lam, ((μ : ℤ) - lam)).natAbs =
      Int.natAbsHom (∏ μ ∈ (range (n + 1)).erase lam, ((μ : ℤ) - lam)) from rfl, map_prod,
    ← Finset.prod_filter_mul_prod_filter_not _ (· < lam)]
  have h1 : ((range (n + 1)).erase lam).filter (· < lam) = range lam := by
    ext x; simp only [mem_filter, mem_erase, mem_range]; omega
  have h2 : ((range (n + 1)).erase lam).filter (fun x => ¬ x < lam) = Ico (lam + 1) (n + 1) := by
    ext x; simp only [mem_filter, mem_erase, mem_range, mem_Ico]; omega
  rw [h1, h2, ← prod_left lam, Finset.prod_Ico_eq_prod_range,
    show n + 1 - (lam + 1) = n - lam by omega, ← Finset.prod_range_add_one_eq_factorial]
  congr 1
  · refine Finset.prod_congr rfl fun μ hμ => ?_
    simp only [mem_range] at hμ
    show ((μ : ℤ) - lam).natAbs = lam - μ
    omega
  · refine Finset.prod_congr rfl fun k _ => ?_
    show (((lam + 1 + k : ℕ) : ℤ) - lam).natAbs = k + 1
    omega

lemma distProd_dvd (n m lam : ℕ) (hlam : lam ≤ n) :
    distProd n m lam ∣ ((n.factorial : ℕ) : ℤ) ^ (m + 1) := by
  rw [distProd, Finset.prod_pow]
  refine pow_dvd_pow_of_dvd ?_ _
  rw [← Int.natAbs_dvd_natAbs, natAbs_prod_dist n lam hlam, Int.natAbs_natCast]
  simpa using Nat.factorial_mul_factorial_dvd_factorial hlam

/-- **General L2 integrality**: `P · A_hk ∈ ℤ` coefficientwise, all `n, m`. -/
theorem integral_coeffs_general (n m : ℕ) :
    ∀ h k e : ℕ, h ≤ m → k ≤ m → e ≤ n →
      ((mahlerP n m : ℚ) * rawACoeff n m h k e).den = 1 := by
  intro h k e hh hk he
  set lam := n - e with hlam_def
  have hlam : lam ≤ n := by omega
  have hg := gSeries_intScaled n m lam h hlam ⟨m - k, by omega⟩
  obtain ⟨u, hu⟩ := Nat.factorial_dvd_factorial hk
  obtain ⟨v, hv⟩ := distProd_dvd n m lam hlam
  obtain ⟨z, hz⟩ := hg
  have hk0 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have key : (mahlerP n m : ℚ) * rawACoeff n m h k e =
      ((u * lcmUpto n ^ k * v * z : ℤ) : ℚ) := by
    have hz' : (z : ℚ) = (distProd n m lam : ℚ) * (lcmUpto n : ℚ) ^ (m - k) *
        gSeries n m lam h ⟨m - k, by omega⟩ := hz
    have hv' : ((n.factorial : ℚ)) ^ (m + 1) = (distProd n m lam : ℚ) * v := by
      exact_mod_cast hv
    have hu' : (m.factorial : ℚ) = k.factorial * u := by exact_mod_cast hu
    have hpow : (lcmUpto n : ℚ) ^ m = (lcmUpto n : ℚ) ^ k * (lcmUpto n : ℚ) ^ (m - k) := by
      rw [← pow_add]; congr 1; omega
    rw [rawACoeff, if_pos ⟨hh, hk, he⟩, mahlerP]
    push_cast
    rw [hz', hu', hpow, hv']
    field_simp
    ring
  rw [key, Rat.den_intCast]


/-- `m = 0` closed form (Lagrange / divided-difference identity), as a corollary. -/
theorem lagrange_m0 (n s : ℕ) (hs : s ≤ n) :
    ∑ lam ∈ range (n + 1), (-(lam : ℚ)) ^ s * ∏ μ ∈ (range (n + 1)).erase lam, ((μ : ℚ) - lam)⁻¹ =
      if s = n then 1 else 0 := by
  have := resSum_eq_ite n 0 s (by omega)
  rw [show (n + 1) * (0 + 1) - 1 = n by omega] at this
  rw [← this, resSum, Fin.sum_univ_eq_sum_range (fun l => gSeries n 0 l s ⟨0, by omega⟩)]
  refine sum_congr rfl fun lam _ => ?_
  rw [gSeries_repr n 0 lam s ⟨0, by omega⟩]
  simp [PowerSeries.coeff_zero_eq_constantCoeff, Wser, invPow, map_prod, mul_comm]

#print axioms sum_locRes_eq_coeff
#print axioms gSeries_repr
#print axioms resSum_vanish_general
#print axioms resSum_top_general
#print axioms lagrange_m0
#print axioms lcmUpto_eq_finset_lcm
#print axioms integral_coeffs_general
end MahlerGeneral
