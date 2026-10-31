import BBPPi.Algebra
import BBPPi.Tail

/-!
# The BBP series and its scaled split

Infinite BBP π-series (proved algebraic layer).

Proves the scaled split for the formal series `bbpSeries`; link to `Real.pi` is `BBPPiEqualsSeries`.
-/

namespace BBPPi

open Real Nat Finset

noncomputable def bbpSeries : ℝ := ∑' k : Nat, bbpSummand k

noncomputable def bbpTailSeries (n : Nat) : ℝ := ∑' j : Nat, bbpSummand (n + 1 + j)

/-- Scaled tail `ε` in the BBP split `16^n · π = bbpScaledHead n + ε`, `ε ∈ [0,1)`. -/
noncomputable def bbpScaledTail (n : Nat) : ℝ :=
  ∑' j : Nat, bbpCoeff (n + 1 + j) / ((16 : ℝ) ^ (j + 1))

private lemma tail_reindex (n j : Nat) : bbpSummand (n + 1 + j) = bbpSummand (j + (n + 1)) := by
  ring_nf

private lemma one_div_sixteen_nonneg : 0 ≤ (1 / (16 : ℝ)) := by norm_num

private lemma one_div_sixteen_lt_one : (1 / (16 : ℝ)) < 1 := by norm_num

private lemma summable_geom16 : Summable fun j : ℕ => (1 / (16 : ℝ)) ^ j :=
  summable_geometric_of_lt_one one_div_sixteen_nonneg one_div_sixteen_lt_one

private lemma bbpScaledTail_term_eq (n j : Nat) :
    bbpCoeff (n + 1 + j) / ((16 : ℝ) ^ (j + 1)) =
      (16 : ℝ) ^ n * bbpSummand (n + 1 + j) := by
  unfold bbpSummand
  have hpow : (16 : ℝ) ^ (n + 1 + j) = (16 : ℝ) ^ n * (16 : ℝ) ^ (j + 1) := by ring_nf
  field_simp [hpow]
  ring

theorem summable_bbpSummand : Summable bbpSummand := by
  refine Summable.of_norm_bounded (Summable.mul_left (8 : ℝ) summable_geom16) ?_
  intro k
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using bbpSummand_abs_le k

theorem summable_bbpTailSeries (n : Nat) : Summable (fun j => bbpSummand (n + 1 + j)) := by
  simpa [tail_reindex] using (summable_nat_add_iff (n + 1)).2 summable_bbpSummand

theorem summable_bbpScaledTail (n : Nat) :
    Summable (fun j => bbpCoeff (n + 1 + j) / ((16 : ℝ) ^ (j + 1))) := by
  refine Summable.of_norm_bounded (Summable.mul_left ((8 : ℝ) / 16) summable_geom16) ?_
  intro j
  have hterm := summand_term_bound n j
  have hcast := bbpScaledTail_term_eq n j
  have hnonneg : 0 ≤ bbpSummand (n + 1 + j) := bbpSummand_nonneg (n + 1 + j)
  have hnn : 0 ≤ bbpCoeff (n + 1 + j) / ((16 : ℝ) ^ (j + 1)) := by
    rw [hcast]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n) hnonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, hcast]
  have hstep := mul_le_mul_of_nonneg_left hterm (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n)
  have hmul :
      (16 : ℝ) ^ n * ((8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j) =
        (8 : ℝ) / 16 * (1 / (16 : ℝ)) ^ j := by
    field_simp [pow_add]
    ring
  linarith [hstep, hmul]

theorem bbpSeries_split (n : Nat) :
    bbpSeries = bbpHead n + bbpTailSeries n := by
  unfold bbpSeries bbpHead bbpTailSeries
  have h := summable_bbpSummand.sum_add_tsum_nat_add (n + 1)
  calc
    ∑' k, bbpSummand k =
        (∑ k ∈ range (n + 1), bbpSummand k) + ∑' j, bbpSummand (j + (n + 1)) := h.symm
    _ = bbpHead n + ∑' j, bbpSummand (n + 1 + j) := by
      congr 1
      refine tsum_congr ?_
      intro j
      simpa [tail_reindex] using (tail_reindex n j).symm

theorem bbpSeries_scaled_split (n : Nat) :
    (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + bbpScaledTail n := by
  have hsplit := bbpSeries_split n
  calc
    (16 : ℝ) ^ n * bbpSeries
        = (16 : ℝ) ^ n * (bbpHead n + bbpTailSeries n) := by rw [hsplit]
    _ = bbpScaledHead n + (16 : ℝ) ^ n * bbpTailSeries n := by
      simp [bbpScaledHead, mul_add]
    _ = bbpScaledHead n + bbpScaledTail n := by
      congr 1
      unfold bbpTailSeries bbpScaledTail
      rw [← (summable_bbpTailSeries n).tsum_mul_left ((16 : ℝ) ^ n)]
      refine tsum_congr ?_
      intro j
      exact (bbpScaledTail_term_eq n j).symm

theorem bbpScaledTail_nonneg (n : Nat) : 0 ≤ bbpScaledTail n := by
  unfold bbpScaledTail
  refine tsum_nonneg ?_
  intro j
  have h := bbpSummand_nonneg (n + 1 + j)
  rw [bbpScaledTail_term_eq n j]
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n) h

private lemma geom_tail_sum_lt_one :
    ∑' j : Nat, (8 : ℝ) / 16 * (1 / (16 : ℝ)) ^ j < 1 := by
  have hsum :=
    (Summable.tsum_mul_left ((8 : ℝ) / 16) summable_geom16).symm
  rw [← hsum, tsum_geometric_of_lt_one one_div_sixteen_nonneg one_div_sixteen_lt_one]
  norm_num

theorem bbpTailTrunc_le_tailSeries (n M : Nat) :
    bbpTailTrunc n M ≤ bbpTailSeries n := by
  unfold bbpTailTrunc bbpTailSeries
  exact (summable_bbpTailSeries n).sum_le_tsum (range M) fun j _ =>
    bbpSummand_nonneg (n + 1 + j)

theorem bbpScaledTail_eq_mul_tailSeries (n : Nat) :
    bbpScaledTail n = (16 : ℝ) ^ n * bbpTailSeries n := by
  unfold bbpScaledTail bbpTailSeries
  conv_rhs => rw [← (summable_bbpTailSeries n).tsum_mul_left ((16 : ℝ) ^ n)]
  refine tsum_congr ?_
  intro j
  exact bbpScaledTail_term_eq n j

theorem bbpScaledTailTrunc_le_bbpScaledTail (n M : Nat) :
    bbpScaledTailTrunc n M ≤ bbpScaledTail n := by
  rw [bbpScaledTail_eq_mul_tailSeries n]
  unfold bbpScaledTailTrunc
  exact mul_le_mul_of_nonneg_left (bbpTailTrunc_le_tailSeries n M)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n)

theorem bbpScaledTail_lt_one (n : Nat) : bbpScaledTail n < 1 := by
  unfold bbpScaledTail
  have hterm :
      ∀ j : Nat, bbpCoeff (n + 1 + j) / ((16 : ℝ) ^ (j + 1)) ≤ (8 : ℝ) / 16 * (1 / (16 : ℝ)) ^ j := by
    intro j
    have hterm := summand_term_bound n j
    have hcast := bbpScaledTail_term_eq n j
    rw [hcast]
    have hstep := mul_le_mul_of_nonneg_left hterm (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n)
    have hmul :
        (16 : ℝ) ^ n * ((8 / (16 : ℝ) ^ (n + 1)) * (1 / (16 : ℝ)) ^ j) =
          (8 : ℝ) / 16 * (1 / (16 : ℝ)) ^ j := by
      field_simp [pow_add]
      ring
    rw [← hmul]
    exact hstep
  have hgeom := Summable.mul_left ((8 : ℝ) / 16) summable_geom16
  have hle := (summable_bbpScaledTail n).tsum_le_tsum hterm hgeom
  exact hle.trans_lt geom_tail_sum_lt_one

/-- Formal BBP series equals Mathlib `Real.pi` (single analytic gate). -/
def BBPPiEqualsSeries : Prop := bbpSeries = Real.pi

theorem bbpScaledPiSplit_series (n : Nat) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * bbpSeries = bbpScaledHead n + ε :=
  ⟨bbpScaledTail n, bbpScaledTail_nonneg n, bbpScaledTail_lt_one n, bbpSeries_scaled_split n⟩

theorem bbpScaledPiSplit_of_pi_eq_series (n : Nat) (h : BBPPiEqualsSeries) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ (16 : ℝ) ^ n * Real.pi = bbpScaledHead n + ε := by
  rcases bbpScaledPiSplit_series n with ⟨ε, hε0, hε1, hEq⟩
  refine ⟨ε, hε0, hε1, ?_⟩
  rw [← h, hEq]

end BBPPi
