/-
  Integer BBP spigot sums vs the proved real series (P-BBP-01 support layer).

  **2026-09 correctness audit.** `bbp_term` now carries the `1/16^k` weight (it is
  definitionally `bbpSpigotTerm`), so `bbpIntFullSum = bbpSpigotIntFullSum` and the old
  "legacy track" is gone. Removed from this file (they were artifacts of the mis-scaled
  term or of an off-by-one digit criterion):
  * the 51 `bbpIntSeriesBracket_upper_holds_*`, 18 `bbpIntFullSum_*` numerals and 33
    `bbpSpigotIntFullSum_le_bbpIntFullSum_*` (true only because the legacy sum was ≈3.38×
    too large, or now redundant);
  * the "cert-gap" layer (`BBPSpigotDigitCertGapCorrect*`, `BBPSpigotDigitExtract`,
    `bbpHexDigitIntGapCert`, `bbpHexDigitSpigotCert`, …): it compared the certificate's low
    digit with `⌊16·gap⌋ mod 16`, which is digit `n+1`, so it only recorded chance matches;
  * the 8 Tier-1 `BBPSpigotDigitCorrect_*` / `*_of_hz` theorems (4 of the `hz` numerals
    were false: n = 5, 18, 24, 42).
  The correct certificate, its two-sided bracket and the Tier-1 digits are in
  `BBPGuarded.lean` / `BBPGuardedCerts.lean`.

  What remains here is true but one-sided: the *unguarded* sums overshoot
  `16^n·bbpSeries` (head overshoot, `bbpSpigotIntSeriesBracket_upper_holds_*`); the lower
  bracket for the unguarded sum is generally false. No `sorry`, no axioms, and (after the
  audit) no `native_decide`: the remaining numeric families are `norm_num` proofs.
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Cast.Order.Field
import Thoughts.Proved.BBPAlgebra
import Thoughts.Proved.BBPTail
import Thoughts.Proved.BBPSeries
import Thoughts.Proved.BBPDigitDefs

namespace FinitistProved

open Real Nat Finset

/-! ### Integer sums -/

/-- Full certificate sum through index `n + 50`. -/
def bbpIntFullSum (n : Nat) : Nat :=
  ∑ k ∈ range (n + 51), bbp_term k n

/-- Tail certificate sum `k ∈ {n+1,…,n+50}`. -/
def bbpIntTailSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.Icc (n + 1) (n + 50), bbp_term k n

theorem bbpIntFullSum_eq_head_add_tail (n : Nat) :
    bbpIntFullSum n = bbpIntHeadSum n + bbpIntTailSum n := by
  unfold bbpIntFullSum bbpIntHeadSum bbpIntTailSum
  have hsplit :
      range (n + 51) = range (n + 1) ∪ Icc (n + 1) (n + 50) := by
    ext k
    simp only [mem_range, mem_union, mem_Icc]
    constructor
    · intro hk
      rcases lt_or_ge k (n + 1) with hk1 | hk1
      · left; exact hk1
      · right; constructor <;> omega
    · intro hk
      rcases hk with hk | ⟨hk1, hk2⟩
      · omega
      · omega
  have hdisj : Disjoint (range (n + 1)) (Icc (n + 1) (n + 50)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp [mem_range, mem_Icc] at ha hb
    omega
  rw [hsplit, sum_union hdisj]

/-! ### Provable per-term head bound -/

/-- Low hex digit of the unguarded sum is `bbpIntFullSum n % 16` (comparison only). -/
theorem bbpHexDigitUnguarded_eq_intFullSum_mod (n : Nat) :
    bbpHexDigitUnguarded n = bbpIntFullSum n % 16 := rfl

/-- The legacy (mis-scaled) term never exceeds its leading integer division branch. -/
theorem bbp_term_legacy_le_first_branch (k n : Nat) :
    bbp_term_legacy k n ≤ (4 * 16 ^ n) / (8 * k + 1) := by
  dsimp [bbp_term_legacy]
  apply le_trans (Nat.sub_le _ _)
  apply le_trans (Nat.sub_le _ _)
  exact Nat.sub_le _ _

/-! ### Analytically weighted spigot sums (`16^{n-k}` scaling) -/

/-- Full weighted sum through index `n + 50`. -/
def bbpSpigotIntFullSum (n : Nat) : Nat :=
  ∑ k ∈ range (n + 51), bbpSpigotTerm k n

/-- Weighted head sum `∑_{k≤n} bbpSpigotTerm k n`. -/
def bbpSpigotIntHeadSum (n : Nat) : Nat :=
  ∑ k ∈ range (n + 1), bbpSpigotTerm k n

/-- Weighted tail sum `k ∈ {n+1,…,n+50}`. -/
def bbpSpigotIntTailSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.Icc (n + 1) (n + 50), bbpSpigotTerm k n

theorem bbpSpigotIntFullSum_eq_head_add_tail (n : Nat) :
    bbpSpigotIntFullSum n = bbpSpigotIntHeadSum n + bbpSpigotIntTailSum n := by
  unfold bbpSpigotIntFullSum bbpSpigotIntHeadSum bbpSpigotIntTailSum
  have hsplit :
      range (n + 51) = range (n + 1) ∪ Icc (n + 1) (n + 50) := by
    ext k
    simp only [mem_range, mem_union, mem_Icc]
    constructor
    · intro hk
      rcases lt_or_ge k (n + 1) with hk1 | hk1
      · left; exact hk1
      · right; constructor <;> omega
    · intro hk
      rcases hk with hk | ⟨hk1, hk2⟩
      · omega
      · omega
  have hdisj : Disjoint (range (n + 1)) (Icc (n + 1) (n + 50)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp [mem_range, mem_Icc] at ha hb
    omega
  rw [hsplit, sum_union hdisj]

theorem bbpSpigotTerm_le_first_branch (k n : Nat) :
    bbpSpigotTerm k n ≤ (4 * 16 ^ n) / (16 ^ k * (8 * k + 1)) := by
  dsimp [bbpSpigotTerm]
  apply le_trans (Nat.sub_le _ _)
  apply le_trans (Nat.sub_le _ _)
  exact Nat.sub_le _ _

private lemma bbpSpigotIntTailSum_eq_sum_range (n : Nat) :
    bbpSpigotIntTailSum n = ∑ j ∈ range 50, bbpSpigotTerm (n + 1 + j) n := by
  unfold bbpSpigotIntTailSum
  have hmap :
      Finset.Icc (n + 1) (n + 50) =
        (Finset.range 50).map ⟨fun j => n + 1 + j, fun j₁ j₂ h => by simp at h; omega⟩ := by
    ext k
    simp [Finset.mem_map, mem_Icc, mem_range]
    constructor
    · intro ⟨hk1, hk2⟩
      refine ⟨k - (n + 1), ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
  rw [hmap, Finset.sum_map]
  rfl

/--
  **Proved tail cert input:** weighted tail terms vanish for `k > n`, so the
  `50`-term certificate tail sum is exactly zero.
-/
theorem bbpSpigotTerm_tail_eq_zero (n j : Nat) (hj : j ∈ range 50) :
    bbpSpigotTerm (n + 1 + j) n = 0 :=
  bbpSpigotTerm_eq_zero_of_gt (n + 1 + j) n (by omega)

theorem bbpSpigotIntTailSum_eq_zero (n : Nat) : bbpSpigotIntTailSum n = 0 := by
  rw [bbpSpigotIntTailSum_eq_sum_range]
  exact Finset.sum_eq_zero fun j hj => bbpSpigotTerm_tail_eq_zero n j hj

private lemma Finset.sum_range_succ_shift {α : Type*} [AddCommMonoid α] (n : Nat) (f : Nat → α) :
    ∑ k ∈ range (n + 1), f k =
      f 0 + ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Finset.sum_range_succ, ih, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm]

private lemma bbpHead_eq_summand_zero_add_shift (n : Nat) :
    bbpHead n = bbpSummand 0 + ∑ k ∈ range n, bbpSummand (k + 1) := by
  simpa [bbpHead] using Finset.sum_range_succ_shift n bbpSummand

private lemma bbpSpigotIntHeadSum_eq_term_zero_add_shift (n : Nat) :
    bbpSpigotIntHeadSum n =
      bbpSpigotTerm 0 n + ∑ k ∈ range n, bbpSpigotTerm (k + 1) n := by
  simpa [bbpSpigotIntHeadSum] using Finset.sum_range_succ_shift n (fun k => bbpSpigotTerm k n)

theorem bbpSpigotIntHeadSum_ge_term_zero (n : Nat) :
    (bbpSpigotTerm 0 n : ℝ) ≤ (bbpSpigotIntHeadSum n : ℝ) := by
  have hmem : 0 ∈ range (n + 1) := by simp [mem_range]
  simpa [bbpSpigotIntHeadSum] using
    Finset.single_le_sum (f := fun k => (bbpSpigotTerm k n : ℝ))
      (fun k _ => Nat.cast_nonneg _) hmem

/-- Integer strictly above `⌊bbpScaledHead n⌋` forces strict overshoot of the real head. -/
theorem bbpSpigotIntHeadSum_gt_scaledHead_of_gt_floor (n : Nat)
    (h : (bbpSpigotIntHeadSum n : ℝ) > ⌊bbpScaledHead n⌋) :
    bbpScaledHead n < (bbpSpigotIntHeadSum n : ℝ) := by
  have hm : (⌊bbpScaledHead n⌋ + 1 : ℝ) ≤ (bbpSpigotIntHeadSum n : ℝ) := by
    have h' : (⌊bbpScaledHead n⌋ : ℤ) < (bbpSpigotIntHeadSum n : ℤ) := Int.cast_lt.mp h
    exact_mod_cast Int.add_one_le_of_lt h'
  linarith [Int.floor_le (bbpScaledHead n), Int.lt_floor_add_one (bbpScaledHead n), hm]

/--
  **P-BBP-01 head overshoot:** integer weighted head exceeds analytic `bbpScaledHead`.
  Proved at `n ≤ 13`; general `n` reduces to `k = 0` excess plus sum-level rest control.
-/
def BBPSpigotIntHeadOvershoot (n : Nat) : Prop :=
  bbpScaledHead n < (bbpSpigotIntHeadSum n : ℝ)

/-- **Proved k = 0 input:** weighted head dominates the `k = 0` analytic summand. -/
theorem bbpSpigotIntHeadSum_gt_scaledSummand_zero (n : Nat) :
    (16 : ℝ) ^ n * bbpSummand 0 < (bbpSpigotIntHeadSum n : ℝ) :=
  lt_of_lt_of_le (bbpSpigotTerm_zero_gt_scaledSummand n) (bbpSpigotIntHeadSum_ge_term_zero n)

/--
  **General head overshoot reduction:** `k = 0` excess strictly dominates the
  net `k ≥ 1` gap `16^n · ∑_{k≥1} bbpSummand k - ∑_{k≥1} bbpSpigotTerm k n`.
  (Individual `k ≥ 1` terms can overshoot, e.g. `k = 1`, `n ≥ 2`; no uniform
  per-term undershoot bound.)
-/
theorem bbpSpigotIntHeadOvershoot_of_zero_excess_dom (n : Nat)
    (h :
      (16 : ℝ) ^ n * (∑ k ∈ range n, bbpSummand (k + 1)) -
          (∑ k ∈ range n, (bbpSpigotTerm (k + 1) n : ℝ)) <
        (bbpSpigotTerm 0 n : ℝ) - (16 : ℝ) ^ n * bbpSummand 0) :
    BBPSpigotIntHeadOvershoot n := by
  unfold BBPSpigotIntHeadOvershoot bbpScaledHead bbpHead
  have hhead :
      (16 : ℝ) ^ n * ∑ k ∈ range (n + 1), bbpSummand k =
        (16 : ℝ) ^ n * bbpSummand 0 +
          (16 : ℝ) ^ n * ∑ k ∈ range n, bbpSummand (k + 1) := by
    have h := congrArg (fun x => (16 : ℝ) ^ n * x) (bbpHead_eq_summand_zero_add_shift n)
    simpa [bbpHead, Finset.mul_sum, mul_add] using h
  have hsum :
      (bbpSpigotIntHeadSum n : ℝ) =
        (bbpSpigotTerm 0 n : ℝ) + ∑ k ∈ range n, (bbpSpigotTerm (k + 1) n : ℝ) :=
    by exact_mod_cast bbpSpigotIntHeadSum_eq_term_zero_add_shift n
  linarith [hhead, hsum, h]

/-- Net `k ≥ 1` analytic-vs-spigot gap appearing in `bbpSpigotIntHeadOvershoot_of_zero_excess_dom`. -/
noncomputable def bbpSpigotIntHeadRestGap (n : Nat) : ℝ :=
  (16 : ℝ) ^ n * (∑ k ∈ range n, bbpSummand (k + 1)) -
    (∑ k ∈ range n, (bbpSpigotTerm (k + 1) n : ℝ))

theorem bbpSpigotIntHeadOvershoot_of_rest_gap (n : Nat)
    (h : bbpSpigotIntHeadRestGap n <
        (bbpSpigotTerm 0 n : ℝ) - (16 : ℝ) ^ n * bbpSummand 0) :
    BBPSpigotIntHeadOvershoot n := by
  dsimp [bbpSpigotIntHeadRestGap] at h
  exact bbpSpigotIntHeadOvershoot_of_zero_excess_dom n h

/--
  **Negative rest gap shortcut:** for `n ≥ 2` the weighted `k ≥ 1` block typically
  net-overshoots (`bbpSpigotIntHeadRestGap n < 0`); with strict k = 0 excess this
  yields head overshoot without expanding the full head sum.
-/
theorem bbpSpigotIntHeadOvershoot_of_neg_rest_gap (n : Nat)
    (hrest : bbpSpigotIntHeadRestGap n < 0) :
    BBPSpigotIntHeadOvershoot n := by
  apply bbpSpigotIntHeadOvershoot_of_rest_gap n
  linarith [bbpSpigotTerm_zero_gt_scaledSummand n, hrest]

theorem bbpSpigotIntHeadRestGap_neg_ten : bbpSpigotIntHeadRestGap 10 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_ten :
    BBPSpigotIntHeadOvershoot 10 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 10 bbpSpigotIntHeadRestGap_neg_ten

theorem bbpSpigotIntHeadRestGap_neg_eleven : bbpSpigotIntHeadRestGap 11 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_eleven :
    BBPSpigotIntHeadOvershoot 11 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 11 bbpSpigotIntHeadRestGap_neg_eleven

theorem bbpSpigotIntHeadRestGap_neg_twelve : bbpSpigotIntHeadRestGap 12 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twelve :
    BBPSpigotIntHeadOvershoot 12 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 12 bbpSpigotIntHeadRestGap_neg_twelve

theorem bbpSpigotIntHeadRestGap_neg_thirteen : bbpSpigotIntHeadRestGap 13 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirteen :
    BBPSpigotIntHeadOvershoot 13 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 13 bbpSpigotIntHeadRestGap_neg_thirteen

theorem bbpSpigotIntHeadRestGap_neg_fourteen : bbpSpigotIntHeadRestGap 14 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_fourteen :
    BBPSpigotIntHeadOvershoot 14 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 14 bbpSpigotIntHeadRestGap_neg_fourteen

theorem bbpSpigotIntHeadRestGap_neg_fifteen : bbpSpigotIntHeadRestGap 15 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_fifteen :
    BBPSpigotIntHeadOvershoot 15 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 15 bbpSpigotIntHeadRestGap_neg_fifteen

theorem bbpSpigotIntHeadRestGap_neg_sixteen : bbpSpigotIntHeadRestGap 16 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_sixteen :
    BBPSpigotIntHeadOvershoot 16 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 16 bbpSpigotIntHeadRestGap_neg_sixteen

theorem bbpSpigotIntHeadSum_gt_scaledHead_zero :
    BBPSpigotIntHeadOvershoot 0 := by
  unfold BBPSpigotIntHeadOvershoot
  have hterm : bbpSpigotIntHeadSum 0 = bbpSpigotTerm 0 0 := by simp [bbpSpigotIntHeadSum]
  rw [hterm]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_one :
    BBPSpigotIntHeadOvershoot 1 := by
  unfold BBPSpigotIntHeadOvershoot
  have hterm :
      bbpSpigotIntHeadSum 1 = bbpSpigotTerm 0 1 + bbpSpigotTerm 1 1 := by
    simp [bbpSpigotIntHeadSum, Finset.sum_range_succ]
  rw [hterm]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_two :
    BBPSpigotIntHeadOvershoot 2 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_three :
    BBPSpigotIntHeadOvershoot 3 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_four :
    BBPSpigotIntHeadOvershoot 4 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_five :
    BBPSpigotIntHeadOvershoot 5 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_six :
    BBPSpigotIntHeadOvershoot 6 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_seven :
    BBPSpigotIntHeadOvershoot 7 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_eight :
    BBPSpigotIntHeadOvershoot 8 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_nine :
    BBPSpigotIntHeadOvershoot 9 := by
  unfold BBPSpigotIntHeadOvershoot
  rw [bbpSpigotIntHeadSum_eq_term_zero_add_shift]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpScaledHead, bbpHead, bbpSummand, bbpCoeff]
  norm_num

/-! ### Tail indexing (certificate depth 50) -/

private lemma bbpIntTailSum_eq_sum_range (n : Nat) :
    bbpIntTailSum n = ∑ j ∈ range 50, bbp_term (n + 1 + j) n := by
  unfold bbpIntTailSum
  have hmap :
      Finset.Icc (n + 1) (n + 50) =
        (Finset.range 50).map ⟨fun j => n + 1 + j, fun j₁ j₂ h => by simp at h; omega⟩ := by
    ext k
    simp [Finset.mem_map, mem_Icc, mem_range]
    constructor
    · intro ⟨hk1, hk2⟩
      refine ⟨k - (n + 1), ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
  rw [hmap, Finset.sum_map]
  rfl

/-! ### Scaled tail remainder (proved from `BBPSeries`) -/

theorem bbpScaledTail_remainder_nonneg (n M : Nat) :
    0 ≤ bbpScaledTail n - bbpScaledTailTrunc n M := by
  exact sub_nonneg.mpr (bbpScaledTailTrunc_le_bbpScaledTail n M)

/-- Tail mass beyond certificate depth `50` (terms after index `n + 50`). -/
noncomputable def bbpScaledTailRemainder (n : Nat) : ℝ :=
  bbpScaledTail n - bbpScaledTailTrunc n 50

theorem bbpScaledTailRemainder_nonneg (n : Nat) :
    0 ≤ bbpScaledTailRemainder n :=
  bbpScaledTail_remainder_nonneg n 50

theorem bbpScaledTailRemainder_lt_one (n : Nat) :
    bbpScaledTailRemainder n < 1 := by
  unfold bbpScaledTailRemainder bbpScaledTailTrunc
  have htrunc :
      0 ≤ (16 : ℝ) ^ n * bbpTailTrunc n 50 :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n) (bbpTailTrunc_nonneg n 50)
  linarith [bbpScaledTail_lt_one n, htrunc, bbpScaledTailTrunc_le_bbpScaledTail n 50]

theorem bbpScaledTail_eq_trunc_plus_remainder (n : Nat) :
    bbpScaledTail n = bbpScaledTailTrunc n 50 + bbpScaledTailRemainder n := by
  unfold bbpScaledTailRemainder
  ring

/-! ### Convergence `Prop`s (priority P-BBP-01) -/

/--
  Unit bracket: `⌊16^n · bbpSeries⌋` equals the legacy certificate sum.
  Integer spigot sums typically overshoot the series, so this is a single
  convergence claim (not a pointwise cast bound).
-/
def BBPIntSeriesBracket (n : Nat) : Prop :=
  (bbpIntFullSum n : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries ∧
    (16 : ℝ) ^ n * bbpSeries < (bbpIntFullSum n : ℝ) + 1

/-- Lower half: certificate sum sits below the scaled series. -/
def BBPIntSeriesBracketLower (n : Nat) : Prop :=
  (bbpIntFullSum n : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries

/-- Upper half: scaled series sits below certificate sum plus one. -/
def BBPIntSeriesBracketUpper (n : Nat) : Prop :=
  (16 : ℝ) ^ n * bbpSeries < (bbpIntFullSum n : ℝ) + 1

theorem bbpIntSeriesBracket_iff_split (n : Nat) :
    BBPIntSeriesBracket n ↔ BBPIntSeriesBracketLower n ∧ BBPIntSeriesBracketUpper n := by
  unfold BBPIntSeriesBracket BBPIntSeriesBracketLower BBPIntSeriesBracketUpper
  tauto

/-- Head/tail gap for the legacy (unweighted) certificate sums. -/
noncomputable def bbpIntHeadGap (n : Nat) : ℝ :=
  bbpScaledHead n - (bbpIntHeadSum n : ℝ)

noncomputable def bbpIntTailGap (n : Nat) : ℝ :=
  bbpScaledTail n - (bbpIntTailSum n : ℝ)

theorem bbpIntHeadGap_eq (n : Nat) :
    bbpIntHeadGap n = bbpScaledHead n - (bbpIntHeadSum n : ℝ) :=
  rfl

theorem bbpIntTailGap_eq (n : Nat) :
    bbpIntTailGap n = bbpScaledTail n - (bbpIntTailSum n : ℝ) :=
  rfl

theorem bbpIntGap_eq_head_add_tail (n : Nat) :
    bbpIntHeadGap n + bbpIntTailGap n =
      (16 : ℝ) ^ n * bbpSeries - (bbpIntFullSum n : ℝ) := by
  rw [bbpIntHeadGap_eq, bbpIntTailGap_eq]
  have hfull := bbpIntFullSum_eq_head_add_tail n
  have hcast : (bbpIntFullSum n : ℝ) =
      (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
    rw [← Nat.cast_add, hfull]
  linarith [bbpSeries_scaled_split n, hcast]

/--
  Sum-level gap target on the legacy certificate block.
-/
def BBPIntGapBracket (n : Nat) : Prop :=
  0 ≤ bbpIntHeadGap n + bbpIntTailGap n ∧
    bbpIntHeadGap n + bbpIntTailGap n < 1

/--
  Weighted spigot bracket (analytic `16^{n-k}` scaling); same convergence claim
  on `bbpSpigotIntFullSum`.
-/
def BBPSpigotIntSeriesBracket (n : Nat) : Prop :=
  (bbpSpigotIntFullSum n : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries ∧
    (16 : ℝ) ^ n * bbpSeries < (bbpSpigotIntFullSum n : ℝ) + 1

/-- Lower half of the weighted spigot bracket. -/
def BBPSpigotIntSeriesBracketLower (n : Nat) : Prop :=
  (bbpSpigotIntFullSum n : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries

/-- Upper half of the weighted spigot bracket. -/
def BBPSpigotIntSeriesBracketUpper (n : Nat) : Prop :=
  (16 : ℝ) ^ n * bbpSeries < (bbpSpigotIntFullSum n : ℝ) + 1

theorem bbpSpigotIntSeriesBracket_iff_split (n : Nat) :
    BBPSpigotIntSeriesBracket n ↔
      BBPSpigotIntSeriesBracketLower n ∧ BBPSpigotIntSeriesBracketUpper n := by
  unfold BBPSpigotIntSeriesBracket BBPSpigotIntSeriesBracketLower BBPSpigotIntSeriesBracketUpper
  tauto

/-- Head/tail gap from the proved scaled split (sum-level, not per-term). -/
noncomputable def bbpSpigotIntHeadGap (n : Nat) : ℝ :=
  bbpScaledHead n - (bbpSpigotIntHeadSum n : ℝ)

noncomputable def bbpSpigotIntTailGap (n : Nat) : ℝ :=
  bbpScaledTail n - (bbpSpigotIntTailSum n : ℝ)

theorem bbpSpigotIntHeadGap_eq (n : Nat) :
    bbpSpigotIntHeadGap n = bbpScaledHead n - (bbpSpigotIntHeadSum n : ℝ) :=
  rfl

theorem bbpSpigotIntTailGap_eq (n : Nat) :
    bbpSpigotIntTailGap n = bbpScaledTail n - (bbpSpigotIntTailSum n : ℝ) :=
  rfl

theorem bbpSpigotIntTailGap_eq_scaledTail (n : Nat) :
    bbpSpigotIntTailGap n = bbpScaledTail n := by
  unfold bbpSpigotIntTailGap
  rw [bbpSpigotIntTailSum_eq_zero]
  simp

theorem bbpSpigotIntGap_eq_head_add_tail (n : Nat) :
    bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n =
      (16 : ℝ) ^ n * bbpSeries - (bbpSpigotIntFullSum n : ℝ) := by
  rw [bbpSpigotIntHeadGap_eq, bbpSpigotIntTailGap_eq]
  have hfull := bbpSpigotIntFullSum_eq_head_add_tail n
  have hcast : (bbpSpigotIntFullSum n : ℝ) =
      (bbpSpigotIntHeadSum n : ℝ) + (bbpSpigotIntTailSum n : ℝ) := by
    rw [← Nat.cast_add, hfull]
  linarith [bbpSeries_scaled_split n, hcast]

theorem bbpSpigotIntSeriesBracketLower_iff_gap_nonneg (n : Nat) :
    BBPSpigotIntSeriesBracketLower n ↔ 0 ≤ bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n := by
  constructor
  · intro h
    unfold BBPSpigotIntSeriesBracketLower at h
    linarith [bbpSpigotIntGap_eq_head_add_tail n, h]
  · intro h
    unfold BBPSpigotIntSeriesBracketLower
    linarith [bbpSpigotIntGap_eq_head_add_tail n, h]

theorem bbpSpigotIntSeriesBracketUpper_iff_gap_lt_one (n : Nat) :
    BBPSpigotIntSeriesBracketUpper n ↔
      bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n < 1 := by
  constructor
  · intro h
    unfold BBPSpigotIntSeriesBracketUpper at h
    linarith [bbpSpigotIntGap_eq_head_add_tail n, h]
  · intro h
    unfold BBPSpigotIntSeriesBracketUpper
    linarith [bbpSpigotIntGap_eq_head_add_tail n, h]

/--
  Sum-level head slack: weighted integer head may undershoot `bbpScaledHead` by at most `s`.
-/
def BBPSpigotIntHeadSlack (n : Nat) (s : ℝ) : Prop :=
  bbpScaledHead n - s ≤ (bbpSpigotIntHeadSum n : ℝ) ∧
    (bbpSpigotIntHeadSum n : ℝ) ≤ bbpScaledHead n + s

/--
  Head gap strictly below a budget (typical subgoal for the upper bracket).
-/
def BBPSpigotIntHeadGapBound (n : Nat) (t : ℝ) : Prop :=
  bbpSpigotIntHeadGap n < t

/--
  Sum-level gap target: total head+tail gap in `[0,1)`.
-/
def BBPSpigotIntGapBracket (n : Nat) : Prop :=
  0 ≤ bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n ∧
    bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n < 1

theorem bbpSpigotIntGapBracket_iff_bracket (n : Nat) :
    BBPSpigotIntGapBracket n ↔ BBPSpigotIntSeriesBracket n := by
  unfold BBPSpigotIntGapBracket
  rw [bbpSpigotIntSeriesBracket_iff_split n,
    bbpSpigotIntSeriesBracketLower_iff_gap_nonneg n,
    bbpSpigotIntSeriesBracketUpper_iff_gap_lt_one n]

/--
  Integer head overshoots scaled head by at most `s` (correct inequality direction).
 -/
def BBPIntHeadSlack (n : Nat) (s : ℝ) : Prop :=
  bbpScaledHead n ≤ (bbpIntHeadSum n : ℝ) ∧
    (bbpIntHeadSum n : ℝ) ≤ bbpScaledHead n + s

/--
  Floor slack: certificate sum tracks `⌊16^n · bbpSeries⌋` within `s`.
-/
def BBPIntFloorSlack (n : Nat) (s : ℕ) : Prop :=
  ⌊(16 : ℝ) ^ n * bbpSeries⌋ ≤ bbpIntFullSum n ∧
    bbpIntFullSum n ≤ ⌊(16 : ℝ) ^ n * bbpSeries⌋ + s

/--
  Legacy `50`-term tail vs scaled truncation (unweighted `bbp_term` sums).

  **Not provable for `n ≥ 1`:** legacy tail terms keep full `16^n` scaling, so the
  block overshoots `bbpScaledTailTrunc` (e.g. `n = 1`: tail sum `7` vs trunc `< 1`).
  Retained as a named subgoal for the legacy certificate track only.
-/
def BBPIntTailCertBound (n : Nat) : Prop :=
  (bbpIntTailSum n : ℝ) ≤ bbpScaledTailTrunc n 50

/--
  Weighted tail bound on the analytic spigot block.
  **Proved unconditionally** (`bbpSpigotIntTailCertBound_holds`): tail terms with
  `k > n` vanish, so the integer tail sum is `0`.
-/
def BBPSpigotIntTailCertBound (n : Nat) : Prop :=
  (bbpSpigotIntTailSum n : ℝ) ≤ bbpScaledTailTrunc n 50

theorem bbpScaledTailTrunc_nonneg (n M : Nat) : 0 ≤ bbpScaledTailTrunc n M := by
  unfold bbpScaledTailTrunc
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n) (bbpTailTrunc_nonneg n M)

theorem bbpSpigotIntTailCertBound_holds (n : Nat) : BBPSpigotIntTailCertBound n := by
  unfold BBPSpigotIntTailCertBound
  rw [bbpSpigotIntTailSum_eq_zero]
  exact mod_cast bbpScaledTailTrunc_nonneg n 50

/--
  Per-term cast bound for weighted spigot terms.
  **Not provable in general:** per-branch `Nat` division then subtraction can
  overshoot the analytic term (e.g. `bbpSpigotTerm 0 1 = 51` while
  `16^1 · bbpSummand 0 < 51`). Convergence is a **sum-level** bracket claim.
-/
def BBPSpigotTermCastBound (k n : Nat) : Prop :=
  (bbpSpigotTerm k n : ℝ) ≤ (16 : ℝ) ^ n * bbpSummand k

def BBPSpigotIntHeadCertBound (n : Nat) : Prop :=
  (bbpSpigotIntHeadSum n : ℝ) ≤ bbpScaledHead n

theorem bbpSpigotIntHeadCertBound_of_term_bounds (n : Nat)
    (h : ∀ k ∈ range (n + 1), BBPSpigotTermCastBound k n) :
    BBPSpigotIntHeadCertBound n := by
  unfold BBPSpigotIntHeadCertBound bbpSpigotIntHeadSum bbpScaledHead bbpHead
  have hterm :
      ∀ k ∈ range (n + 1), (bbpSpigotTerm k n : ℝ) ≤ (16 : ℝ) ^ n * bbpSummand k :=
    fun k hk => h k hk
  calc
    (bbpSpigotIntHeadSum n : ℝ) = ∑ k ∈ range (n + 1), (bbpSpigotTerm k n : ℝ) := by
      simp [bbpSpigotIntHeadSum]
    _ ≤ ∑ k ∈ range (n + 1), (16 : ℝ) ^ n * bbpSummand k := Finset.sum_le_sum hterm
    _ = (16 : ℝ) ^ n * ∑ k ∈ range (n + 1), bbpSummand k := by rw [Finset.mul_sum]
    _ = bbpScaledHead n := by simp [bbpScaledHead, bbpHead]

theorem bbpSpigotIntTailCertBound_of_term_bounds (n : Nat)
    (h : ∀ j ∈ range 50, BBPSpigotTermCastBound (n + 1 + j) n) :
    BBPSpigotIntTailCertBound n := by
  unfold BBPSpigotIntTailCertBound bbpSpigotIntTailSum bbpScaledTailTrunc bbpTailTrunc
  have hterm :
      ∀ j ∈ range 50, (bbpSpigotTerm (n + 1 + j) n : ℝ) ≤ (16 : ℝ) ^ n * bbpSummand (n + 1 + j) :=
    fun j hj => h j hj
  calc
    (bbpSpigotIntTailSum n : ℝ) =
        ∑ j ∈ range 50, (bbpSpigotTerm (n + 1 + j) n : ℝ) := by
      rw [← Nat.cast_sum, bbpSpigotIntTailSum_eq_sum_range]
    _ ≤ ∑ j ∈ range 50, (16 : ℝ) ^ n * bbpSummand (n + 1 + j) :=
      Finset.sum_le_sum hterm
    _ = bbpScaledTailTrunc n 50 := by
      simp [bbpScaledTailTrunc, bbpTailTrunc, Finset.mul_sum]

theorem bbpSpigotIntFullSum_le_scaled_trunc_of_bounds (n : Nat)
    (hHead : BBPSpigotIntHeadCertBound n) (hTail : BBPSpigotIntTailCertBound n) :
    (bbpSpigotIntFullSum n : ℝ) ≤ bbpScaledHead n + bbpScaledTailTrunc n 50 := by
  have hsplit := bbpSpigotIntFullSum_eq_head_add_tail n
  calc
    (bbpSpigotIntFullSum n : ℝ) =
        (bbpSpigotIntHeadSum n : ℝ) + (bbpSpigotIntTailSum n : ℝ) := by
      rw [← Nat.cast_add, hsplit]
    _ ≤ bbpScaledHead n + bbpScaledTailTrunc n 50 :=
      add_le_add (by simpa [BBPSpigotIntHeadCertBound] using hHead)
        (by simpa [BBPSpigotIntTailCertBound] using hTail)

theorem bbpSpigotIntSeriesBracket_lower_of_bounds (n : Nat)
    (hHead : BBPSpigotIntHeadCertBound n) (hTail : BBPSpigotIntTailCertBound n) :
    BBPSpigotIntSeriesBracketLower n := by
  unfold BBPSpigotIntSeriesBracketLower
  have htrunc := bbpSpigotIntFullSum_le_scaled_trunc_of_bounds n hHead hTail
  have hsplit := bbpSeries_scaled_split n
  have hhead_tail := bbpScaledHead_plus_tailTrunc n 50
  have htail := bbpScaledTailTrunc_le_bbpScaledTail n 50
  linarith [htrunc, hsplit, hhead_tail, bbpScaledTail_nonneg n]

theorem bbpSpigotIntTailGap_ge_remainder_of (n : Nat) (h : BBPSpigotIntTailCertBound n) :
    bbpScaledTailRemainder n ≤ bbpSpigotIntTailGap n := by
  unfold bbpSpigotIntTailGap bbpScaledTailRemainder
  simpa [BBPSpigotIntTailCertBound] using
    sub_le_sub_left h (bbpScaledTail n)

theorem bbpSpigotIntTailGap_lt_one_of (n : Nat) (h : BBPSpigotIntTailCertBound n) :
    bbpSpigotIntTailGap n < 1 := by
  unfold bbpSpigotIntTailGap
  have hnonneg : 0 ≤ (bbpSpigotIntTailSum n : ℝ) :=
    mod_cast Finset.sum_nonneg fun k _ =>
      Nat.zero_le (bbpSpigotTerm k n)
  linarith [h, bbpScaledTail_lt_one n, hnonneg]

theorem bbpSpigotIntSeriesBracket_upper_of_gap (n : Nat)
    (h : bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n < 1) :
    BBPSpigotIntSeriesBracketUpper n :=
  (bbpSpigotIntSeriesBracketUpper_iff_gap_lt_one n).mpr h

theorem bbpSpigotIntSeriesBracket_upper_of_head_gap_budget (n : Nat)
    (hHead : BBPSpigotIntHeadGapBound n (1 - bbpSpigotIntTailGap n)) :
    BBPSpigotIntSeriesBracketUpper n := by
  unfold BBPSpigotIntHeadGapBound at hHead
  unfold BBPSpigotIntSeriesBracketUpper
  linarith [bbpSpigotIntGap_eq_head_add_tail n, hHead]

/--
  Remainder-based head budget implies the upper bracket once the tail gap equals
  the proved remainder (typically `bbpSpigotIntTailSum = 0` and tight tail control).
-/
theorem bbpSpigotIntSeriesBracket_upper_of_head_budget (n : Nat)
    (_hTail : BBPSpigotIntTailCertBound n)
    (hHead : BBPSpigotIntHeadGapBound n (1 - bbpSpigotIntTailGap n)) :
    BBPSpigotIntSeriesBracketUpper n :=
  bbpSpigotIntSeriesBracket_upper_of_head_gap_budget n hHead

theorem bbpSpigotIntSeriesBracket_upper_of_head_budget_proved (n : Nat)
    (hHead : BBPSpigotIntHeadGapBound n (1 - bbpSpigotIntTailGap n)) :
    BBPSpigotIntSeriesBracketUpper n :=
  bbpSpigotIntSeriesBracket_upper_of_head_gap_budget n hHead

theorem bbpSpigotIntGap_eq_head_plus_scaledTail (n : Nat) :
    bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n =
      bbpSpigotIntHeadGap n + bbpScaledTail n := by
  rw [bbpSpigotIntTailGap_eq_scaledTail n]

/--
  **Proved upper half shortcut:** once the integer head overshoots `bbpScaledHead`,
  the tail gap is exactly `bbpScaledTail` (`bbpSpigotIntTailSum = 0`), hence the
  total gap is below `bbpScaledTail < 1`.
-/
theorem bbpSpigotIntSeriesBracket_upper_of_head_overshoot (n : Nat)
    (h : bbpScaledHead n < (bbpSpigotIntHeadSum n : ℝ)) :
    BBPSpigotIntSeriesBracketUpper n := by
  rw [bbpSpigotIntSeriesBracketUpper_iff_gap_lt_one]
  rw [bbpSpigotIntGap_eq_head_plus_scaledTail]
  have htail := bbpScaledTail_lt_one n
  linarith [bbpSpigotIntHeadGap_eq n, h, htail]

theorem bbpSpigotIntSeriesBracket_upper_holds_zero :
    BBPSpigotIntSeriesBracketUpper 0 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 0 bbpSpigotIntHeadSum_gt_scaledHead_zero

theorem bbpSpigotIntSeriesBracket_upper_holds_one :
    BBPSpigotIntSeriesBracketUpper 1 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 1 bbpSpigotIntHeadSum_gt_scaledHead_one

theorem bbpSpigotIntSeriesBracket_upper_holds_two :
    BBPSpigotIntSeriesBracketUpper 2 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 2 bbpSpigotIntHeadSum_gt_scaledHead_two

theorem bbpSpigotIntSeriesBracket_upper_holds_three :
    BBPSpigotIntSeriesBracketUpper 3 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 3 bbpSpigotIntHeadSum_gt_scaledHead_three

theorem bbpSpigotIntSeriesBracket_upper_holds_four :
    BBPSpigotIntSeriesBracketUpper 4 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 4 bbpSpigotIntHeadSum_gt_scaledHead_four

theorem bbpSpigotIntSeriesBracket_upper_holds_five :
    BBPSpigotIntSeriesBracketUpper 5 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 5 bbpSpigotIntHeadSum_gt_scaledHead_five

theorem bbpSpigotIntSeriesBracket_upper_holds_six :
    BBPSpigotIntSeriesBracketUpper 6 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 6 bbpSpigotIntHeadSum_gt_scaledHead_six

theorem bbpSpigotIntSeriesBracket_upper_holds_seven :
    BBPSpigotIntSeriesBracketUpper 7 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 7 bbpSpigotIntHeadSum_gt_scaledHead_seven

theorem bbpSpigotIntSeriesBracket_upper_holds_eight :
    BBPSpigotIntSeriesBracketUpper 8 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 8 bbpSpigotIntHeadSum_gt_scaledHead_eight

theorem bbpSpigotIntSeriesBracket_upper_holds_nine :
    BBPSpigotIntSeriesBracketUpper 9 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 9 bbpSpigotIntHeadSum_gt_scaledHead_nine

theorem bbpSpigotIntSeriesBracket_upper_holds_ten :
    BBPSpigotIntSeriesBracketUpper 10 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 10 bbpSpigotIntHeadSum_gt_scaledHead_ten

theorem bbpSpigotIntSeriesBracket_upper_holds_eleven :
    BBPSpigotIntSeriesBracketUpper 11 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 11 bbpSpigotIntHeadSum_gt_scaledHead_eleven

theorem bbpSpigotIntSeriesBracket_upper_holds_twelve :
    BBPSpigotIntSeriesBracketUpper 12 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 12 bbpSpigotIntHeadSum_gt_scaledHead_twelve

theorem bbpSpigotIntSeriesBracket_upper_holds_thirteen :
    BBPSpigotIntSeriesBracketUpper 13 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 13 bbpSpigotIntHeadSum_gt_scaledHead_thirteen

theorem bbpSpigotIntSeriesBracket_upper_holds_fourteen :
    BBPSpigotIntSeriesBracketUpper 14 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 14 bbpSpigotIntHeadSum_gt_scaledHead_fourteen

theorem bbpSpigotIntSeriesBracket_upper_holds_fifteen :
    BBPSpigotIntSeriesBracketUpper 15 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 15 bbpSpigotIntHeadSum_gt_scaledHead_fifteen

theorem bbpSpigotIntSeriesBracket_upper_holds_sixteen :
    BBPSpigotIntSeriesBracketUpper 16 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 16 bbpSpigotIntHeadSum_gt_scaledHead_sixteen

theorem bbpSpigotIntHeadRestGap_neg_seventeen : bbpSpigotIntHeadRestGap 17 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_seventeen :
    BBPSpigotIntHeadOvershoot 17 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 17 bbpSpigotIntHeadRestGap_neg_seventeen

theorem bbpSpigotIntSeriesBracket_upper_holds_seventeen :
    BBPSpigotIntSeriesBracketUpper 17 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 17 bbpSpigotIntHeadSum_gt_scaledHead_seventeen

theorem bbpSpigotIntHeadRestGap_neg_eighteen : bbpSpigotIntHeadRestGap 18 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_eighteen :
    BBPSpigotIntHeadOvershoot 18 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 18 bbpSpigotIntHeadRestGap_neg_eighteen

theorem bbpSpigotIntSeriesBracket_upper_holds_eighteen :
    BBPSpigotIntSeriesBracketUpper 18 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 18 bbpSpigotIntHeadSum_gt_scaledHead_eighteen

theorem bbpSpigotIntHeadRestGap_neg_nineteen : bbpSpigotIntHeadRestGap 19 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_nineteen :
    BBPSpigotIntHeadOvershoot 19 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 19 bbpSpigotIntHeadRestGap_neg_nineteen

theorem bbpSpigotIntSeriesBracket_upper_holds_nineteen :
    BBPSpigotIntSeriesBracketUpper 19 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 19 bbpSpigotIntHeadSum_gt_scaledHead_nineteen

theorem bbpSpigotIntHeadRestGap_neg_twenty : bbpSpigotIntHeadRestGap 20 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty :
    BBPSpigotIntHeadOvershoot 20 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 20 bbpSpigotIntHeadRestGap_neg_twenty

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty :
    BBPSpigotIntSeriesBracketUpper 20 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 20 bbpSpigotIntHeadSum_gt_scaledHead_twenty

theorem bbpSpigotIntHeadRestGap_neg_twenty_one : bbpSpigotIntHeadRestGap 21 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_one :
    BBPSpigotIntHeadOvershoot 21 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 21 bbpSpigotIntHeadRestGap_neg_twenty_one

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_one :
    BBPSpigotIntSeriesBracketUpper 21 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 21 bbpSpigotIntHeadSum_gt_scaledHead_twenty_one

theorem bbpSpigotIntHeadRestGap_neg_twenty_two : bbpSpigotIntHeadRestGap 22 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_two :
    BBPSpigotIntHeadOvershoot 22 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 22 bbpSpigotIntHeadRestGap_neg_twenty_two

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_two :
    BBPSpigotIntSeriesBracketUpper 22 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 22 bbpSpigotIntHeadSum_gt_scaledHead_twenty_two

theorem bbpSpigotIntHeadRestGap_neg_twenty_three : bbpSpigotIntHeadRestGap 23 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_three :
    BBPSpigotIntHeadOvershoot 23 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 23 bbpSpigotIntHeadRestGap_neg_twenty_three

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_three :
    BBPSpigotIntSeriesBracketUpper 23 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 23 bbpSpigotIntHeadSum_gt_scaledHead_twenty_three

theorem bbpSpigotIntHeadRestGap_neg_twenty_four : bbpSpigotIntHeadRestGap 24 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_four :
    BBPSpigotIntHeadOvershoot 24 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 24 bbpSpigotIntHeadRestGap_neg_twenty_four

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_four :
    BBPSpigotIntSeriesBracketUpper 24 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 24 bbpSpigotIntHeadSum_gt_scaledHead_twenty_four

theorem bbpSpigotIntHeadRestGap_neg_twenty_five : bbpSpigotIntHeadRestGap 25 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_five :
    BBPSpigotIntHeadOvershoot 25 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 25 bbpSpigotIntHeadRestGap_neg_twenty_five

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_five :
    BBPSpigotIntSeriesBracketUpper 25 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 25 bbpSpigotIntHeadSum_gt_scaledHead_twenty_five

theorem bbpSpigotIntHeadRestGap_neg_twenty_six : bbpSpigotIntHeadRestGap 26 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_six :
    BBPSpigotIntHeadOvershoot 26 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 26 bbpSpigotIntHeadRestGap_neg_twenty_six

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_six :
    BBPSpigotIntSeriesBracketUpper 26 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 26 bbpSpigotIntHeadSum_gt_scaledHead_twenty_six

theorem bbpSpigotIntHeadRestGap_neg_twenty_seven : bbpSpigotIntHeadRestGap 27 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_seven :
    BBPSpigotIntHeadOvershoot 27 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 27 bbpSpigotIntHeadRestGap_neg_twenty_seven

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_seven :
    BBPSpigotIntSeriesBracketUpper 27 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 27 bbpSpigotIntHeadSum_gt_scaledHead_twenty_seven

theorem bbpSpigotIntHeadRestGap_neg_twenty_eight : bbpSpigotIntHeadRestGap 28 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_eight :
    BBPSpigotIntHeadOvershoot 28 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 28 bbpSpigotIntHeadRestGap_neg_twenty_eight

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_eight :
    BBPSpigotIntSeriesBracketUpper 28 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 28 bbpSpigotIntHeadSum_gt_scaledHead_twenty_eight

theorem bbpSpigotIntHeadRestGap_neg_twenty_nine : bbpSpigotIntHeadRestGap 29 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_twenty_nine :
    BBPSpigotIntHeadOvershoot 29 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 29 bbpSpigotIntHeadRestGap_neg_twenty_nine

theorem bbpSpigotIntSeriesBracket_upper_holds_twenty_nine :
    BBPSpigotIntSeriesBracketUpper 29 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 29 bbpSpigotIntHeadSum_gt_scaledHead_twenty_nine

theorem bbpSpigotIntHeadRestGap_neg_thirty : bbpSpigotIntHeadRestGap 30 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty :
    BBPSpigotIntHeadOvershoot 30 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 30 bbpSpigotIntHeadRestGap_neg_thirty

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty :
    BBPSpigotIntSeriesBracketUpper 30 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 30 bbpSpigotIntHeadSum_gt_scaledHead_thirty

theorem bbpSpigotIntHeadRestGap_neg_thirty_one : bbpSpigotIntHeadRestGap 31 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_one :
    BBPSpigotIntHeadOvershoot 31 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 31 bbpSpigotIntHeadRestGap_neg_thirty_one

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_one :
    BBPSpigotIntSeriesBracketUpper 31 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 31 bbpSpigotIntHeadSum_gt_scaledHead_thirty_one

theorem bbpSpigotIntHeadRestGap_neg_thirty_two : bbpSpigotIntHeadRestGap 32 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_two :
    BBPSpigotIntHeadOvershoot 32 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 32 bbpSpigotIntHeadRestGap_neg_thirty_two

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_two :
    BBPSpigotIntSeriesBracketUpper 32 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 32 bbpSpigotIntHeadSum_gt_scaledHead_thirty_two

theorem bbpSpigotIntHeadRestGap_neg_thirty_three : bbpSpigotIntHeadRestGap 33 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_three :
    BBPSpigotIntHeadOvershoot 33 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 33 bbpSpigotIntHeadRestGap_neg_thirty_three

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_three :
    BBPSpigotIntSeriesBracketUpper 33 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 33 bbpSpigotIntHeadSum_gt_scaledHead_thirty_three

theorem bbpSpigotIntHeadRestGap_neg_thirty_four : bbpSpigotIntHeadRestGap 34 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_four :
    BBPSpigotIntHeadOvershoot 34 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 34 bbpSpigotIntHeadRestGap_neg_thirty_four

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_four :
    BBPSpigotIntSeriesBracketUpper 34 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 34 bbpSpigotIntHeadSum_gt_scaledHead_thirty_four

theorem bbpSpigotIntHeadRestGap_neg_thirty_five : bbpSpigotIntHeadRestGap 35 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_five :
    BBPSpigotIntHeadOvershoot 35 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 35 bbpSpigotIntHeadRestGap_neg_thirty_five

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_five :
    BBPSpigotIntSeriesBracketUpper 35 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 35 bbpSpigotIntHeadSum_gt_scaledHead_thirty_five

theorem bbpSpigotIntHeadRestGap_neg_thirty_six : bbpSpigotIntHeadRestGap 36 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_six :
    BBPSpigotIntHeadOvershoot 36 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 36 bbpSpigotIntHeadRestGap_neg_thirty_six

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_six :
    BBPSpigotIntSeriesBracketUpper 36 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 36 bbpSpigotIntHeadSum_gt_scaledHead_thirty_six

theorem bbpSpigotIntHeadRestGap_neg_thirty_seven : bbpSpigotIntHeadRestGap 37 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_seven :
    BBPSpigotIntHeadOvershoot 37 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 37 bbpSpigotIntHeadRestGap_neg_thirty_seven

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_seven :
    BBPSpigotIntSeriesBracketUpper 37 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 37 bbpSpigotIntHeadSum_gt_scaledHead_thirty_seven

theorem bbpSpigotIntHeadRestGap_neg_thirty_eight : bbpSpigotIntHeadRestGap 38 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_eight :
    BBPSpigotIntHeadOvershoot 38 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 38 bbpSpigotIntHeadRestGap_neg_thirty_eight

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_eight :
    BBPSpigotIntSeriesBracketUpper 38 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 38 bbpSpigotIntHeadSum_gt_scaledHead_thirty_eight

theorem bbpSpigotIntHeadRestGap_neg_thirty_nine : bbpSpigotIntHeadRestGap 39 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_thirty_nine :
    BBPSpigotIntHeadOvershoot 39 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 39 bbpSpigotIntHeadRestGap_neg_thirty_nine

theorem bbpSpigotIntSeriesBracket_upper_holds_thirty_nine :
    BBPSpigotIntSeriesBracketUpper 39 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 39 bbpSpigotIntHeadSum_gt_scaledHead_thirty_nine

theorem bbpSpigotIntHeadRestGap_neg_forty : bbpSpigotIntHeadRestGap 40 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty :
    BBPSpigotIntHeadOvershoot 40 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 40 bbpSpigotIntHeadRestGap_neg_forty

theorem bbpSpigotIntSeriesBracket_upper_holds_forty :
    BBPSpigotIntSeriesBracketUpper 40 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 40 bbpSpigotIntHeadSum_gt_scaledHead_forty

theorem bbpSpigotIntHeadRestGap_neg_forty_one : bbpSpigotIntHeadRestGap 41 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty_one :
    BBPSpigotIntHeadOvershoot 41 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 41 bbpSpigotIntHeadRestGap_neg_forty_one

theorem bbpSpigotIntSeriesBracket_upper_holds_forty_one :
    BBPSpigotIntSeriesBracketUpper 41 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 41 bbpSpigotIntHeadSum_gt_scaledHead_forty_one

theorem bbpSpigotIntHeadRestGap_neg_forty_two : bbpSpigotIntHeadRestGap 42 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty_two :
    BBPSpigotIntHeadOvershoot 42 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 42 bbpSpigotIntHeadRestGap_neg_forty_two

theorem bbpSpigotIntSeriesBracket_upper_holds_forty_two :
    BBPSpigotIntSeriesBracketUpper 42 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 42 bbpSpigotIntHeadSum_gt_scaledHead_forty_two

theorem bbpSpigotIntHeadRestGap_neg_forty_three : bbpSpigotIntHeadRestGap 43 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty_three :
    BBPSpigotIntHeadOvershoot 43 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 43 bbpSpigotIntHeadRestGap_neg_forty_three

theorem bbpSpigotIntSeriesBracket_upper_holds_forty_three :
    BBPSpigotIntSeriesBracketUpper 43 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 43 bbpSpigotIntHeadSum_gt_scaledHead_forty_three

theorem bbpSpigotIntHeadRestGap_neg_forty_four : bbpSpigotIntHeadRestGap 44 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty_four :
    BBPSpigotIntHeadOvershoot 44 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 44 bbpSpigotIntHeadRestGap_neg_forty_four

theorem bbpSpigotIntSeriesBracket_upper_holds_forty_four :
    BBPSpigotIntSeriesBracketUpper 44 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 44 bbpSpigotIntHeadSum_gt_scaledHead_forty_four

theorem bbpSpigotIntHeadRestGap_neg_forty_five : bbpSpigotIntHeadRestGap 45 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty_five :
    BBPSpigotIntHeadOvershoot 45 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 45 bbpSpigotIntHeadRestGap_neg_forty_five

theorem bbpSpigotIntSeriesBracket_upper_holds_forty_five :
    BBPSpigotIntSeriesBracketUpper 45 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 45 bbpSpigotIntHeadSum_gt_scaledHead_forty_five

theorem bbpSpigotIntHeadRestGap_neg_forty_six : bbpSpigotIntHeadRestGap 46 < 0 := by
  dsimp [bbpSpigotIntHeadRestGap]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  repeat rw [Finset.sum_range_succ]
  dsimp [bbpSpigotTerm, bbpSummand, bbpCoeff]
  norm_num

theorem bbpSpigotIntHeadSum_gt_scaledHead_forty_six :
    BBPSpigotIntHeadOvershoot 46 :=
  bbpSpigotIntHeadOvershoot_of_neg_rest_gap 46 bbpSpigotIntHeadRestGap_neg_forty_six

theorem bbpSpigotIntSeriesBracket_upper_holds_forty_six :
    BBPSpigotIntSeriesBracketUpper 46 :=
  bbpSpigotIntSeriesBracket_upper_of_head_overshoot 46 bbpSpigotIntHeadSum_gt_scaledHead_forty_six

/-- Computable gap-floor digit (`Int.emod` semantics); shadow for `native_decide`. -/
def bbpHexDigitOfGapFloorZ (z : ℤ) : Nat :=
  Int.toNat (z % 16)

/--
  Hex digit from `⌊16·g⌋`, stable when `g` differs from `{16^n·bbpSeries}` by an integer offset.
-/
noncomputable def bbpHexDigitOfGapFloor (z : ℤ) : Nat :=
  bbpHexDigitOfGapFloorZ z

theorem bbpHexDigitOfGapFloor_eq_Z (z : ℤ) :
    bbpHexDigitOfGapFloor z = bbpHexDigitOfGapFloorZ z := rfl

theorem bbpHexDigitOfGapFloorZ_eq_of_emod_eq {z w : ℤ} (h : z % 16 = w % 16) :
    bbpHexDigitOfGapFloorZ z = bbpHexDigitOfGapFloorZ w := by
  dsimp [bbpHexDigitOfGapFloorZ]
  rw [h]

private lemma bbpHexDigitOfGapFloor_eq_toNat_mod {z : ℤ} (hz : 0 ≤ z) (hz' : z < 16) :
    bbpHexDigitOfGapFloor z = Int.toNat z % 16 := by
  dsimp [bbpHexDigitOfGapFloor, bbpHexDigitOfGapFloorZ]
  rw [Int.emod_eq_of_lt hz hz']
  exact (Nat.mod_eq_of_lt ((Int.toNat_lt_of_ne_zero (n := 16) (by decide : 16 ≠ 0)).mpr hz')).symm

theorem bbpSpigotIntFloor_le_headSum_of_upper (n : Nat)
    (h : BBPSpigotIntSeriesBracketUpper n) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ ≤ (bbpSpigotIntHeadSum n : ℤ) := by
  unfold BBPSpigotIntSeriesBracketUpper at h
  have hfull := bbpSpigotIntFullSum_eq_head_add_tail n
  have htail := bbpSpigotIntTailSum_eq_zero n
  have heq : (bbpSpigotIntFullSum n : ℝ) = (bbpSpigotIntHeadSum n : ℝ) := by
    rw [hfull, htail, add_zero]
  rw [heq] at h
  exact (Int.floor_le_iff (a := (16 : ℝ) ^ n * bbpSeries) (z := (bbpSpigotIntHeadSum n : ℤ))).mpr h

theorem bbpIntFloor_le_fullSum_of_upper (n : Nat)
    (h : BBPIntSeriesBracketUpper n) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ ≤ (bbpIntFullSum n : ℤ) := by
  unfold BBPIntSeriesBracketUpper at h
  exact (Int.floor_le_iff (a := (16 : ℝ) ^ n * bbpSeries) (z := (bbpIntFullSum n : ℤ))).mpr h

/-- Legacy certificate overshoot above `⌊16^n · bbpSeries⌋` (integer slack). -/
noncomputable def bbpIntFloorDelta (n : Nat) : ℤ :=
  (bbpIntFullSum n : ℤ) - ⌊(16 : ℝ) ^ n * bbpSeries⌋

theorem bbpIntFloorDelta_eq (n : Nat) :
    (bbpIntFullSum n : ℤ) = ⌊(16 : ℝ) ^ n * bbpSeries⌋ + bbpIntFloorDelta n := by
  unfold bbpIntFloorDelta
  ring

theorem bbpIntFloorDelta_nonneg (n : Nat) (h : BBPIntSeriesBracketUpper n) :
    0 ≤ bbpIntFloorDelta n := by
  unfold bbpIntFloorDelta
  exact sub_nonneg.mpr (bbpIntFloor_le_fullSum_of_upper n h)

/--
  **Upper-only digit link:** `⌊16·{16^n·bbpSeries}⌋ mod 16` from the weighted spigot gap.
  The gap may be negative once head overshoots; use `bbpHexDigitOfGapFloor` (emod-stable).
-/
theorem bbpHexDigitSeries_eq_spigot_gap_floor_of_upper (n : Nat)
    (h : BBPSpigotIntSeriesBracketUpper n) :
    (Int.toNat ⌊16 * Int.fract ((16 : ℝ) ^ n * bbpSeries)⌋) % 16 =
      bbpHexDigitOfGapFloor
        ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋ := by
  set x : ℝ := (16 : ℝ) ^ n * bbpSeries
  set s : ℝ := (bbpSpigotIntHeadSum n : ℝ)
  set δ : ℤ := (bbpSpigotIntHeadSum n : ℤ) - ⌊x⌋
  have hfloor := bbpSpigotIntFloor_le_headSum_of_upper n h
  have hδ : 0 ≤ δ := sub_nonneg.mpr hfloor
  have hδ_cast : (δ : ℝ) = s - ↑(⌊x⌋) := by
    dsimp [δ, s]
    norm_cast
  have hgap :
      x - s = Int.fract x - (δ : ℝ) := by
    calc
      x - s = (Int.fract x + ↑(⌊x⌋)) - s := by rw [Int.fract_add_floor x]
      _ = Int.fract x - (s - ↑(⌊x⌋)) := by ring
      _ = Int.fract x - (δ : ℝ) := by rw [hδ_cast]
  have hfloor16 :
      ⌊16 * (Int.fract x - (δ : ℝ))⌋ = ⌊16 * Int.fract x⌋ - 16 * δ := by
    have hcast : (16 : ℝ) * (δ : ℝ) = ((16 * δ : ℤ) : ℝ) := by push_cast; ring
    have hmul :
        (16 : ℝ) * (Int.fract x - (δ : ℝ)) = 16 * Int.fract x - (16 : ℝ) * (δ : ℝ) := by ring
    rw [hmul, hcast, Int.floor_sub_intCast]
  have hmod :
      (⌊16 * Int.fract x⌋ - 16 * δ) % 16 = ⌊16 * Int.fract x⌋ % 16 := by
    have hzero : (16 * δ : ℤ) ≡ 0 [ZMOD 16] := (Int.dvd_mul_right 16 δ).modEq_zero_int
    simpa [sub_zero] using (Int.ModEq.refl ⌊16 * Int.fract x⌋).sub hzero |>.eq
  have hfract_nonneg : 0 ≤ Int.fract x := by
    simp only [Int.fract]
    linarith [Int.floor_le x]
  have hfract_lt : Int.fract x < 1 := by
    simp only [Int.fract]
    linarith [Int.lt_floor_add_one x]
  have hmul_nonneg : 0 ≤ 16 * Int.fract x := mul_nonneg (by norm_num) hfract_nonneg
  have hmul_lt : 16 * Int.fract x < 16 := by nlinarith [hfract_lt]
  have hfloor_nonneg : 0 ≤ ⌊16 * Int.fract x⌋ :=
    Int.floor_nonneg.mpr hmul_nonneg
  have hfloor_lt : ⌊16 * Int.fract x⌋ < 16 :=
    (Int.floor_lt (a := 16 * Int.fract x) (z := 16)).mpr hmul_lt
  have hgap_eq :
      bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n = x - s := by
    have hsum := bbpSpigotIntGap_eq_head_add_tail n
    dsimp [x, s] at hsum ⊢
    have hfull := bbpSpigotIntFullSum_eq_head_add_tail n
    have htail := bbpSpigotIntTailSum_eq_zero n
    have hcast : (bbpSpigotIntFullSum n : ℝ) = s := by rw [hfull, htail, add_zero]
    linarith [hsum, hcast, bbpSeries_scaled_split n]
  have hfloor_gap :
      ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋ =
        ⌊16 * Int.fract x⌋ - 16 * δ := by
    calc
      ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋
          = ⌊16 * (x - s)⌋ := by rw [← hgap_eq]
      _ = ⌊16 * (Int.fract x - (δ : ℝ))⌋ := by rw [hgap]
      _ = ⌊16 * Int.fract x⌋ - 16 * δ := hfloor16
  have hfloor_toNat_lt : Int.toNat ⌊16 * Int.fract x⌋ < 16 :=
    (Int.toNat_lt_of_ne_zero (n := 16) (by decide : 16 ≠ 0)).mpr hfloor_lt
  calc
    (Int.toNat ⌊16 * Int.fract x⌋) % 16
        = bbpHexDigitOfGapFloor ⌊16 * Int.fract x⌋ := by
          rw [bbpHexDigitOfGapFloor_eq_toNat_mod hfloor_nonneg hfloor_lt,
            Nat.mod_eq_of_lt hfloor_toNat_lt]
    _ = bbpHexDigitOfGapFloor (⌊16 * Int.fract x⌋ - 16 * δ) := by
          dsimp [bbpHexDigitOfGapFloor]
          exact bbpHexDigitOfGapFloorZ_eq_of_emod_eq hmod.symm
    _ = bbpHexDigitOfGapFloor
          ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋ := by
          rw [← hfloor_gap]

/--
  **Upper-only digit link (legacy certificate):** same identity on `bbpIntFullSum` gaps.
-/
theorem bbpHexDigitSeries_eq_int_gap_floor_of_upper (n : Nat)
    (h : BBPIntSeriesBracketUpper n) :
    (Int.toNat ⌊16 * Int.fract ((16 : ℝ) ^ n * bbpSeries)⌋) % 16 =
      bbpHexDigitOfGapFloor
        ⌊16 * (bbpIntHeadGap n + bbpIntTailGap n)⌋ := by
  set x : ℝ := (16 : ℝ) ^ n * bbpSeries
  set s : ℝ := (bbpIntFullSum n : ℝ)
  set δ : ℤ := (bbpIntFullSum n : ℤ) - ⌊x⌋
  have hfloor := bbpIntFloor_le_fullSum_of_upper n h
  have hδ : 0 ≤ δ := sub_nonneg.mpr hfloor
  have hδ_cast : (δ : ℝ) = s - ↑(⌊x⌋) := by
    dsimp [δ, s]
    norm_cast
  have hgap :
      x - s = Int.fract x - (δ : ℝ) := by
    calc
      x - s = (Int.fract x + ↑(⌊x⌋)) - s := by rw [Int.fract_add_floor x]
      _ = Int.fract x - (s - ↑(⌊x⌋)) := by ring
      _ = Int.fract x - (δ : ℝ) := by rw [hδ_cast]
  have hfloor16 :
      ⌊16 * (Int.fract x - (δ : ℝ))⌋ = ⌊16 * Int.fract x⌋ - 16 * δ := by
    have hcast : (16 : ℝ) * (δ : ℝ) = ((16 * δ : ℤ) : ℝ) := by push_cast; ring
    have hmul :
        (16 : ℝ) * (Int.fract x - (δ : ℝ)) = 16 * Int.fract x - (16 : ℝ) * (δ : ℝ) := by ring
    rw [hmul, hcast, Int.floor_sub_intCast]
  have hmod :
      (⌊16 * Int.fract x⌋ - 16 * δ) % 16 = ⌊16 * Int.fract x⌋ % 16 := by
    have hzero : (16 * δ : ℤ) ≡ 0 [ZMOD 16] := (Int.dvd_mul_right 16 δ).modEq_zero_int
    simpa [sub_zero] using (Int.ModEq.refl ⌊16 * Int.fract x⌋).sub hzero |>.eq
  have hfract_nonneg : 0 ≤ Int.fract x := by
    simp only [Int.fract]
    linarith [Int.floor_le x]
  have hfract_lt : Int.fract x < 1 := by
    simp only [Int.fract]
    linarith [Int.lt_floor_add_one x]
  have hmul_nonneg : 0 ≤ 16 * Int.fract x := mul_nonneg (by norm_num) hfract_nonneg
  have hmul_lt : 16 * Int.fract x < 16 := by nlinarith [hfract_lt]
  have hfloor_nonneg : 0 ≤ ⌊16 * Int.fract x⌋ :=
    Int.floor_nonneg.mpr hmul_nonneg
  have hfloor_lt : ⌊16 * Int.fract x⌋ < 16 :=
    (Int.floor_lt (a := 16 * Int.fract x) (z := 16)).mpr hmul_lt
  have hgap_eq :
      bbpIntHeadGap n + bbpIntTailGap n = x - s := by
    have hsum := bbpIntGap_eq_head_add_tail n
    dsimp [x, s] at hsum ⊢
    linarith [hsum, bbpSeries_scaled_split n]
  have hfloor_gap :
      ⌊16 * (bbpIntHeadGap n + bbpIntTailGap n)⌋ =
        ⌊16 * Int.fract x⌋ - 16 * δ := by
    calc
      ⌊16 * (bbpIntHeadGap n + bbpIntTailGap n)⌋
          = ⌊16 * (x - s)⌋ := by rw [← hgap_eq]
      _ = ⌊16 * (Int.fract x - (δ : ℝ))⌋ := by rw [hgap]
      _ = ⌊16 * Int.fract x⌋ - 16 * δ := hfloor16
  have hfloor_toNat_lt : Int.toNat ⌊16 * Int.fract x⌋ < 16 :=
    (Int.toNat_lt_of_ne_zero (n := 16) (by decide : 16 ≠ 0)).mpr hfloor_lt
  calc
    (Int.toNat ⌊16 * Int.fract x⌋) % 16
        = bbpHexDigitOfGapFloor ⌊16 * Int.fract x⌋ := by
          rw [bbpHexDigitOfGapFloor_eq_toNat_mod hfloor_nonneg hfloor_lt,
            Nat.mod_eq_of_lt hfloor_toNat_lt]
    _ = bbpHexDigitOfGapFloor (⌊16 * Int.fract x⌋ - 16 * δ) := by
          dsimp [bbpHexDigitOfGapFloor]
          exact bbpHexDigitOfGapFloorZ_eq_of_emod_eq hmod.symm
    _ = bbpHexDigitOfGapFloor
          ⌊16 * (bbpIntHeadGap n + bbpIntTailGap n)⌋ := by
          rw [← hfloor_gap]

/--
  Weighted and legacy gap digits agree once both upper brackets hold.
-/
theorem bbpHexDigitOfGapFloor_spigot_eq_int_of_upper (n : Nat)
    (hSpigot : BBPSpigotIntSeriesBracketUpper n)
    (hInt : BBPIntSeriesBracketUpper n) :
    bbpHexDigitOfGapFloor
        ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋ =
      bbpHexDigitOfGapFloor
        ⌊16 * (bbpIntHeadGap n + bbpIntTailGap n)⌋ := by
  rw [← bbpHexDigitSeries_eq_spigot_gap_floor_of_upper n hSpigot,
    ← bbpHexDigitSeries_eq_int_gap_floor_of_upper n hInt]

/-- Scaled-series fractional hex digit (Tier-1 series-digit target). -/
noncomputable def bbpSeriesFractHexDigit (n : Nat) : Nat :=
  (Int.toNat ⌊16 * Int.fract ((16 : ℝ) ^ n * bbpSeries)⌋) % 16

private lemma bbpHexDigitOfGapFloor_eq_toNat_of_lt_sixteen {z : ℤ}
    (hz0 : 0 ≤ z) (hz1 : z < 16) :
    bbpHexDigitOfGapFloor z = Int.toNat z := by
  rw [bbpHexDigitOfGapFloor_eq_toNat_mod hz0 hz1]
  exact Nat.mod_eq_of_lt <|
    (Int.toNat_lt_of_ne_zero (n := 16) (by decide : 16 ≠ 0)).mpr hz1

private lemma bbpFractHexFloor_lt_sixteen (n : Nat) :
    ⌊16 * Int.fract ((16 : ℝ) ^ n * bbpSeries)⌋ < 16 := by
  set x := (16 : ℝ) ^ n * bbpSeries
  have hfract_lt : Int.fract x < 1 := by
    unfold Int.fract
    linarith [Int.lt_floor_add_one x]
  have hmul_lt : 16 * Int.fract x < 16 := by
    have hnonneg : 0 ≤ Int.fract x := by
      unfold Int.fract
      linarith [Int.floor_le x]
    nlinarith
  exact (Int.floor_lt (a := 16 * Int.fract x) (z := 16)).mpr hmul_lt

/--
  **Tier-1 computational target (cluster script `scripts/bbp_pbbp01_cluster.py`):**
  scaled series within `ε` of the legacy certificate sum. Witnesses feed this `Prop`;
  proving it for general `n` is analytic (not `native_decide` on `% 16` alone).
-/
def BBPIntFullSumApproxBound (n : Nat) (ε : ℝ) : Prop :=
  |(16 : ℝ) ^ n * bbpSeries - (bbpIntFullSum n : ℝ)| < ε

/--
  Weighted analogue: typically tighter (`bbpSpigotIntFullSum ≤ bbpIntFullSum` for `n ≤ 46`).
-/
def BBPSpigotIntFullSumApproxBound (n : Nat) (ε : ℝ) : Prop :=
  |(16 : ℝ) ^ n * bbpSeries - (bbpSpigotIntFullSum n : ℝ)| < ε

/-- FinitistUnified bridge scale `1/64` (hex-digit stability margin). -/
noncomputable def bbpCertBridgeScale : ℝ := 1 / 64

theorem bbpCertBridgeScale_pos : 0 < bbpCertBridgeScale := by
  unfold bbpCertBridgeScale
  norm_num

theorem bbpCertBridgeScale_nonneg : 0 ≤ bbpCertBridgeScale := by
  unfold bbpCertBridgeScale
  norm_num

noncomputable def bbpSeriesScaled (n : Nat) : ℝ := (16 : ℝ) ^ n * bbpSeries

def BBPFracStableAt (x ε : ℝ) : Prop :=
  ε ≤ Int.fract x ∧ Int.fract x + ε < 1

def BBPAwayFromHexBoundaries (x ε : ℝ) : Prop :=
  ∀ d : Nat, d ≤ 16 → ε ≤ |Int.fract x - (d : ℝ) / 16|

def BBPSeriesFracStableAt (n : Nat) (ε : ℝ) : Prop :=
  BBPFracStableAt (bbpSeriesScaled n) ε

def BBPSeriesAwayFromHexBoundaries (n : Nat) (ε : ℝ) : Prop :=
  BBPAwayFromHexBoundaries (bbpSeriesScaled n) ε

-- Method (A) targets: see FinitistUnified; cluster script checks candidates (analytic gate).

/--
  **Lower half shortcut (zero tail):** head bounded by `bbpScaledHead + bbpScaledTail`.
  Fails once head overshoots scaled head (typical for `n ≥ 1`); digit extraction uses
  `⌊16 · gap⌋ mod 16` with possibly negative gap, not `headSum % 16`.
-/
theorem bbpSpigotIntSeriesBracket_lower_of_head_le_scaled_plus_tail (n : Nat)
    (h : (bbpSpigotIntHeadSum n : ℝ) ≤ bbpScaledHead n + bbpScaledTail n) :
    BBPSpigotIntSeriesBracketLower n := by
  have hnonneg : 0 ≤ bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n := by
    rw [bbpSpigotIntTailGap_eq_scaledTail n, bbpSpigotIntHeadGap_eq n]
    linarith [h]
  exact (bbpSpigotIntSeriesBracketLower_iff_gap_nonneg n).mpr hnonneg

theorem bbpSpigotIntSeriesBracket_lower_of_head_le_scaled_plus_trunc (n : Nat)
    (h : (bbpSpigotIntHeadSum n : ℝ) ≤ bbpScaledHead n + bbpScaledTailTrunc n 50) :
    BBPSpigotIntSeriesBracketLower n :=
  bbpSpigotIntSeriesBracket_lower_of_head_le_scaled_plus_tail n <|
    h.trans (add_le_add_right (bbpScaledTailTrunc_le_bbpScaledTail n 50) (bbpScaledHead n))

theorem bbpSpigotIntSeriesBracket_of_gap (n : Nat) (h : BBPSpigotIntGapBracket n) :
    BBPSpigotIntSeriesBracket n :=
  (bbpSpigotIntGapBracket_iff_bracket n).mp h

theorem bbpSpigotIntSeriesBracket_of_head_tail_budget (n : Nat)
    (hLowerHead : BBPSpigotIntHeadCertBound n)
    (hTail : BBPSpigotIntTailCertBound n)
    (hHeadGap : BBPSpigotIntHeadGapBound n (1 - bbpSpigotIntTailGap n)) :
    BBPSpigotIntSeriesBracket n := by
  refine ⟨(bbpSpigotIntSeriesBracket_lower_of_bounds n hLowerHead hTail), ?_⟩
  exact bbpSpigotIntSeriesBracket_upper_of_head_budget n hTail hHeadGap

theorem bbpIntTailCertBound_of_le (n : Nat) (h : BBPIntTailCertBound n) :
    (bbpIntTailSum n : ℝ) ≤ bbpScaledTailTrunc n 50 := h

theorem bbpScaledTailTrunc_le_full_tail (n : Nat) :
    bbpScaledTailTrunc n 50 ≤ bbpScaledTail n :=
  bbpScaledTailTrunc_le_bbpScaledTail n 50

theorem bbpIntSeriesBracket_lower_of (n : Nat) (h : BBPIntSeriesBracket n) :
    BBPIntSeriesBracketLower n := h.1

theorem bbpIntSeriesBracket_upper_of (n : Nat) (h : BBPIntSeriesBracket n) :
    BBPIntSeriesBracketUpper n := h.2

/-- Gap decomposition for weighted spigot sums. -/
theorem bbpSeries_sub_spigotIntFullSum_eq_gap (n : Nat) :
    (16 : ℝ) ^ n * bbpSeries - bbpSpigotIntFullSum n =
      (bbpScaledHead n - (bbpSpigotIntHeadSum n : ℝ)) +
        (bbpScaledTail n - (bbpSpigotIntTailSum n : ℝ)) := by
  have hsplit := bbpSeries_scaled_split n
  have hfull := bbpSpigotIntFullSum_eq_head_add_tail n
  have hcast :
      (bbpSpigotIntFullSum n : ℝ) =
        (bbpSpigotIntHeadSum n : ℝ) + (bbpSpigotIntTailSum n : ℝ) := by
    rw [← Nat.cast_add, hfull]
  rw [hsplit, hcast]
  ring

theorem bbpIntTailGap_le_remainder_plus_trunc (n : Nat) (h : BBPIntTailCertBound n) :
    bbpScaledTail n - (bbpIntTailSum n : ℝ) ≤
      bbpScaledTailRemainder n +
        (bbpScaledTailTrunc n 50 - (bbpIntTailSum n : ℝ)) := by
  unfold bbpScaledTailRemainder
  linarith [h, bbpScaledTailTrunc_le_bbpScaledTail n 50]

theorem bbpIntTailGap_lt_one_of (n : Nat) (h : BBPIntTailCertBound n) :
    bbpScaledTail n - (bbpIntTailSum n : ℝ) < 1 := by
  have htrunc :
      0 ≤ (16 : ℝ) ^ n * bbpTailTrunc n 50 :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) n) (bbpTailTrunc_nonneg n 50)
  linarith [h, bbpScaledTail_lt_one n, htrunc, bbpScaledTailTrunc_le_bbpScaledTail n 50]

theorem bbpIntSeriesBracketUpper_iff_gap_lt_one (n : Nat) :
    BBPIntSeriesBracketUpper n ↔
      (bbpScaledHead n - (bbpIntHeadSum n : ℝ)) +
          (bbpScaledTail n - (bbpIntTailSum n : ℝ)) < 1 := by
  constructor
  · intro h
    unfold BBPIntSeriesBracketUpper at h
    have hfull := bbpIntFullSum_eq_head_add_tail n
    have hcast : (bbpIntFullSum n : ℝ) =
        (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
      rw [← Nat.cast_add, hfull]
    linarith [bbpSeries_scaled_split n, hcast, h]
  · intro h
    unfold BBPIntSeriesBracketUpper
    have hfull := bbpIntFullSum_eq_head_add_tail n
    have hcast : (bbpIntFullSum n : ℝ) =
        (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
      rw [← Nat.cast_add, hfull]
    linarith [bbpSeries_scaled_split n, hcast, h]

theorem bbpIntSeriesBracketLower_iff_gap_nonneg (n : Nat) :
    BBPIntSeriesBracketLower n ↔
      0 ≤ (bbpScaledHead n - (bbpIntHeadSum n : ℝ)) +
        (bbpScaledTail n - (bbpIntTailSum n : ℝ)) := by
  constructor
  · intro h
    unfold BBPIntSeriesBracketLower at h
    have hfull := bbpIntFullSum_eq_head_add_tail n
    have hcast : (bbpIntFullSum n : ℝ) =
        (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
      rw [← Nat.cast_add, hfull]
    linarith [bbpSeries_scaled_split n, hcast, h]
  · intro h
    unfold BBPIntSeriesBracketLower
    have hfull := bbpIntFullSum_eq_head_add_tail n
    have hcast : (bbpIntFullSum n : ℝ) =
        (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
      rw [← Nat.cast_add, hfull]
    linarith [bbpSeries_scaled_split n, hcast, h]

theorem bbpIntGapBracket_iff_bracket (n : Nat) :
    BBPIntGapBracket n ↔ BBPIntSeriesBracket n := by
  unfold BBPIntGapBracket
  rw [bbpIntSeriesBracket_iff_split n,
    bbpIntSeriesBracketLower_iff_gap_nonneg n,
    bbpIntSeriesBracketUpper_iff_gap_lt_one n]
  tauto

theorem bbpIntSeriesBracket_upper_of_tail_budget (n : Nat)
    (_hTail : BBPIntTailCertBound n)
    (hHead : bbpScaledHead n - (bbpIntHeadSum n : ℝ) <
        1 - (bbpScaledTail n - (bbpIntTailSum n : ℝ))) :
    BBPIntSeriesBracketUpper n := by
  rw [bbpIntSeriesBracketUpper_iff_gap_lt_one n]
  linarith [hHead]

theorem bbpIntSeriesBracket_upper_of_gap (n : Nat)
    (h : bbpIntHeadGap n + bbpIntTailGap n < 1) :
    BBPIntSeriesBracketUpper n :=
  (bbpIntSeriesBracketUpper_iff_gap_lt_one n).mpr h

/--
  Negative total gap forces the upper bracket (certificate overshoots the series).
-/
theorem bbpIntSeriesBracket_upper_of_neg_gap (n : Nat)
    (h : bbpIntHeadGap n + bbpIntTailGap n < 0) :
    BBPIntSeriesBracketUpper n :=
  bbpIntSeriesBracket_upper_of_gap n (lt_trans h (by norm_num : (0 : ℝ) < 1))

/--
  Integer certificate overshoots the analytic scaled split ⇒ upper bracket.
-/
theorem bbpIntSeriesBracket_upper_of_full_overshoot (n : Nat)
    (h : bbpScaledHead n + bbpScaledTail n < (bbpIntFullSum n : ℝ)) :
    BBPIntSeriesBracketUpper n := by
  unfold BBPIntSeriesBracketUpper
  have hsplit := bbpSeries_scaled_split n
  rw [hsplit]
  linarith

/--
  Weighted spigot upper bracket + legacy full-sum dominance ⇒ legacy upper bracket.
-/
theorem bbpIntSeriesBracket_upper_of_spigot_upper (n : Nat)
    (hSpigot : BBPSpigotIntSeriesBracketUpper n)
    (hle : bbpSpigotIntFullSum n ≤ bbpIntFullSum n) :
    BBPIntSeriesBracketUpper n := by
  unfold BBPIntSeriesBracketUpper BBPSpigotIntSeriesBracketUpper at *
  have hle' : (bbpSpigotIntFullSum n : ℝ) ≤ (bbpIntFullSum n : ℝ) := mod_cast hle
  linarith [hSpigot, hle']

theorem bbpIntSeriesBracket_of_gap (n : Nat) (h : BBPIntGapBracket n) :
    BBPIntSeriesBracket n :=
  (bbpIntGapBracket_iff_bracket n).mp h

theorem bbpIntSeriesBracket_of_head_tail_budget (n : Nat)
    (hLower : BBPIntSeriesBracketLower n)
    (hTail : BBPIntTailCertBound n)
    (hHead : bbpIntHeadGap n < 1 - bbpIntTailGap n) :
    BBPIntSeriesBracket n := by
  refine ⟨hLower, ?_⟩
  exact bbpIntSeriesBracket_upper_of_tail_budget n hTail (by
    simpa [bbpIntHeadGap_eq, bbpIntTailGap_eq] using hHead)

/-! ### Fractional extraction from bracket (algebraic link) -/

/-- Bracket identifies `⌊16^n · bbpSeries⌋` with the integer certificate sum. -/
theorem bbpIntFullSum_floor_eq_of_bracket (n : Nat) (h : BBPIntSeriesBracket n) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ = bbpIntFullSum n := by
  rcases h with ⟨hle, hlt⟩
  rw [Int.floor_eq_iff]
  constructor
  · exact_mod_cast hle
  · exact_mod_cast hlt

theorem bbpFracSeries_eq_sub_intSum_of_bracket (n : Nat) (h : BBPIntSeriesBracket n) :
    Int.fract ((16 : ℝ) ^ n * bbpSeries) =
      (16 : ℝ) ^ n * bbpSeries - bbpIntFullSum n := by
  rw [Int.fract, bbpIntFullSum_floor_eq_of_bracket n h]
  simp

/-- Gap between proved scaled split and integer certificate sums. -/
theorem bbpSeries_sub_intFullSum_eq_gap (n : Nat) :
    (16 : ℝ) ^ n * bbpSeries - bbpIntFullSum n =
      (bbpScaledHead n - (bbpIntHeadSum n : ℝ)) +
        (bbpScaledTail n - (bbpIntTailSum n : ℝ)) := by
  have hsplit := bbpSeries_scaled_split n
  have hfull := bbpIntFullSum_eq_head_add_tail n
  have hcast : (bbpIntFullSum n : ℝ) = (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
    rw [← Nat.cast_add, hfull]
  rw [hsplit, hcast]
  ring

theorem bbpSpigotIntFullSum_floor_eq_of_bracket (n : Nat) (h : BBPSpigotIntSeriesBracket n) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ = bbpSpigotIntFullSum n := by
  rcases h with ⟨hle, hlt⟩
  rw [Int.floor_eq_iff]
  constructor
  · exact_mod_cast hle
  · exact_mod_cast hlt

theorem bbpFracSeries_eq_sub_spigotIntSum_of_bracket (n : Nat) (h : BBPSpigotIntSeriesBracket n) :
    Int.fract ((16 : ℝ) ^ n * bbpSeries) =
      (16 : ℝ) ^ n * bbpSeries - bbpSpigotIntFullSum n := by
  rw [Int.fract, bbpSpigotIntFullSum_floor_eq_of_bracket n h]
  simp

/--
  Series fractional digit as `⌊16 · gap⌋ mod 16` on the weighted spigot block.
-/
theorem bbpHexDigitRealSeries_eq_spigot_gap_of (n : Nat) (h : BBPSpigotIntSeriesBracket n) :
    (Int.toNat ⌊16 * Int.fract ((16 : ℝ) ^ n * bbpSeries)⌋) % 16 =
      (Int.toNat ⌊16 *
        ((bbpScaledHead n - (bbpSpigotIntHeadSum n : ℝ)) +
          (bbpScaledTail n - (bbpSpigotIntTailSum n : ℝ)))⌋) % 16 := by
  have hfrac := bbpFracSeries_eq_sub_spigotIntSum_of_bracket n h
  have hgap := bbpSeries_sub_spigotIntFullSum_eq_gap n
  conv_lhs => arg 1; rw [hfrac]
  rw [hgap]

/--
  Upper-bracket digit link (gap may be negative); see `bbpHexDigitOfGapFloor`.
  Re-exported on `bbpHexDigitRealSeries` from `BBPSpigot`.
-/
theorem bbpHexDigitSeries_eq_spigot_gap_sum_of_upper (n : Nat)
    (h : BBPSpigotIntSeriesBracketUpper n) :
    (Int.toNat ⌊16 * Int.fract ((16 : ℝ) ^ n * bbpSeries)⌋) % 16 =
      bbpHexDigitOfGapFloor
        ⌊16 * (bbpSpigotIntHeadGap n + bbpSpigotIntTailGap n)⌋ :=
  bbpHexDigitSeries_eq_spigot_gap_floor_of_upper n h

/--
  Bracket + tail bound ⇒ tail gap is below `1` (proved analytic input).
-/
theorem bbpIntTailGap_lt_one_of_bracket (n : Nat) (_hbr : BBPIntSeriesBracket n)
    (hTail : BBPIntTailCertBound n) :
    bbpScaledTail n - (bbpIntTailSum n : ℝ) < 1 :=
  bbpIntTailGap_lt_one_of n hTail

theorem bbpIntHeadCorrect_of_bracket (n : Nat) (h : BBPIntSeriesBracket n) (_hHead : BBPIntHeadCorrect n) :
    (bbpIntHeadSum n : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries ∧
      (16 : ℝ) ^ n * bbpSeries < (bbpIntHeadSum n : ℝ) + 1 + (bbpIntTailSum n : ℝ) := by
  rcases h with ⟨hle, hlt⟩
  have hsplit := bbpIntFullSum_eq_head_add_tail n
  constructor
  · calc
      (bbpIntHeadSum n : ℝ) ≤ (bbpIntHeadSum n + bbpIntTailSum n : ℝ) := mod_cast Nat.le_add_right _ _
      _ = (bbpIntFullSum n : ℝ) := by rw [← Nat.cast_add, hsplit]
      _ ≤ _ := hle
  · have hfull : (bbpIntFullSum n : ℝ) = (bbpIntHeadSum n : ℝ) + (bbpIntTailSum n : ℝ) := by
      rw [← Nat.cast_add, hsplit]
    linarith [hlt, hfull]

/-! ### Tier-1 cluster witnesses: proved cert digit; gap-floor `hz` gate open -/

end FinitistProved