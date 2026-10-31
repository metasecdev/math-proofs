/-
  Finite BBP-series algebra (fully proved, no axioms).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinitistProved

open Real Nat Finset

noncomputable def bbpCoeff (k : Nat) : ℝ :=
  (4 : ℝ) / (8 * k + 1)
    - (2 : ℝ) / (8 * k + 4)
    - (1 : ℝ) / (8 * k + 5)
    - (1 : ℝ) / (8 * k + 6)

noncomputable def bbpSummand (k : Nat) : ℝ := bbpCoeff k / ((16 : ℝ) ^ k)

noncomputable def bbpHead (n : Nat) : ℝ := ∑ k ∈ Finset.range (n + 1), bbpSummand k

noncomputable def bbpTailTrunc (n M : Nat) : ℝ := ∑ j ∈ Finset.range M, bbpSummand (n + 1 + j)

noncomputable def bbpScaledHead (n : Nat) : ℝ := ((16 : ℝ) ^ n) * bbpHead n

noncomputable def bbpScaledTailTrunc (n M : Nat) : ℝ := ((16 : ℝ) ^ n) * bbpTailTrunc n M

theorem bbpHead_zero : bbpHead 0 = bbpSummand 0 := by simp [bbpHead]

theorem bbpHead_succ (n : Nat) :
    bbpHead (n + 1) = bbpHead n + bbpSummand (n + 1) := by
  simp [bbpHead, Finset.sum_range_succ]

theorem bbpTailTrunc_zero (n : Nat) : bbpTailTrunc n 0 = 0 := by simp [bbpTailTrunc]

theorem bbpTailTrunc_succ (n M : Nat) :
    bbpTailTrunc n (M + 1) = bbpTailTrunc n M + bbpSummand (n + 1 + M) := by
  simp [bbpTailTrunc, Finset.sum_range_succ]

theorem bbpScaledHead_plus_tailTrunc (n M : Nat) :
    bbpScaledHead n + bbpScaledTailTrunc n M
      = ((16 : ℝ) ^ n) * (bbpHead n + bbpTailTrunc n M) := by
  simp [bbpScaledHead, bbpScaledTailTrunc, mul_add]

end FinitistProved