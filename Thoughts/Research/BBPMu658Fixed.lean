import Thoughts.Research.BBPMu658
import Thoughts.Research.BBPMu570Fixed

/-!
# Fixed-depth P-BBP-01 for `μ = 658` (guard-depth monotonicity)

Same argument as `BBPMu570Fixed`: the guard-constant hypothesis of `guard_agrees_of_const` is
upward closed in `j` (`guardConst_hyp_mono`), so every depth at or above the Round-6 guard
`657·n + ⌊log₁₆(n+1)⌋ + 1 + 430009` is certified.
-/

namespace FinitistProved

theorem bbp_guard_mu658_of_ge (n g : ℕ)
    (hg : 657 * n + (Nat.log 16 (n + 1) + 1) + 430009 ≤ g) : BBPGuardAgreesAt n g := by
  have hspec := guardLogConst_spec (μ := 658) piC6_pos
  rw [guardLogConst_658] at hspec
  obtain ⟨j, hj, rfl⟩ : ∃ j, 430009 ≤ j ∧ g = 657 * n + (Nat.log 16 (n + 1) + 1) + j :=
    ⟨g - (657 * n + (Nat.log 16 (n + 1) + 1)), by omega, by omega⟩
  have h := guard_agrees_of_const (μ := 658) (by norm_num) pi_pow16_measure_mu658 j (by omega)
    (guardConst_hyp_mono (by positivity) hspec j hj) n
  simpa using h

theorem bbp_digit_all_n_mu658_of_ge (n g : ℕ)
    (hg : 657 * n + (Nat.log 16 (n + 1) + 1) + 430009 ≤ g) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
      bbpCertDigitAt n g = bbpHexDigitReal n :=
  ⟨(bbp_guard_mu658_of_ge n g hg).floor_pi, (bbp_guard_mu658_of_ge n g hg).digit_pi⟩

theorem guard658_le (n : ℕ) :
    657 * n + (Nat.log 16 (n + 1) + 1) + 430009 ≤ 658 * n + 430010 := by
  have : Nat.log 16 (n + 1) ≤ n := by
    have h := Nat.log_lt_self 16 (show n + 1 ≠ 0 by omega)
    omega
  omega

/-- **P-BBP-01, fixed depth, μ = 658 (simple form)**: every `g ≥ 658·n + 430010` works. -/
theorem bbp_digit_all_n_fixed658 (n g : ℕ) (hg : 658 * n + 430010 ≤ g) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
      bbpCertDigitAt n g = bbpHexDigitReal n :=
  bbp_digit_all_n_mu658_of_ge n g (le_trans (guard658_le n) hg)

end FinitistProved

#print axioms FinitistProved.bbp_guard_mu658_of_ge
#print axioms FinitistProved.bbp_digit_all_n_mu658_of_ge
#print axioms FinitistProved.bbp_digit_all_n_fixed658
