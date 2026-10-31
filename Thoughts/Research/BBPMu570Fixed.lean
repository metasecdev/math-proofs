import Thoughts.Research.BBPMu570Simple

/-!
# Round 7: fixed-depth P-BBP-01 (guard-depth monotonicity)

`guard_agrees_of_const` accepts *any* additive constant `j ≥ 1` with `(8μ+20)(j+1) ≤ C·16^j`.
That hypothesis is upward closed in `j` (the left side grows by a factor `≤ 2`, the right side by
`16`), so every depth `g ≥ 569·n + ⌊log₁₆(n+1)⌋ + 1 + 2273495` is certified, not just one depth.
This is re-derived from the irrationality measure directly, not from the `n`/`g` shift lemma.
-/

namespace FinitistProved

/-- The guard-constant hypothesis is upward closed in `j`. -/
theorem guardConst_hyp_mono {A C : ℝ} (hA : 0 ≤ A) {j : ℕ}
    (h : A * ((j : ℝ) + 1) ≤ C * (16 : ℝ) ^ j) :
    ∀ k, j ≤ k → A * ((k : ℝ) + 1) ≤ C * (16 : ℝ) ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : A * (((k + 1 : ℕ) : ℝ) + 1) ≤ 16 * (A * ((k : ℝ) + 1)) := by
      push_cast; nlinarith
    calc A * (((k + 1 : ℕ) : ℝ) + 1) ≤ 16 * (A * ((k : ℝ) + 1)) := h1
      _ ≤ 16 * (C * (16 : ℝ) ^ k) := by linarith
      _ = C * (16 : ℝ) ^ (k + 1) := by ring

/-- **Guard-depth monotonicity (μ = 570)**: the guard agrees at every depth `g` at or above the
exact Round-7 guard `569·n + ⌊log₁₆(n+1)⌋ + 1 + 2273495`. -/
theorem bbp_guard_mu570_of_ge (n g : ℕ)
    (hg : 569 * n + (Nat.log 16 (n + 1) + 1) + 2273495 ≤ g) : BBPGuardAgreesAt n g := by
  have hspec := guardLogConst_spec (μ := 570) piC7_pos
  rw [guardLogConst_570] at hspec
  obtain ⟨j, hj, rfl⟩ : ∃ j, 2273495 ≤ j ∧ g = 569 * n + (Nat.log 16 (n + 1) + 1) + j :=
    ⟨g - (569 * n + (Nat.log 16 (n + 1) + 1)), by omega, by omega⟩
  have h := guard_agrees_of_const (μ := 570) (by norm_num) pi_pow16_measure_mu570 j (by omega)
    (guardConst_hyp_mono (by positivity) hspec j hj) n
  simpa using h

/-- **P-BBP-01, fixed depth (exact guard)**: every depth at or above the exact guard gives π's
floor and hex digit. -/
theorem bbp_digit_all_n_mu570_of_ge (n g : ℕ)
    (hg : 569 * n + (Nat.log 16 (n + 1) + 1) + 2273495 ≤ g) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
      bbpCertDigitAt n g = bbpHexDigitReal n :=
  ⟨(bbp_guard_mu570_of_ge n g hg).floor_pi, (bbp_guard_mu570_of_ge n g hg).digit_pi⟩

/-- **P-BBP-01, fixed depth (simple form)**: for every `n` and every `g ≥ 570·n + 2273496`, the
depth-`g` certificate gives π's floor and `n`-th hex digit. -/
theorem bbp_digit_all_n_fixed (n g : ℕ) (hg : 570 * n + 2273496 ≤ g) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
      bbpCertDigitAt n g = bbpHexDigitReal n :=
  bbp_digit_all_n_mu570_of_ge n g (le_trans (guard570_le n) hg)

/-- Concrete depth function: `G(n) = 570·n + 2273496` works for every `n`. -/
theorem bbp_digit_all_n_at_G (n : ℕ) :
    bbpCertDigitAt n (570 * n + 2273496) = bbpHexDigitReal n :=
  (bbp_digit_all_n_fixed n _ le_rfl).2

end FinitistProved

#print axioms FinitistProved.guardConst_hyp_mono
#print axioms FinitistProved.bbp_guard_mu570_of_ge
#print axioms FinitistProved.bbp_digit_all_n_mu570_of_ge
#print axioms FinitistProved.bbp_digit_all_n_fixed
#print axioms FinitistProved.bbp_digit_all_n_at_G
