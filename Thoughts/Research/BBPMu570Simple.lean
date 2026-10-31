import Thoughts.Research.BBPMu570

/-!
# Round 7, clean corollary: a linear guard bound with one constant

For every `n` the exact Round-7 guard `569·n + ⌊log₁₆(n+1)⌋ + 1 + 2273495` is at most
`570·n + 2273496`, so P-BBP-01 holds with a certificate depth bounded linearly in `n` with simple
constants. (The guard is not shown to be monotone in the depth, so the exact depth is kept as
the witness; the corollary bounds it.)
-/

namespace FinitistProved

theorem guard570_le (n : ℕ) :
    569 * n + (Nat.log 16 (n + 1) + 1) + 2273495 ≤ 570 * n + 2273496 := by
  have : Nat.log 16 (n + 1) ≤ n := by
    have h := Nat.log_lt_self 16 (show n + 1 ≠ 0 by omega)
    omega
  omega

/-- **P-BBP-01, simple form**: for every `n` there is a certificate depth `g ≤ 570·n + 2273496`
at which the BBP guard agrees and the certified hex digit is the true `n`-th digit of `π`. -/
theorem bbp_digit_all_n_simple (n : ℕ) :
    ∃ g ≤ 570 * n + 2273496,
      ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
        bbpCertDigitAt n g = bbpHexDigitReal n :=
  ⟨_, guard570_le n, bbp_digit_all_n_mu570 n⟩

end FinitistProved

#print axioms FinitistProved.bbp_digit_all_n_simple
