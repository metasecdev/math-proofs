import Thoughts.Research.BBPBase2k
import Thoughts.Research.BBPMu658Fixed

/-!
# Fixed-depth base-`2^k` P-BBP-01

Every guard depth at or above the Round-6 depth used in `BBPBase2k` (with `M = ⌈N/4⌉`) certifies
`⌊2^N π⌋` and the base-`2^j` digits; a simple closed form is `g ≥ 165·N + 430504`.
-/

namespace FinitistProved

theorem bbp_floor_two_pow_of_ge (N g : ℕ)
    (hg : 657 * ((N + 3) / 4) + (Nat.log 16 ((N + 3) / 4 + 1) + 1) + 430009 ≤ g) :
    ⌊(2 : ℝ) ^ N * Real.pi⌋ =
      (bbpCertFloorAt ((N + 3) / 4) g : ℤ) / ((2 ^ (4 * ((N + 3) / 4) - N) : ℕ) : ℤ) := by
  rw [floor_two_pow_mul_pi, (bbp_digit_all_n_mu658_of_ge ((N + 3) / 4) g hg).1]

theorem bbp_floor_two_pow_fixed (N g : ℕ) (hg : 165 * N + 430504 ≤ g) :
    ⌊(2 : ℝ) ^ N * Real.pi⌋ =
      (bbpCertFloorAt ((N + 3) / 4) g : ℤ) / ((2 ^ (4 * ((N + 3) / 4) - N) : ℕ) : ℤ) := by
  apply bbp_floor_two_pow_of_ge
  have := guard658_le ((N + 3) / 4)
  omega

theorem pow2Digit_of_ge (j n g : ℕ)
    (hg : 657 * ((j * n + 3) / 4) + (Nat.log 16 ((j * n + 3) / 4 + 1) + 1) + 430009 ≤ g) :
    pow2DigitReal j n =
      ((bbpCertFloorAt ((j * n + 3) / 4) g : ℤ) /
        ((2 ^ (4 * ((j * n + 3) / 4) - j * n) : ℕ) : ℤ)) % 2 ^ j := by
  unfold pow2DigitReal; rw [bbp_floor_two_pow_of_ge _ g hg]

theorem pow2Digit_fixed (j n g : ℕ) (hg : 165 * (j * n) + 430504 ≤ g) :
    pow2DigitReal j n =
      ((bbpCertFloorAt ((j * n + 3) / 4) g : ℤ) /
        ((2 ^ (4 * ((j * n + 3) / 4) - j * n) : ℕ) : ℤ)) % 2 ^ j := by
  unfold pow2DigitReal; rw [bbp_floor_two_pow_fixed _ g hg]

end FinitistProved

#print axioms FinitistProved.bbp_floor_two_pow_of_ge
#print axioms FinitistProved.bbp_floor_two_pow_fixed
#print axioms FinitistProved.pow2Digit_of_ge
#print axioms FinitistProved.pow2Digit_fixed
