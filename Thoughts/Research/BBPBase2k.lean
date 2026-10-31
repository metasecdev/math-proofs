import Thoughts.Research.BBPMu658

/-!
# Round 6: base-`2^j` digits of π from the hex certificate (all positions)

`⌊2^N π⌋ = ⌊16^M π⌋ / 2^(4M−N)` with `M = ⌈N/4⌉`, so the unconditional hex certificate
(`bbp_digit_all_n_mu658`) also certifies every binary digit, hence every digit in base
`2, 4, 8, 16` (and any `2^j`: the base-`2^j` digit at position `n` is `⌊2^{jn} π⌋ mod 2^j`).
-/

namespace FinitistProved
open Real

theorem floor_two_pow_mul_pi (N : ℕ) :
    ⌊(2 : ℝ) ^ N * Real.pi⌋ =
      ⌊(16 : ℝ) ^ ((N + 3) / 4) * Real.pi⌋ / ((2 ^ (4 * ((N + 3) / 4) - N) : ℕ) : ℤ) := by
  set M := (N + 3) / 4
  set r := 4 * M - N
  have hr : N + r = 4 * M := by omega
  have h16 : (16 : ℝ) ^ M = 2 ^ N * 2 ^ r := by
    rw [← pow_add, hr, pow_mul]; norm_num
  have e : (2 : ℝ) ^ N * Real.pi = (16 : ℝ) ^ M * Real.pi / ((2 ^ r : ℕ) : ℝ) := by
    rw [h16]; push_cast; field_simp
  rw [e, Int.floor_div_natCast]

/-- **Every binary digit of π, unconditionally certified** (all `N`): with `M = ⌈N/4⌉`,
`⌊2^N π⌋ = bbpCertFloorAt M (657 M + ⌊log₁₆(M+1)⌋ + 1 + 430009) / 2^(4M−N)`. -/
theorem bbp_floor_two_pow_all_N (N : ℕ) :
    ⌊(2 : ℝ) ^ N * Real.pi⌋ =
      (bbpCertFloorAt ((N + 3) / 4)
          (657 * ((N + 3) / 4) + (Nat.log 16 ((N + 3) / 4 + 1) + 1) + 430009) : ℤ) /
        ((2 ^ (4 * ((N + 3) / 4) - N) : ℕ) : ℤ) := by
  rw [floor_two_pow_mul_pi, (bbp_digit_all_n_mu658 ((N + 3) / 4)).1]

/-- base-`2^j` digit at position `n`: `⌊(2^j)^n π⌋ mod 2^j`. -/
noncomputable def pow2DigitReal (j n : ℕ) : ℤ := ⌊(2 : ℝ) ^ (j * n) * Real.pi⌋ % 2 ^ j

theorem pow2Digit_certified (j n : ℕ) :
    pow2DigitReal j n =
      ((bbpCertFloorAt ((j * n + 3) / 4)
          (657 * ((j * n + 3) / 4) + (Nat.log 16 ((j * n + 3) / 4 + 1) + 1) + 430009) : ℤ) /
        ((2 ^ (4 * ((j * n + 3) / 4) - j * n) : ℕ) : ℤ)) % 2 ^ j := by
  unfold pow2DigitReal; rw [bbp_floor_two_pow_all_N]

end FinitistProved

#print axioms FinitistProved.floor_two_pow_mul_pi
#print axioms FinitistProved.bbp_floor_two_pow_all_N
#print axioms FinitistProved.pow2Digit_certified
