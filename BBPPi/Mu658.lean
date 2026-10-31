import BBPPi.GuardLog
import BBPPi.Mahler.Sharp

/-!
# All-`n` digit correctness with `μ = 658`

Plugs `MahlerSharp.pi_pow16_measure6` (`μ = 658`, `C = 2^-1720001`) into the logarithmic
guard of `BBPPi.GuardLog`. Guard depth: `657·n + ⌊log₁₆(n+1)⌋ + 1 + 430009`.
Superseded numerically by `BBPPi.Mu570` but kept because the paper cites it.

## Main results

* `guardAgreesAt_guard658`, `floor_digit_eq_guard658`.
-/

namespace BBPPi
open Real

/-- the μ = 658 bound constant `C = 2^-1720001`. -/
noncomputable abbrev piC6 : ℝ := 1 / 2 ^ (1720000 + 1)

theorem piC6_pos : 0 < piC6 := by unfold piC6; positivity

theorem pi_pow16_measure_mu658 : PiPow16Measure 658 piC6 := MahlerSharp.pi_pow16_measure6

private lemma natLog16_mul_pow6 (c N e : ℕ) (hc1 : 16 ^ e ≤ c) (hc2 : c < 16 ^ (e + 1)) :
    Nat.log 16 (c * 16 ^ N) = N + e := by
  have hc0 : c ≠ 0 := by
    have : 0 < 16 ^ e := by positivity
    omega
  have hN : c * 16 ^ N ≠ 0 := Nat.mul_ne_zero hc0 (by positivity)
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hN⟩)]
  constructor
  · rw [pow_add, mul_comm (16 ^ N)]; exact Nat.mul_le_mul_right _ hc1
  · rw [show N + e + 1 = N + (e + 1) by omega, pow_add, mul_comm (16 ^ N)]
    exact Nat.mul_lt_mul_of_pos_right hc2 (by positivity)

theorem guardLogL_658 : guardLogL 658 piC6 = 430004 := by
  unfold guardLogL piC6
  have hceil : ⌈(8 * ((658 : ℕ) : ℝ) + 20) / (1 / 2 ^ (1720000 + 1))⌉₊ = 10568 * 16 ^ 430000 := by
    have e : (8 * ((658 : ℕ) : ℝ) + 20) / (1 / 2 ^ (1720000 + 1)) =
        ((10568 * 16 ^ 430000 : ℕ) : ℝ) := by
      rw [div_div_eq_mul_div, div_one]
      have h2 : (2 : ℝ) ^ (1720000 + 1) = 2 * 16 ^ 430000 := by
        rw [show 1720000 + 1 = 1 + 4 * 430000 by norm_num, pow_add, pow_mul]; norm_num
      rw [h2]; push_cast; ring
    rw [e, Nat.ceil_natCast]
  rw [hceil, natLog16_mul_pow6 10568 430000 3 (by norm_num) (by norm_num)]

theorem guardLogConst_658 : guardLogConst 658 piC6 = 430009 := by
  unfold guardLogConst
  rw [guardLogL_658]
  have : Nat.log 16 (2 * 430004) = 4 := by
    rw [Nat.log_eq_iff (Or.inl (by norm_num))]; norm_num
  rw [this]

/-- **Unconditional all-`n` digit correctness, `μ = 658`**: for every `n`, the guard agrees at depth
`657·n + ⌊log₁₆(n+1)⌋ + 1 + 430009`. -/
theorem guardAgreesAt_guard658 (n : ℕ) :
    BBPGuardAgreesAt n (657 * n + (Nat.log 16 (n + 1) + 1) + 430009) := by
  have h := pi_pow16_measure_guard_all_n'' piC6_pos pi_pow16_measure_mu658 (by norm_num) n
  unfold gfun'' at h
  rwa [show 658 - 1 = 657 by norm_num, guardLogConst_658] at h

theorem floor_digit_eq_guard658 (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ =
        (bbpCertFloorAt n (657 * n + (Nat.log 16 (n + 1) + 1) + 430009) : ℤ) ∧
      bbpCertDigitAt n (657 * n + (Nat.log 16 (n + 1) + 1) + 430009) = bbpHexDigitReal n :=
  ⟨(guardAgreesAt_guard658 n).floor_pi, (guardAgreesAt_guard658 n).digit_pi⟩

end BBPPi
