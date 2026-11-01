import Thoughts.Research.BBPGuardLog
import Thoughts.Research.MahlerSharp7

/-!
# Round 7: unconditional all-`n` P-BBP-01 with `μ = 570`

Plugs `MahlerSharp7.pi_pow16_measure7` (`μ = 570`, `C = 2^-9093942`) into the Round-5 logarithmic
guard (`BBPGuardLog`).  Guard depth: `569·n + ⌊log₁₆(n+1)⌋ + 1 + 2273495`
(Round 6: `657·n + ⌊log₁₆(n+1)⌋ + 1 + 430009`).
Superseded by `BBPMu570b.lean` (Round 7b): additive constant `1795710`, simple form
`570·n + 1795711`.
-/

namespace FinitistProved
open Real

/-- Round-7 constant `C = 2^-9093942`. -/
noncomputable abbrev piC7 : ℝ := 1 / 2 ^ (9093941 + 1)

theorem piC7_pos : 0 < piC7 := by unfold piC7; positivity

theorem pi_pow16_measure_mu570 : PiPow16Measure 570 piC7 := MahlerSharp7.pi_pow16_measure7

private lemma natLog16_mul_pow7 (c N e : ℕ) (hc1 : 16 ^ e ≤ c) (hc2 : c < 16 ^ (e + 1)) :
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

theorem guardLogL_570 : guardLogL 570 piC7 = 2273489 := by
  unfold guardLogL piC7
  have hceil : ⌈(8 * ((570 : ℕ) : ℝ) + 20) / (1 / 2 ^ (9093941 + 1))⌉₊ = 18320 * 16 ^ 2273485 := by
    have e : (8 * ((570 : ℕ) : ℝ) + 20) / (1 / 2 ^ (9093941 + 1)) =
        ((18320 * 16 ^ 2273485 : ℕ) : ℝ) := by
      rw [div_div_eq_mul_div, div_one]
      have h2 : (2 : ℝ) ^ (9093941 + 1) = 4 * 16 ^ 2273485 := by
        rw [show 9093941 + 1 = 2 + 4 * 2273485 by norm_num, pow_add, pow_mul]; norm_num
      rw [h2]; push_cast; ring
    rw [e, Nat.ceil_natCast]
  rw [hceil, natLog16_mul_pow7 18320 2273485 3 (by norm_num) (by norm_num)]

theorem guardLogConst_570 : guardLogConst 570 piC7 = 2273495 := by
  unfold guardLogConst
  rw [guardLogL_570]
  have : Nat.log 16 (2 * 2273489) = 5 := by
    rw [Nat.log_eq_iff (Or.inl (by norm_num))]; norm_num
  rw [this]

/-- **Unconditional all-`n` P-BBP-01, `μ = 570`**: for every `n`, the guard agrees at depth
`569·n + ⌊log₁₆(n+1)⌋ + 1 + 2273495`. -/
theorem bbp_guard_all_n_mu570 (n : ℕ) :
    BBPGuardAgreesAt n (569 * n + (Nat.log 16 (n + 1) + 1) + 2273495) := by
  have h := pi_pow16_measure_guard_all_n'' piC7_pos pi_pow16_measure_mu570 (by norm_num) n
  unfold gfun'' at h
  rwa [show 570 - 1 = 569 by norm_num, guardLogConst_570] at h

theorem bbp_digit_all_n_mu570 (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ =
        (bbpCertFloorAt n (569 * n + (Nat.log 16 (n + 1) + 1) + 2273495) : ℤ) ∧
      bbpCertDigitAt n (569 * n + (Nat.log 16 (n + 1) + 1) + 2273495) = bbpHexDigitReal n :=
  ⟨(bbp_guard_all_n_mu570 n).floor_pi, (bbp_guard_all_n_mu570 n).digit_pi⟩

end FinitistProved

#print axioms FinitistProved.pi_pow16_measure_mu570
#print axioms FinitistProved.guardLogConst_570
#print axioms FinitistProved.bbp_guard_all_n_mu570
#print axioms FinitistProved.bbp_digit_all_n_mu570
