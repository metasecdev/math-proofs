import BBPPi.Mahler.Sharp570
import BBPPi.GuardLog

/-!
# All-`n` digit correctness with guard depth `570·n + 1795711`

Plugs the irrationality measure `MahlerSharp7b.pi_pow16_irrationality_measure`
(`μ = 570`, `C = 2^-7182802`, file `BBPPi.Mahler.Sharp570`) into the logarithmic guard of
`BBPPi.GuardLog`.

## Main results

* `guardAgreesAt_guard570`: the guarded bracket collapses at depth
  `569·n + ⌊log₁₆(n+1)⌋ + 1 + 1795710`, for every `n`.
* `floor_digit_eq_guard570`: at that depth the certificate computes `⌊16^n·π⌋` and the true
  `n`-th hex digit.
* `guardAgreesAt_of_guard570_le`: agreement at every depth at or above that one.
* `bbpDigit_eq_of_guard_ge`: simple form, every depth `g ≥ 570·n + 1795711` is correct.

The old names (`bbp_digit_all_n_mu570b`, …) are deprecated aliases (`BBPPi.Deprecated`).
-/

namespace BBPPi
open Real

/-- The μ = 570 constant `C = 2^-7182802`. -/
noncomputable abbrev piC7b : ℝ := 1 / 2 ^ (7182801 + 1)

theorem piC7b_pos : 0 < piC7b := by unfold piC7b; positivity

theorem pi_pow16_measure_mu570b : PiPow16Measure 570 piC7b := MahlerSharp7b.pi_pow16_irrationality_measure

private lemma natLog16_mul_pow7b (c N e : ℕ) (hc1 : 16 ^ e ≤ c) (hc2 : c < 16 ^ (e + 1)) :
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

theorem guardLogL_570b : guardLogL 570 piC7b = 1795704 := by
  unfold guardLogL piC7b
  have hceil : ⌈(8 * ((570 : ℕ) : ℝ) + 20) / (1 / 2 ^ (7182801 + 1))⌉₊ = 18320 * 16 ^ 1795700 := by
    have e : (8 * ((570 : ℕ) : ℝ) + 20) / (1 / 2 ^ (7182801 + 1)) =
        ((18320 * 16 ^ 1795700 : ℕ) : ℝ) := by
      rw [div_div_eq_mul_div, div_one]
      have h2 : (2 : ℝ) ^ (7182801 + 1) = 4 * 16 ^ 1795700 := by
        rw [show 7182801 + 1 = 2 + 4 * 1795700 by norm_num, pow_add, pow_mul]; norm_num
      rw [h2]; push_cast; ring
    rw [e, Nat.ceil_natCast]
  rw [hceil, natLog16_mul_pow7b 18320 1795700 3 (by norm_num) (by norm_num)]

theorem guardLogConst_570b : guardLogConst 570 piC7b = 1795710 := by
  unfold guardLogConst
  rw [guardLogL_570b]
  have : Nat.log 16 (2 * 1795704) = 5 := by
    rw [Nat.log_eq_iff (Or.inl (by norm_num))]; norm_num
  rw [this]

/-- **All-`n` guard agreement (μ = 570)**: for every `n`, the guard agrees at depth
`569·n + ⌊log₁₆(n+1)⌋ + 1 + 1795710`. -/
theorem guardAgreesAt_guard570 (n : ℕ) :
    BBPGuardAgreesAt n (569 * n + (Nat.log 16 (n + 1) + 1) + 1795710) := by
  have h := pi_pow16_measure_guard_all_n'' piC7b_pos pi_pow16_measure_mu570b (by norm_num) n
  unfold gfun'' at h
  rwa [show 570 - 1 = 569 by norm_num, guardLogConst_570b] at h

/-- At the μ = 570 guard depth the certificate gives `⌊16^n·π⌋` and the `n`-th hex digit. -/
theorem floor_digit_eq_guard570 (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ =
        (bbpCertFloorAt n (569 * n + (Nat.log 16 (n + 1) + 1) + 1795710) : ℤ) ∧
      bbpCertDigitAt n (569 * n + (Nat.log 16 (n + 1) + 1) + 1795710) = bbpHexDigitReal n :=
  ⟨(guardAgreesAt_guard570 n).floor_pi, (guardAgreesAt_guard570 n).digit_pi⟩

/-- Every depth at or above the μ = 570 guard depth agrees (monotonicity). -/
theorem guardAgreesAt_of_guard570_le (n g : ℕ)
    (hg : 569 * n + (Nat.log 16 (n + 1) + 1) + 1795710 ≤ g) : BBPGuardAgreesAt n g := by
  have hspec := guardLogConst_spec (μ := 570) piC7b_pos
  rw [guardLogConst_570b] at hspec
  obtain ⟨j, hj, rfl⟩ : ∃ j, 1795710 ≤ j ∧ g = 569 * n + (Nat.log 16 (n + 1) + 1) + j :=
    ⟨g - (569 * n + (Nat.log 16 (n + 1) + 1)), by omega, by omega⟩
  have h := guard_agrees_of_const (μ := 570) (by norm_num) pi_pow16_measure_mu570b j (by omega)
    (guardConst_hyp_mono (by positivity) hspec j hj) n
  simpa using h

/-- `⌊log₁₆(n+1)⌋ ≤ n`. -/
theorem log16_succ_le (n : ℕ) : Nat.log 16 (n + 1) ≤ n := by
  have h3 : 16 ^ (Nat.log 16 (n + 1)) ≤ n + 1 := Nat.pow_log_le_self 16 (by omega)
  have : Nat.log 16 (n + 1) < 16 ^ (Nat.log 16 (n + 1)) := Nat.lt_pow_self (by norm_num)
  omega

/-- **Digit correctness at every large enough depth (μ = 570, simple form)**: for every `n` and every
`g ≥ 570·n + 1795711`, the depth-`g` certificate gives π's floor and `n`-th hex digit. -/
theorem bbpDigit_eq_of_guard_ge (n g : ℕ) (hg : 570 * n + 1795711 ≤ g) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n g : ℤ) ∧
      bbpCertDigitAt n g = bbpHexDigitReal n := by
  have h := guardAgreesAt_of_guard570_le n g (by have := log16_succ_le n; omega)
  exact ⟨h.floor_pi, h.digit_pi⟩

/-- The digit at depth `570·n + 1795711` is the `n`-th hex digit of π. -/
theorem bbpDigit_eq_at_guard570_simple (n : ℕ) :
    bbpCertDigitAt n (570 * n + 1795711) = bbpHexDigitReal n :=
  (bbpDigit_eq_of_guard_ge n _ le_rfl).2

end BBPPi
