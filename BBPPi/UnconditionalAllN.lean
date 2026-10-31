import BBPPi.ConditionalAllN
import BBPPi.Mahler.PiMeasure

/-!
# All-`n` digit correctness from the μ = 851967 measure

**Unconditional all-`n` digit correctness**: plugging the explicit Mahler–Mignotte measure
`MahlerPiMeasure.pi_pow16_measure` (μ = 851967, C = 1/2^17170446) into the conditional theorem
`BBPPi.pi_pow16_measure_guard_all_n'`. Sorry-free; axioms propext, Classical.choice,
Quot.sound. The guard depth `gfun' μ C n = (μ-1)n + ⌊log₁₆(n+1)⌋ + 1 + ⌈(8μ+20)/C⌉` is explicit
but astronomically large (the constant term is about 2^17170469); it is a proof of existence of an
explicit computable bound, not a practical algorithm.
-/

namespace BBPPi

/-- the explicit irrationality exponent for π (at denominators 16^k) -/
abbrev piMu : ℕ := MahlerPiMeasure.muPi

/-- the explicit constant `C = 1 / 2^(A+1)` -/
noncomputable abbrev piC : ℝ := 1 / 2 ^ (MahlerPiMeasure.Aexp + 1)

theorem piC_pos : 0 < piC := by unfold piC; positivity

theorem piMu_pos : 1 ≤ piMu := by
  unfold piMu; rw [MahlerPiMeasure.muPi_def]; norm_num

/-- **Unconditional** explicit irrationality measure for π at `q = 16^n`. -/
theorem pi_pow16_measure_unconditional : PiPow16Measure piMu piC :=
  MahlerPiMeasure.pi_pow16_measure

/-- **Unconditional all-`n` digit correctness** (explicit guard depth `gfun' piMu piC n`). -/
theorem bbp_guard_all_n_unconditional :
    ∀ n : ℕ, BBPGuardAgreesAt n (gfun' piMu piC n) :=
  pi_pow16_measure_guard_all_n' piC_pos pi_pow16_measure_unconditional piMu_pos

/-- digit form: for every `n`, the guarded certificate at depth `gfun' piMu piC n` computes
`⌊16^n π⌋` and the `n`-th hex digit of π. -/
theorem bbp_digit_all_n_unconditional (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n (gfun' piMu piC n) : ℤ) ∧
      bbpCertDigitAt n (gfun' piMu piC n) = bbpHexDigitReal n :=
  ⟨(bbp_guard_all_n_unconditional n).floor_pi, (bbp_guard_all_n_unconditional n).digit_pi⟩

end BBPPi
