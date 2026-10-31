import BBPPiCerts.CapRefutation

/-!
# Capped digit correctness: widest structural failure window (2026-10-29)

`not_BBPSpigotDigitCorrect_window` refutes the capped (cap 68) certificate on `[2^272, 2^273]`.
The same structural argument (`lo_digit_ne_of_window` at `g = 68`) needs only
`16^68 ≤ n + 71` and `5(n + 69) + 3 ≤ 14·16^68`, so the window is
`[2^272 − 71, ⌊(14·2^272 − 348)/5⌋]`.  Below `2^272 − 71` the bias `K+2` of the guarded lower end
is smaller than `16^68`, and whether the capped digit is wrong depends on the actual hex digits of
π after position `n` (a run of ≈ 68 − log₁₆ n zeros); no structural argument decides it.

`not_BBPSpigotDigitCorrect_first` gives the smallest `n` this argument reaches: `2^272 − 71`.
-/

namespace BBPPi

/-- **Widened refutation window**: for every `n` with `2^272 − 71 ≤ n` and `5n + 348 ≤ 14·2^272`,
the capped digit is wrong. -/
theorem not_BBPSpigotDigitCorrect_window' (n : ℕ) (hlo : 2 ^ 272 - 71 ≤ n)
    (hhi : 5 * n + 348 ≤ 14 * 2 ^ 272) : ¬ BBPSpigotDigitCorrect n := by
  have h253 : 2 ^ 253 ≤ n := by
    have : 2 ^ 253 + 71 ≤ 2 ^ 272 := by decide +kernel
    omega
  have hG : bbpCertGuard n = 68 := bbpCertGuard_eq_68 n h253
  have h1 : 1 ≤ n := le_trans Nat.one_le_two_pow h253
  have h16 : (16 : ℕ) ^ 68 = 2 ^ 272 := by decide +kernel
  have h71 : 71 ≤ 2 ^ 272 := by decide +kernel
  unfold BBPSpigotDigitCorrect
  show bbpHexDigitCert n ≠ _
  unfold bbpHexDigitCert bbpCertFloor
  rw [hG]
  exact lo_digit_ne_of_window n 68 h1 (by omega) (by omega)

/-- The smallest `n` reached by the structural refutation: `n = 2^272 − 71` is a counterexample. -/
theorem not_BBPSpigotDigitCorrect_first : ¬ BBPSpigotDigitCorrect (2 ^ 272 - 71) :=
  not_BBPSpigotDigitCorrect_window' _ le_rfl (by decide +kernel)

/-- The structural window condition `16^68 ≤ n + 71` is exactly `n ≥ 2^272 − 71`: the argument
cannot reach any smaller `n`. -/
theorem cap_window_condition_sharp (n : ℕ) : 16 ^ 68 ≤ n + 68 + 1 + 2 ↔ 2 ^ 272 - 71 ≤ n := by
  have h16 : (16 : ℕ) ^ 68 = 2 ^ 272 := by decide +kernel
  have h71 : 71 ≤ 2 ^ 272 := by decide +kernel
  omega

end BBPPi
