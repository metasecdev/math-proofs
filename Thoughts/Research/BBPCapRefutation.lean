import Thoughts.Research.BBPCapAnalysis

/-!
# P-BBP-01: the literal capped statement is FALSE (2026-10-29)

`PBBP01General : ∀ n, bbp_hex_digit n = bbpHexDigitReal n` uses the capped certificate
`bbp_hex_digit n = bbpGuardedLo n (bbpCertGuard n) % 16`, whose guard search stops at depth 68.

Structural argument (no enumeration, no digit of π computed):
* the guarded lower end is *always* below `16^n π` by a deterministic amount:
  `16^(n+g) π − (5K+3) − 16^g < lo·16^g ≤ 16^(n+g) π − (K+2)` with `K = n+g+1`
  (per-term floor error `∈ (−1, 3)`, error budget `E = 4K+2`, tail `∈ [0,1)`);
* so if `16^g ≤ K+2` and `5K+3 ≤ 14·16^g`, then `1 ≤ ⌊16^n π⌋ − lo ≤ 14` and the hex digits
  differ (`lo_digit_ne_of_window`);
* for `2^272 ≤ n ≤ 2^273` every searched depth `4,…,64` fails (`16^64 ≤ 8n`), so
  `bbpCertGuard n = 68`, and `g = 68` satisfies both inequalities.

Hence `bbp_hex_digit n ≠ bbpHexDigitReal n` for every `n ∈ [2^272, 2^273]`:
`not_PBBP01General`, `not_CertDigitTail`, `not_PBBP01OpenGap`.
The explicit-guard form `bbp_digit_all_n_unconditional` is unaffected.
-/

namespace FinitistProved
open Real

/-- Deterministic two-sided position of the guarded lower end (needs `1 ≤ n` so `E ≤ S`). -/
theorem guardedLo_position (n g : ℕ) (hn : 1 ≤ n) :
    (bbpGuardedLo n g : ℝ) * (16 : ℝ) ^ g ≤
        (16 : ℝ) ^ g * ((16 : ℝ) ^ n * Real.pi) - ((n : ℝ) + g + 1 + 2) ∧
      (16 : ℝ) ^ g * ((16 : ℝ) ^ n * Real.pi) - (5 * ((n : ℝ) + g + 1) + 3) - (16 : ℝ) ^ g <
        (bbpGuardedLo n g : ℝ) * (16 : ℝ) ^ g := by
  have hx := bbpSeries_scaled_split (n + g)
  have ht0 := bbpScaledTail_nonneg (n + g)
  have ht1 := bbpScaledTail_lt_one (n + g)
  obtain ⟨hs1, hs2⟩ := bbpSpigotSum_cast_bounds (n + g) (n + g + 1)
  have hhead :
      bbpScaledHead (n + g) =
        (16 : ℝ) ^ (n + g) * ∑ k ∈ Finset.range (n + g + 1), bbpSummand k := rfl
  have hS : bbpGuardedSum n g = bbpSpigotSum (n + g) (n + g + 1) := rfl
  have hE : ((bbpGuardErr n g : ℕ) : ℝ) = 4 * ((n : ℝ) + g + 1) + 2 := by
    simp [bbpGuardErr]
  have hpow : (16 : ℝ) ^ (n + g) = (16 : ℝ) ^ g * (16 : ℝ) ^ n := by rw [pow_add, mul_comm]
  have hcastK : ((n + g + 1 : ℕ) : ℝ) = (n : ℝ) + g + 1 := by push_cast; ring
  rw [hcastK] at hs1 hs2
  rw [bbpSeries_eq_pi, hpow] at hx
  rw [hhead, hpow] at hx
  have hge := bbpGuardedSum_ge_err n g hn
  set D := bbpGuardedSum n g - bbpGuardErr n g with hD
  have hDr : (D : ℝ) = (bbpSpigotSum (n + g) (n + g + 1) : ℝ) - (4 * ((n : ℝ) + g + 1) + 2) := by
    rw [hD, Nat.cast_sub hge, hE, hS]
  have hpos : 0 < 16 ^ g := by positivity
  have hdm := Nat.div_add_mod D (16 ^ g)
  have hmod := Nat.mod_lt D hpos
  have hlo : bbpGuardedLo n g = D / 16 ^ g := rfl
  have hdmR : ((16 ^ g * (D / 16 ^ g) + D % 16 ^ g : ℕ) : ℝ) = (D : ℝ) := by rw [hdm]
  push_cast at hdmR
  have hmodR : ((D % 16 ^ g : ℕ) : ℝ) < (16 : ℝ) ^ g := by exact_mod_cast hmod
  have hmod0 : (0 : ℝ) ≤ ((D % 16 ^ g : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hlo]
  rw [hpow] at hs1 hs2
  constructor <;> nlinarith

/-- If `16^g ≤ K+2` and `5K+3 ≤ 14·16^g` (`K = n+g+1`), the depth-`g` certificate digit is wrong. -/
theorem lo_digit_ne_of_window (n g : ℕ) (hn : 1 ≤ n) (h1 : 16 ^ g ≤ n + g + 1 + 2)
    (h2 : 5 * (n + g + 1) + 3 ≤ 14 * 16 ^ g) :
    bbpGuardedLo n g % 16 ≠ bbpHexDigitReal n := by
  obtain ⟨hu, hl⟩ := guardedLo_position n g hn
  have hg : (0 : ℝ) < (16 : ℝ) ^ g := by positivity
  have h1R : (16 : ℝ) ^ g ≤ (n : ℝ) + g + 1 + 2 := by exact_mod_cast h1
  have h2R : 5 * ((n : ℝ) + g + 1) + 3 ≤ 14 * (16 : ℝ) ^ g := by exact_mod_cast h2
  set x := (16 : ℝ) ^ n * Real.pi with hxdef
  set lo := bbpGuardedLo n g
  -- lo ≤ x - 1 and x < lo + 15
  have hA : ((lo : ℝ) + 1) * (16 : ℝ) ^ g ≤ x * (16 : ℝ) ^ g := by nlinarith
  have hB : x * (16 : ℝ) ^ g < ((lo : ℝ) + 15) * (16 : ℝ) ^ g := by nlinarith
  have hA' : (lo : ℝ) + 1 ≤ x := le_of_mul_le_mul_right hA hg
  have hB' : x < (lo : ℝ) + 15 := lt_of_mul_lt_mul_right hB hg.le
  have hF1 : ((lo : ℤ) + 1) ≤ ⌊x⌋ := Int.le_floor.2 (by push_cast; exact hA')
  have hF2 : ⌊x⌋ < (lo : ℤ) + 15 := Int.floor_lt.2 (by push_cast; exact hB')
  unfold bbpHexDigitReal
  rw [← hxdef]
  have hnn : 0 ≤ ⌊x⌋ := by omega
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnn
  rw [hm, Int.toNat_natCast]
  rw [hm] at hF1 hF2
  omega

/-- The capped guard search returns `g + 4·fuel` when every tried depth fails. -/
theorem bbpGuardSearch_of_all_fail (n : ℕ) :
    ∀ (fuel g : ℕ), (∀ t < fuel, ¬ BBPGuardAgreesAt n (g + 4 * t)) →
      bbpGuardSearch n fuel g = g + 4 * fuel := by
  intro fuel
  induction fuel with
  | zero => intro g _; simp [bbpGuardSearch]
  | succ f ih =>
    intro g h
    have h0 : ¬ (bbpGuardedLo n g = bbpGuardedHi n g) := by simpa using h 0 (by omega)
    simp only [bbpGuardSearch, h0, if_false]
    rw [ih (g + 4) (fun t ht => by
      have := h (t + 1) (by omega)
      rwa [show g + 4 * (t + 1) = g + 4 + 4 * t by ring] at this)]
    ring

/-- For `n ≥ 2^253` the capped search exhausts its grid: `bbpCertGuard n = 68`. -/
theorem bbpCertGuard_eq_68 (n : ℕ) (hn : 2 ^ 253 ≤ n) : bbpCertGuard n = 68 := by
  have h1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have h16 : (16 : ℕ) ^ 64 = 8 * 2 ^ 253 := by decide +kernel
  have hfail := no_guard_below_cap 64 n h1 (by omega)
  unfold bbpCertGuard bbpGuardDigits
  rw [bbpGuardSearch_of_all_fail n 16 4 (fun t ht => hfail _ (by omega))]

/-- **Refutation window:** for every `n ∈ [2^272, 2^273]` the capped digit is wrong. -/
theorem not_BBPSpigotDigitCorrect_window (n : ℕ) (hlo : 2 ^ 272 ≤ n) (hhi : n ≤ 2 ^ 273) :
    ¬ BBPSpigotDigitCorrect n := by
  have hG : bbpCertGuard n = 68 :=
    bbpCertGuard_eq_68 n (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hlo)
  have h1 : 1 ≤ n := le_trans Nat.one_le_two_pow hlo
  have h16 : (16 : ℕ) ^ 68 = 2 ^ 272 := by decide +kernel
  have h2 : (2 : ℕ) ^ 273 = 2 * 2 ^ 272 := by decide +kernel
  unfold BBPSpigotDigitCorrect
  show bbpHexDigitCert n ≠ _
  unfold bbpHexDigitCert bbpCertFloor
  rw [hG]
  exact lo_digit_ne_of_window n 68 h1 (by omega) (by omega)

/-- **P-BBP-01 (literal capped form) is false**, witnessed at `n = 2^272`. -/
theorem not_PBBP01General : ¬ PBBP01General := fun h =>
  not_BBPSpigotDigitCorrect_window (2 ^ 272) le_rfl (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (h _)

theorem not_CertDigitTail : ¬ CertDigitTail := fun h =>
  not_BBPSpigotDigitCorrect_window (2 ^ 272) le_rfl (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (h _ (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- The named open gap is closed: it is refuted. -/
theorem not_PBBP01OpenGap : ¬ PBBP01OpenGap := fun h => not_CertDigitTail h.2

end FinitistProved

#print axioms FinitistProved.guardedLo_position
#print axioms FinitistProved.lo_digit_ne_of_window
#print axioms FinitistProved.bbpCertGuard_eq_68
#print axioms FinitistProved.not_BBPSpigotDigitCorrect_window
#print axioms FinitistProved.not_PBBP01General
#print axioms FinitistProved.not_PBBP01OpenGap
