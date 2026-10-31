import Thoughts.Research.BBPBaseQ
import Thoughts.Proved.BBPPiIdentity

/-!
# Round 7: computable base-`q` digit certificate for π (all `q ≥ 2`, all `n`)

* `bbpHeadQ N : ℚ` — rational BBP partial sum `∑_{k ≤ N} c_k / 16^k`; `π ∈ [S_N, S_N + 16^-N)`.
* `baseqLo/Hi q n N` — `⌊q^n S_N⌋`, `⌊q^n (S_N + 16^-N)⌋` (integers, computable over `ℚ`).
* `baseq_floor_of_bracket` — *sound at every depth*: `Lo = Hi → Lo = ⌊q^n π⌋`.
* `baseq_floor_at_depth` — at `N = baseqDepth q n = 430499 + 658·n·(⌊log₁₆ q⌋+1)`,
  `Lo = ⌊q^n π⌋` unconditionally (via `pi_effective_measure6`).
* `baseqCertFloor` — search `Lo = Hi` over small depths, fall back to `baseqDepth`;
  **`baseqCertFloor_eq`**: `baseqCertFloor q n = ⌊q^n π⌋` for all `q ≥ 2`, all `n`;
  **`baseqCertDigit_eq`**: the `n`-th base-`q` digit `⌊q^n π⌋ mod q`.
-/

namespace FinitistProved
open Real

/-- rational BBP partial sum `∑_{k ≤ N} c_k / 16^k`. -/
def bbpHeadQ (N : ℕ) : ℚ := ∑ k ∈ Finset.range (N + 1), bbpCoeffQ k / (16 : ℚ) ^ k

theorem bbpHeadQ_cast (N : ℕ) : ((bbpHeadQ N : ℚ) : ℝ) = bbpHead N := by
  unfold bbpHeadQ bbpHead bbpSummand
  push_cast
  exact Finset.sum_congr rfl fun k _ => by rw [bbpCoeffQ_coe]

/-- `S_N ≤ π < S_N + 16^-N`. -/
theorem pi_bracket (N : ℕ) :
    (bbpHeadQ N : ℝ) ≤ Real.pi ∧ Real.pi < (bbpHeadQ N : ℝ) + 1 / (16 : ℝ) ^ N := by
  have hs := bbpSeries_split N
  rw [bbpSeries_eq_pi] at hs
  have h0 := bbpScaledTail_nonneg N
  have h1 := bbpScaledTail_lt_one N
  rw [bbpScaledTail_eq_mul_tailSeries] at h0 h1
  have hp : (0 : ℝ) < 16 ^ N := by positivity
  rw [bbpHeadQ_cast]
  refine ⟨?_, ?_⟩
  · have : 0 ≤ bbpTailSeries N := by
      by_contra h; push_neg at h; nlinarith
    linarith
  · have : bbpTailSeries N < 1 / 16 ^ N := by
      rw [lt_div_iff₀ hp]; linarith
    linarith

/-- lower bracket floor `⌊q^n S_N⌋`. -/
def baseqLo (q n N : ℕ) : ℤ := ⌊(q : ℚ) ^ n * bbpHeadQ N⌋
/-- upper bracket floor `⌊q^n (S_N + 16^-N)⌋`. -/
def baseqHi (q n N : ℕ) : ℤ := ⌊(q : ℚ) ^ n * (bbpHeadQ N + 1 / (16 : ℚ) ^ N)⌋

/-- **soundness at every depth**: if the bracket floors agree they equal `⌊q^n π⌋`. -/
theorem baseq_floor_of_bracket {q n N : ℕ} (h : baseqLo q n N = baseqHi q n N) :
    baseqLo q n N = ⌊(q : ℝ) ^ n * Real.pi⌋ := by
  obtain ⟨hl, hu⟩ := pi_bracket N
  have hq : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
  have eL : baseqLo q n N = ⌊(q : ℝ) ^ n * (bbpHeadQ N : ℝ)⌋ := by
    unfold baseqLo; rw [← Rat.floor_cast (α := ℝ)]; congr 1; push_cast; ring
  have eH : baseqHi q n N = ⌊(q : ℝ) ^ n * ((bbpHeadQ N : ℝ) + 1 / (16 : ℝ) ^ N)⌋ := by
    unfold baseqHi; rw [← Rat.floor_cast (α := ℝ)]; congr 1; push_cast; ring
  apply le_antisymm
  · rw [eL]; exact Int.floor_mono (mul_le_mul_of_nonneg_left hl hq)
  · rw [h, eH]; exact Int.floor_mono (mul_le_mul_of_nonneg_left hu.le hq)

/-- depth at which the effective measure (`μ = 658`) forces the lower floor to be exact. -/
def baseqDepth (q n : ℕ) : ℕ := 430499 + 658 * n * (Nat.log 16 q + 1)

theorem baseq_floor_at_depth {q n : ℕ} (hq : 2 ≤ q) :
    baseqLo q n (baseqDepth q n) = ⌊(q : ℝ) ^ n * Real.pi⌋ := by
  set N := baseqDepth q n
  obtain ⟨hl, hu⟩ := pi_bracket N
  have eL : baseqLo q n N = ⌊(q : ℝ) ^ n * (bbpHeadQ N : ℝ)⌋ := by
    unfold baseqLo; rw [← Rat.floor_cast (α := ℝ)]; congr 1; push_cast; ring
  rw [eL]
  have hqR : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have h16 : (0 : ℝ) < 16 ^ N := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: π is ≥ 0.14 from every integer and the error is < 16^-430499
    simp only [pow_zero, one_mul]
    have herr : 1 / (16 : ℝ) ^ N ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le (by norm_num)
      calc (16 : ℝ) = 16 ^ 1 := by norm_num
        _ ≤ 16 ^ N := pow_le_pow_right₀ (by norm_num) (by simp [N, baseqDepth])
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h2 : (⌊(bbpHeadQ N : ℝ)⌋ : ℝ) + 1 ≤ ⌊Real.pi⌋ := by exact_mod_cast hlt
      have := Int.lt_floor_add_one (bbpHeadQ N : ℝ)
      have := Int.floor_le Real.pi
      have := pi_dist_int_gt ⌊Real.pi⌋
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    · have h2 : (⌊Real.pi⌋ : ℝ) + 1 ≤ ⌊(bbpHeadQ N : ℝ)⌋ := by exact_mod_cast hgt
      have := Int.lt_floor_add_one Real.pi
      have := Int.floor_le (bbpHeadQ N : ℝ)
      have := pi_dist_int_gt ⌊(bbpHeadQ N : ℝ)⌋
      rw [abs_of_neg (by linarith)] at this
      linarith
  · apply floor_eq_of_effective_measure MahlerSharp.pi_effective_measure6 hq hn
    -- |q^n S - q^n π| ≤ q^n / 16^N ≤ C q^n / (q^n)^658
    have hab : |(q : ℝ) ^ n * (bbpHeadQ N : ℝ) - (q : ℝ) ^ n * Real.pi| ≤ (q : ℝ) ^ n / 16 ^ N := by
      rw [← mul_sub, abs_mul, abs_of_pos hqR, div_eq_mul_one_div]
      gcongr
      rw [abs_of_nonpos (by linarith)]; linarith
    refine hab.trans ?_
    -- 2^1721993 · (q^n)^658 ≤ 16^N
    have hL : q < 16 ^ (Nat.log 16 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hnat : 2 ^ 1721993 * (q ^ n) ^ 658 ≤ 16 ^ N := by
      have e : 16 ^ N = 16 ^ 430499 * (16 ^ (Nat.log 16 q + 1)) ^ (n * 658) := by
        simp only [N, baseqDepth]; rw [pow_add, ← pow_mul]; ring_nf
      rw [e, ← pow_mul]
      apply Nat.mul_le_mul
      · rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
      · exact Nat.pow_le_pow_left hL.le _
    have hR : (2 : ℝ) ^ 1721993 * ((q : ℝ) ^ n) ^ 658 ≤ 16 ^ N := by exact_mod_cast hnat
    have hp : (0 : ℝ) < ((q : ℝ) ^ n) ^ 658 := by positivity
    rw [div_le_iff₀ h16]
    have : (1 / 2 ^ 1721993 : ℝ) * (q : ℝ) ^ n / ((q : ℝ) ^ n) ^ 658 * 16 ^ N
        = (q : ℝ) ^ n * (16 ^ N / (2 ^ 1721993 * ((q : ℝ) ^ n) ^ 658)) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ (16 : ℝ) ^ N / (2 ^ 1721993 * ((q : ℝ) ^ n) ^ 658) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith

/-- search depths `g, g+1, …` (fuel `f`) for agreeing bracket floors; fall back to `baseqDepth`. -/
def baseqSearch (q n : ℕ) : ℕ → ℕ → ℤ
  | _, 0 => baseqLo q n (baseqDepth q n)
  | g, f + 1 => if baseqLo q n g = baseqHi q n g then baseqLo q n g else baseqSearch q n (g + 1) f

theorem baseqSearch_eq {q n : ℕ} (hq : 2 ≤ q) (g f : ℕ) :
    baseqSearch q n g f = ⌊(q : ℝ) ^ n * Real.pi⌋ := by
  induction f generalizing g with
  | zero => exact baseq_floor_at_depth hq
  | succ f ih =>
    unfold baseqSearch
    split_ifs with h
    · exact baseq_floor_of_bracket h
    · exact ih (g + 1)

/-- computable certificate floor: start at depth `n·(⌊log₁₆ q⌋+1) + 2`, try 64 depths. -/
def baseqCertFloor (q n : ℕ) : ℤ := baseqSearch q n (n * (Nat.log 16 q + 1) + 2) 64

/-- computable `n`-th base-`q` digit of π (digit `n` after the point; `n = 0` is `3 mod q`). -/
def baseqCertDigit (q n : ℕ) : ℤ := baseqCertFloor q n % q

/-- **Round 7, base-`q` certificate**: for all `q ≥ 2` and all `n`, the certificate is exact. -/
theorem baseqCertFloor_eq {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    baseqCertFloor q n = ⌊(q : ℝ) ^ n * Real.pi⌋ := baseqSearch_eq hq _ _

theorem baseqCertDigit_eq {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    baseqCertDigit q n = ⌊(q : ℝ) ^ n * Real.pi⌋ % q := by
  unfold baseqCertDigit; rw [baseqCertFloor_eq hq]

-- sanity (evaluation only, not a proof): `⌊10^5 π⌋ = 314159`, `⌊3^8 π⌋ = 20611`
#eval baseqCertFloor 10 5
#eval (baseqCertFloor 3 8, baseqCertDigit 7 20)

end FinitistProved

#print axioms FinitistProved.baseq_floor_at_depth
#print axioms FinitistProved.baseqCertFloor_eq
#print axioms FinitistProved.baseqCertDigit_eq
