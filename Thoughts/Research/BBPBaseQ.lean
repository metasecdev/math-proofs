import Thoughts.Research.MahlerSharpAllQ

/-!
# Round 6: base-`q` digits of π for every `q ≥ 2` (measure + guard, no digit extraction)

From `PiEffectiveMeasure 658 (2^-1721993)` (all denominators): any real `A` within
`ε = 2^-1721993 · q^n / (q^n)^658` of `q^n π` has `⌊A⌋ = ⌊q^n π⌋`.  So every base-`q` digit
`⌊q^n π⌋ mod q` is determined by an approximation of `π` to `≈ 657·n·log₂ q + 1721993` bits
(e.g. a scaled BBP partial sum).  This is *not* a BBP-style spigot for `q ≠ 2^j`.
-/

namespace FinitistProved
open Real

/-- generic: an effective measure makes `⌊q^n π⌋` stable under perturbations below the gap. -/
theorem floor_eq_of_effective_measure {μ : ℕ} {C : ℝ} (H : PiEffectiveMeasure μ C)
    {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) {A : ℝ}
    (hA : |A - (q : ℝ) ^ n * Real.pi| ≤ C * (q : ℝ) ^ n / ((q : ℝ) ^ n) ^ μ) :
    ⌊A⌋ = ⌊(q : ℝ) ^ n * Real.pi⌋ := by
  set x := (q : ℝ) ^ n * Real.pi
  have hQ : 2 ≤ q ^ n := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
  have hQR : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  -- for every integer z: |x - z| > C q^n / (q^n)^μ
  have key : ∀ z : ℤ, C * (q : ℝ) ^ n / ((q : ℝ) ^ n) ^ μ < |x - z| := by
    intro z
    have h := H z (q ^ n) hQ
    push_cast at h
    have e : |x - z| = (q : ℝ) ^ n * |Real.pi - z / (q : ℝ) ^ n| := by
      rw [← abs_of_pos hQR, ← abs_mul, abs_of_pos hQR]
      congr 1; simp only [x]; field_simp
    rw [e]
    have hpow : (0 : ℝ) < ((q : ℝ) ^ n) ^ μ := by positivity
    calc C * (q : ℝ) ^ n / ((q : ℝ) ^ n) ^ μ = (q : ℝ) ^ n * (C / ((q : ℝ) ^ n) ^ μ) := by ring
      _ < _ := mul_lt_mul_of_pos_left h hQR
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- ⌊A⌋ < ⌊x⌋ : z = ⌊x⌋ with A < z ≤ x
    have h1 : A < (⌊x⌋ : ℝ) := by
      have := Int.lt_floor_add_one A
      have h2 : (⌊A⌋ : ℝ) + 1 ≤ ⌊x⌋ := by exact_mod_cast hlt
      linarith
    have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have := key ⌊x⌋
    rw [abs_of_nonneg (by linarith)] at this
    have := abs_le.mp hA
    linarith
  · have h1 : x < (⌊A⌋ : ℝ) := by
      have := Int.lt_floor_add_one x
      have h2 : (⌊x⌋ : ℝ) + 1 ≤ ⌊A⌋ := by exact_mod_cast hgt
      linarith
    have h2 : (⌊A⌋ : ℝ) ≤ A := Int.floor_le A
    have := key ⌊A⌋
    rw [abs_of_neg (by linarith)] at this
    have := abs_le.mp hA
    linarith

/-- **Base-`q` digits of π, all `q ≥ 2`, all `n ≥ 1`**: any `A` with
`|A − q^n π| ≤ 2^-1721993 · q^n / (q^n)^658` gives `⌊A⌋ = ⌊q^n π⌋`, hence the `n`-th base-`q`
digit `⌊q^n π⌋ mod q = ⌊A⌋ mod q`. -/
theorem baseq_floor_of_approx {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) {A : ℝ}
    (hA : |A - (q : ℝ) ^ n * Real.pi| ≤ (1 / 2 ^ 1721993) * (q : ℝ) ^ n / ((q : ℝ) ^ n) ^ 658) :
    ⌊A⌋ = ⌊(q : ℝ) ^ n * Real.pi⌋ ∧ ⌊A⌋ % q = ⌊(q : ℝ) ^ n * Real.pi⌋ % q := by
  have h := floor_eq_of_effective_measure MahlerSharp.pi_effective_measure6 hq hn hA
  exact ⟨h, by rw [h]⟩

end FinitistProved

#print axioms FinitistProved.floor_eq_of_effective_measure
#print axioms FinitistProved.baseq_floor_of_approx
