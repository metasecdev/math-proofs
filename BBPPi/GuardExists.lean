import Mathlib.Tactic
import BBPPi.Identity
import BBPPi.Guarded
import BBPPi.Spigot
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Every position has an agreeing guard depth

`bbpGuardedLo n g = bbpGuardedHi n g` for some `g` (not capped at 68), proved from the
proved guarded bracket machinery, the BBP identity (`bbpSeries = π`) and Mathlib's `irrational_pi`.
Only irrationality is used: `16^n·π` is irrational, so its fractional part `f` lies strictly in
`(0,1)`, and the bracket half-width `E/16^g` shrinks exponentially while `E` grows only
linearly in `g`. No normality / digit-run statement about π is needed for existence.

What this does NOT give: a bound on `g` in terms of `n`. The capped certificate
`bbpCertFloor` / `bbpGuardAgrees` (g ≤ 68) provably fails for `n ≥ 2^270`
(`BBPPiCerts.GuardCap`); making it work for all `n` needs `g` to grow with `n`, which in
turn depends on how close `16^n·π` can be to an integer (irrationality measure of π); see `BBPPi.Mu570`.
-/

namespace BBPPi

open Real

private lemma irrational_scaled (n : ℕ) : Irrational ((16 : ℝ) ^ n * bbpSeries) := by
  rw [bbpSeries_eq_pi]
  have h := irrational_pi.natCast_mul (m := 16 ^ n) (by positivity)
  simpa using h

/-- Sharp (width < 1 unit at `16^g`) enclosure of `S` around `16^(n+g)·bbpSeries`. -/
private lemma guardedSum_enclosure (n g : ℕ) :
    (16 : ℝ) ^ (n + g) * bbpSeries - 1 - ((n : ℝ) + g + 1) < (bbpGuardedSum n g : ℝ) ∧
      (bbpGuardedSum n g : ℝ) ≤ (16 : ℝ) ^ (n + g) * bbpSeries + 3 * ((n : ℝ) + g + 1) := by
  have hx := bbpSeries_scaled_split (n + g)
  have ht0 := bbpScaledTail_nonneg (n + g)
  have ht1 := bbpScaledTail_lt_one (n + g)
  obtain ⟨hs1, hs2⟩ := bbpSpigotSum_cast_bounds (n + g) (n + g + 1)
  have hhead :
      bbpScaledHead (n + g) =
        (16 : ℝ) ^ (n + g) * ∑ k ∈ Finset.range (n + g + 1), bbpSummand k := rfl
  have hS : bbpGuardedSum n g = bbpSpigotSum (n + g) (n + g + 1) := rfl
  have hcastK : ((n + g + 1 : ℕ) : ℝ) = (n : ℝ) + g + 1 := by push_cast; ring
  rw [hcastK] at hs1 hs2
  rw [hS]
  rw [hhead] at hx
  constructor <;> linarith

/-- Exponential beats linear: some `g` has `7(n+g+1)+3 ≤ δ·16^g`. -/
private lemma exists_big_guard (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : ℕ, 1 ≤ g ∧ 7 * ((n : ℝ) + g + 1) + 3 ≤ δ * (16 : ℝ) ^ g := by
  obtain ⟨g, hg⟩ := exists_nat_gt ((7 * (n : ℝ) + 17) / δ)
  refine ⟨g + 1, by omega, ?_⟩
  have hg' : 7 * (n : ℝ) + 17 < g * δ := by
    rwa [div_lt_iff₀ hδ] at hg
  have hb : (1 : ℝ) + 3 * (g + 1 : ℕ) ≤ (4 : ℝ) ^ (g + 1) := by
    have := one_add_mul_le_pow (a := (3 : ℝ)) (by norm_num) (g + 1)
    norm_num at this ⊢
    linarith
  have h16 : (16 : ℝ) ^ (g + 1) = (4 : ℝ) ^ (g + 1) * (4 : ℝ) ^ (g + 1) := by
    rw [← mul_pow]; norm_num
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (1 : ℝ) + 3 * (g + 1 : ℕ) ≤ (4 : ℝ) ^ (g + 1) := hb
  push_cast at h1 ⊢
  rw [h16]
  have h4pos : (0 : ℝ) ≤ (4 : ℝ) ^ (g + 1) := by positivity
  have hsq : (4 + 3 * (g : ℝ)) * (4 + 3 * (g : ℝ)) ≤ (4 : ℝ) ^ (g + 1) * (4 : ℝ) ^ (g + 1) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) h4pos
  have hδsq : δ * ((4 + 3 * (g : ℝ)) * (4 + 3 * (g : ℝ))) ≤ δ * ((4 : ℝ) ^ (g + 1) * (4 : ℝ) ^ (g + 1)) :=
    mul_le_mul_of_nonneg_left hsq hδ.le
  nlinarith [mul_pos hδ hδ, hg', hg0, hn0, mul_nonneg hg0 hg0, mul_nonneg hg0 hδ.le]

/-- **For every `n`, some guard depth `g` makes the guarded bracket collapse** (so
`bbpGuardedLo n g` is exactly `⌊16^n·π⌋`). Uses only the BBP identity and irrationality of π. -/
theorem exists_guard_agrees (n : ℕ) : ∃ g : ℕ, bbpGuardedLo n g = bbpGuardedHi n g := by
  set x : ℝ := (16 : ℝ) ^ n * bbpSeries with hx
  have hirr : Irrational x := irrational_scaled n
  have hxpos : 0 ≤ x := by
    rw [hx, bbpSeries_eq_pi]; positivity
  set F : ℕ := ⌊x⌋₊ with hF
  have hF1 : (F : ℝ) ≤ x := Nat.floor_le hxpos
  have hF2 : x < F + 1 := Nat.lt_floor_add_one x
  have hne : x ≠ (F : ℝ) := by
    have := hirr.ne_nat F
    exact this
  have hf0 : 0 < x - F := by
    have : (F : ℝ) < x := lt_of_le_of_ne hF1 (Ne.symm hne)
    linarith
  have hf1 : 0 < (F + 1 : ℝ) - x := by linarith
  obtain ⟨g, -, hgbig⟩ := exists_big_guard n (min (x - F) ((F + 1 : ℝ) - x)) (lt_min hf0 hf1)
  refine ⟨g, ?_⟩
  obtain ⟨hlo, hup⟩ := guardedSum_enclosure n g
  have hpow : (16 : ℝ) ^ (n + g) = (16 : ℝ) ^ n * (16 : ℝ) ^ g := pow_add _ _ _
  have hX : (16 : ℝ) ^ (n + g) * bbpSeries = x * (16 : ℝ) ^ g := by
    rw [hpow, hx]; ring
  rw [hX] at hlo hup
  have hm : (0 : ℝ) < (16 : ℝ) ^ g := by positivity
  have hE : ((bbpGuardErr n g : ℕ) : ℝ) = 4 * ((n : ℝ) + g + 1) + 2 := by simp [bbpGuardErr]
  have hd1 : min (x - F) ((F + 1 : ℝ) - x) * (16 : ℝ) ^ g ≤ (x - F) * (16 : ℝ) ^ g :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hm.le
  have hd2 : min (x - F) ((F + 1 : ℝ) - x) * (16 : ℝ) ^ g ≤ ((F + 1 : ℝ) - x) * (16 : ℝ) ^ g :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hm.le
  -- real inequalities for the two ends
  have hA : ((F * 16 ^ g + bbpGuardErr n g : ℕ) : ℝ) ≤ (bbpGuardedSum n g : ℝ) := by
    push_cast; rw [hE]; nlinarith
  have hB : (bbpGuardedSum n g : ℝ) + (bbpGuardErr n g : ℝ) < (((F + 1) * 16 ^ g : ℕ) : ℝ) := by
    push_cast; rw [hE]; nlinarith
  have hA' : F * 16 ^ g + bbpGuardErr n g ≤ bbpGuardedSum n g := by exact_mod_cast hA
  have hB' : bbpGuardedSum n g + bbpGuardErr n g < (F + 1) * 16 ^ g := by exact_mod_cast hB
  have hlo' : bbpGuardedLo n g = F := by
    unfold bbpGuardedLo
    exact Nat.div_eq_of_lt_le (by omega) (by
      have : bbpGuardedSum n g - bbpGuardErr n g < (F + 1) * 16 ^ g := by omega
      exact this)
  have hhi' : bbpGuardedHi n g = F := by
    unfold bbpGuardedHi
    exact Nat.div_eq_of_lt_le (by omega) hB'
  rw [hlo', hhi']

/-- **Uncapped certificate, every `n`:** some guard depth `g` collapses the bracket and the
common value is `⌊16^n·π⌋`. (Existential in `g`: no bound on `g` in terms of `n` is claimed, so
this is not a statement about the capped `bbpCertFloor`.) -/
theorem exists_guard_floor_pi (n : ℕ) :
    ∃ g : ℕ, bbpGuardedLo n g = bbpGuardedHi n g ∧
      ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpGuardedLo n g : ℤ) := by
  obtain ⟨g, hg⟩ := exists_guard_agrees n
  refine ⟨g, hg, ?_⟩
  rw [← bbpSeries_eq_pi]
  exact bbpGuarded_floor_eq n g hg

/-- **Uncapped digit certificate, every `n`:** for each `n` there is a guard depth `g` at which the
guarded bracket collapses and its low hex digit is the true `n`-th hex digit of π. (Existential in
`g`; says nothing about how large `g` must be, and is not about the capped `bbp_hex_digit`.) -/
theorem exists_guard_digit_pi (n : ℕ) :
    ∃ g : ℕ, bbpGuardedLo n g = bbpGuardedHi n g ∧ bbpGuardedLo n g % 16 = bbpHexDigitReal n := by
  obtain ⟨g, hg, hf⟩ := exists_guard_floor_pi n
  refine ⟨g, hg, ?_⟩
  unfold bbpHexDigitReal
  rw [hf]
  simp

end BBPPi
