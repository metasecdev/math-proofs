import Mathlib.Tactic
import BBPPi.Series
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Soundness of the guarded spigot bracket

Guarded spigot floor certificate: proved two-sided bracket.

For every `n` and guard depth `g`, with `S = bbpGuardedSum n g` and `E = bbpGuardErr n g`:

  `(S - E) / 16^g ≤ 16^n · bbpSeries < (S + E) / 16^g + 1`        (`bbpGuarded_bracket`)

so whenever the two ends agree (`bbpGuardedLo n g = bbpGuardedHi n g`, a decidable
check on natural numbers) the common value is exactly `⌊16^n · bbpSeries⌋`
(`bbpGuarded_floor_eq`). No hypothesis about π is used here; the link to π is the
single stated hypothesis `BBPPiEqualsSeries` (the BBP identity), used only in the `_pi` variants.
-/

namespace BBPPi

open Real Nat Finset

private lemma natDiv_cast_bounds (m d : ℕ) :
    ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / d ∧ (m : ℝ) / d < ((m / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h := Nat.lt_floor_add_one ((m : ℝ) / d)
  rwa [Nat.floor_div_eq_div] at h

private lemma scaled_summand_eq (k N : ℕ) :
    (16 : ℝ) ^ N * bbpSummand k =
      ((4 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 1) : ℕ) : ℝ) -
        ((2 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 4) : ℕ) : ℝ) -
        ((16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 5) : ℕ) : ℝ) -
        ((16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 6) : ℕ) : ℝ) := by
  unfold bbpSummand bbpCoeff
  push_cast
  field_simp

/--
  Per-term error of the corrected integer term: each of the four floors loses `< 1`,
  one with a `+` sign and three with a `-` sign, so
  `16^N·bbpSummand k - 1 < bbp_term k N < 16^N·bbpSummand k + 3`.
  (Also shows the truncated `Nat` subtraction never truncates.)
-/
theorem bbp_term_cast_bounds (k N : ℕ) :
    (16 : ℝ) ^ N * bbpSummand k - 1 < (bbp_term k N : ℝ) ∧
      (bbp_term k N : ℝ) < (16 : ℝ) ^ N * bbpSummand k + 3 := by
  obtain ⟨a1, b1⟩ := natDiv_cast_bounds (4 * 16 ^ N) (16 ^ k * (8 * k + 1))
  obtain ⟨a4, b4⟩ := natDiv_cast_bounds (2 * 16 ^ N) (16 ^ k * (8 * k + 4))
  obtain ⟨a5, b5⟩ := natDiv_cast_bounds (16 ^ N) (16 ^ k * (8 * k + 5))
  obtain ⟨a6, b6⟩ := natDiv_cast_bounds (16 ^ N) (16 ^ k * (8 * k + 6))
  have hsc : 0 ≤ (16 : ℝ) ^ N * bbpSummand k :=
    mul_nonneg (by positivity) (bbpSummand_nonneg k)
  rw [scaled_summand_eq] at hsc ⊢
  have hd1 : (0 : ℝ) < ((16 ^ k * (8 * k + 1) : ℕ) : ℝ) := by positivity
  have hle :
      (2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
          (16 ^ N) / (16 ^ k * (8 * k + 6)) ≤
        (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have h' :
        (((2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
            (16 ^ N) / (16 ^ k * (8 * k + 6)) : ℕ) : ℝ) ≤
          ((4 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_add]
      linarith
    rw [le_div_iff₀ hd1] at h'
    exact_mod_cast h'
  have hterm :
      bbp_term k N =
        (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) -
          ((2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
            (16 ^ N) / (16 ^ k * (8 * k + 6))) := by
    show (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) - (2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) -
        16 ^ N / (16 ^ k * (8 * k + 5)) - 16 ^ N / (16 ^ k * (8 * k + 6)) = _
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_assoc]
  rw [hterm, Nat.cast_sub hle, Nat.cast_add, Nat.cast_add]
  constructor <;> linarith

/-- Summed error: `16^N·∑_{k<K} bbpSummand k - K ≤ bbpSpigotSum N K ≤ … + 3K`. -/
theorem bbpSpigotSum_cast_bounds (N K : ℕ) :
    (16 : ℝ) ^ N * (∑ k ∈ Finset.range K, bbpSummand k) - K ≤ (bbpSpigotSum N K : ℝ) ∧
      (bbpSpigotSum N K : ℝ) ≤ (16 : ℝ) ^ N * (∑ k ∈ Finset.range K, bbpSummand k) + 3 * K := by
  induction K with
  | zero => simp [bbpSpigotSum]
  | succ K ih =>
    obtain ⟨h1, h2⟩ := bbp_term_cast_bounds K N
    simp only [bbpSpigotSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_succ, mul_add]
    constructor <;> linarith [ih.1, ih.2]

theorem bbpSpigotSum_eq_sum (N K : ℕ) :
    bbpSpigotSum N K = ∑ k ∈ Finset.range K, bbp_term k N := by
  induction K with
  | zero => simp [bbpSpigotSum]
  | succ K ih => simp [bbpSpigotSum, Finset.sum_range_succ, ih]

/--
  **Guarded two-sided bracket (proved, no π hypothesis):**
  `bbpGuardedLo n g ≤ 16^n · bbpSeries < bbpGuardedHi n g + 1`.
-/
theorem bbpGuarded_bracket (n g : ℕ) :
    (bbpGuardedLo n g : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries ∧
      (16 : ℝ) ^ n * bbpSeries < (bbpGuardedHi n g : ℝ) + 1 := by
  have hx := bbpSeries_scaled_split (n + g)
  have ht0 := bbpScaledTail_nonneg (n + g)
  have ht1 := bbpScaledTail_lt_one (n + g)
  obtain ⟨hs1, hs2⟩ := bbpSpigotSum_cast_bounds (n + g) (n + g + 1)
  have hhead :
      bbpScaledHead (n + g) =
        (16 : ℝ) ^ (n + g) * ∑ k ∈ Finset.range (n + g + 1), bbpSummand k := rfl
  have hhead_nn : 0 ≤ bbpScaledHead (n + g) := by
    rw [hhead]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => bbpSummand_nonneg k)
  have hS : bbpGuardedSum n g = bbpSpigotSum (n + g) (n + g + 1) := rfl
  have hE : ((bbpGuardErr n g : ℕ) : ℝ) = 4 * ((n : ℝ) + g + 1) + 2 := by
    simp [bbpGuardErr]
  have hpow : (16 : ℝ) ^ (n + g) = (16 : ℝ) ^ n * (16 : ℝ) ^ g := pow_add _ _ _
  have hg : (0 : ℝ) < (16 : ℝ) ^ g := by positivity
  have hcastK : ((n + g + 1 : ℕ) : ℝ) = (n : ℝ) + g + 1 := by push_cast; ring
  rw [hcastK] at hs1 hs2
  -- lower end
  have hlow :
      ((bbpGuardedSum n g - bbpGuardErr n g : ℕ) : ℝ) ≤ (16 : ℝ) ^ (n + g) * bbpSeries := by
    rcases le_total (bbpGuardErr n g) (bbpGuardedSum n g) with h | h
    · rw [Nat.cast_sub h, hE, hS]
      rw [hhead] at hx
      nlinarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
      linarith
  have hup :
      (16 : ℝ) ^ (n + g) * bbpSeries < ((bbpGuardedSum n g + bbpGuardErr n g : ℕ) : ℝ) := by
    rw [Nat.cast_add, hE, hS]
    rw [hhead] at hx
    nlinarith
  have hlo_nat : bbpGuardedLo n g * 16 ^ g ≤ bbpGuardedSum n g - bbpGuardErr n g :=
    Nat.div_mul_le_self _ _
  have hhi_nat : bbpGuardedSum n g + bbpGuardErr n g < (bbpGuardedHi n g + 1) * 16 ^ g := by
    have h := Nat.lt_div_mul_add (a := bbpGuardedSum n g + bbpGuardErr n g)
      (b := 16 ^ g) (by positivity)
    unfold bbpGuardedHi
    rw [Nat.add_mul, Nat.one_mul]
    exact h
  have hlo_r : (bbpGuardedLo n g : ℝ) * (16 : ℝ) ^ g ≤
      ((bbpGuardedSum n g - bbpGuardErr n g : ℕ) : ℝ) := by exact_mod_cast hlo_nat
  have hhi_r : ((bbpGuardedSum n g + bbpGuardErr n g : ℕ) : ℝ) <
      ((bbpGuardedHi n g : ℝ) + 1) * (16 : ℝ) ^ g := by exact_mod_cast hhi_nat
  rw [hpow] at hlow hup
  constructor
  · have h := hlo_r.trans hlow
    have h' : (bbpGuardedLo n g : ℝ) * (16 : ℝ) ^ g ≤ ((16 : ℝ) ^ n * bbpSeries) * (16 : ℝ) ^ g := by
      linarith
    exact le_of_mul_le_mul_right h' hg
  · have h := hup.trans hhi_r
    have h' : ((16 : ℝ) ^ n * bbpSeries) * (16 : ℝ) ^ g < ((bbpGuardedHi n g : ℝ) + 1) * (16 : ℝ) ^ g := by
      linarith
    exact lt_of_mul_lt_mul_right h' hg.le

/--
  **Exact floor from the guard check (proved, no π hypothesis):** if the guarded ends agree,
  their common value is `⌊16^n · bbpSeries⌋`.
-/
theorem bbpGuarded_floor_eq (n g : ℕ) (h : bbpGuardedLo n g = bbpGuardedHi n g) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ = (bbpGuardedLo n g : ℤ) := by
  obtain ⟨h1, h2⟩ := bbpGuarded_bracket n g
  rw [Int.floor_eq_iff]
  push_cast
  refine ⟨h1, ?_⟩
  rw [h]
  exact h2

/-- Default-guard version: `bbpGuardAgrees n → ⌊16^n · bbpSeries⌋ = bbpCertFloor n`. -/
theorem bbpCertFloor_eq_floor_series (n : ℕ) (h : bbpGuardAgrees n) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ = (bbpCertFloor n : ℤ) :=
  bbpGuarded_floor_eq n (bbpCertGuard n) h

/-- Default-guard two-sided bracket on the series. -/
theorem bbpCertFloor_bracket_series (n : ℕ) (h : bbpGuardAgrees n) :
    (bbpCertFloor n : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries ∧
      (16 : ℝ) ^ n * bbpSeries < (bbpCertFloor n : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := bbpGuarded_bracket n (bbpCertGuard n)
  refine ⟨h1, ?_⟩
  have h' : bbpGuardedHi n (bbpCertGuard n) = bbpCertFloor n := h.symm
  rw [h'] at h2
  exact h2

/-- π version, conditional only on the stated hypothesis `BBPPiEqualsSeries` (the BBP identity). -/
theorem bbpCertFloor_eq_floor_pi (hπ : BBPPiEqualsSeries) (n : ℕ) (h : bbpGuardAgrees n) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloor n : ℤ) := by
  rw [← (hπ : bbpSeries = Real.pi)]
  exact bbpCertFloor_eq_floor_series n h

theorem bbpCertFloor_bracket_pi (hπ : BBPPiEqualsSeries) (n : ℕ) (h : bbpGuardAgrees n) :
    (bbpCertFloor n : ℝ) ≤ (16 : ℝ) ^ n * Real.pi ∧
      (16 : ℝ) ^ n * Real.pi < (bbpCertFloor n : ℝ) + 1 := by
  rw [← (hπ : bbpSeries = Real.pi)]
  exact bbpCertFloor_bracket_series n h

/-! ### Arbitrary summation depth `K ≥ n+g+1` (bridge to the script's `K = n+51`) -/

/-- Terms with `k > N` vanish, so summing further than `N+1` terms changes nothing. -/
theorem bbpSpigotSum_eq_of_ge (N K : ℕ) (hK : N + 1 ≤ K) :
    bbpSpigotSum N K = bbpSpigotSum N (N + 1) := by
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    show bbpSpigotSum N K + bbp_term K N = _
    rw [ih, bbp_term_eq_bbpSpigotTerm, bbpSpigotTerm_eq_zero_of_gt K N (by omega), Nat.add_zero]

/-- The List-based sum used by the generated artifacts equals `bbpSpigotSum`. -/
theorem list_foldl_spigot_eq (N K : ℕ) :
    (List.range K).foldl (fun acc k => acc + bbpSpigotTerm k N) 0 = bbpSpigotSum N K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

/--
  **Guarded bracket at any depth `K ≥ n+g+1`, error budget `4K+2` (proved, no π):**
  `(A - (4K+2))/16^g ≤ 16^n·bbpSeries < (A + (4K+2))/16^g + 1`, `A = ∑_{k<K} bbp_term k (n+g)`.
  This is the "general lemma" the generated `artifacts/PBBP01GuardedWitnesses.lean` refers to.
-/
theorem bbpGuarded_bracket_of_depth (n g K : ℕ) (hK : n + g + 1 ≤ K) :
    (((bbpSpigotSum (n + g) K - (4 * K + 2)) / 16 ^ g : ℕ) : ℝ) ≤ (16 : ℝ) ^ n * bbpSeries ∧
      (16 : ℝ) ^ n * bbpSeries < (((bbpSpigotSum (n + g) K + (4 * K + 2)) / 16 ^ g : ℕ) : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := bbpGuarded_bracket n g
  have hS : bbpSpigotSum (n + g) K = bbpGuardedSum n g := bbpSpigotSum_eq_of_ge _ _ hK
  have hE : bbpGuardErr n g ≤ 4 * K + 2 := by unfold bbpGuardErr; omega
  rw [hS]
  constructor
  · refine le_trans ?_ h1
    have h : (bbpGuardedSum n g - (4 * K + 2)) / 16 ^ g ≤ bbpGuardedLo n g :=
      Nat.div_le_div_right (Nat.sub_le_sub_left hE _)
    exact_mod_cast h
  · refine lt_of_lt_of_le h2 ?_
    have h : bbpGuardedHi n g ≤ (bbpGuardedSum n g + (4 * K + 2)) / 16 ^ g :=
      Nat.div_le_div_right (Nat.add_le_add_left hE _)
    have h' : (bbpGuardedHi n g : ℝ) ≤ (((bbpGuardedSum n g + (4 * K + 2)) / 16 ^ g : ℕ) : ℝ) := by
      exact_mod_cast h
    linarith

end BBPPi
