import Mathlib.Tactic
import BBPPi.Defs
import BBPPi.Guarded
import BBPPi.Identity
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Data.Real.StarOrdered

/-!
# Forced structure of π's hexadecimal digits: runs, gaps, distance and guard need

This file proves, **for every `n`**, four elementary facts about the true hexadecimal digits
`piHexDigit n = ⌊16^n · π⌋ mod 16` (`Normality.lean`, `d₀ = 3`) and chains them together.
Nothing here is statistical: no limits, densities, normality or randomness are used or claimed.
The only analytic input is that `π` is irrational (Mathlib's `irrational_pi`), plus the proved
identity `bbpSeries = π` (`BBPPiIdentity.lean`) for the guard link and the finite certificate.

## Definitions
* `piScaled n = 16^n · π`, `piDist n = min (fract x) (1 - fract x)` = distance from `x` to `ℤ`.
* `ZFBlock n k`: the `k` digits at positions `n+1, …, n+k` are all `0` or all `F` (= 15).
* `piRun n`: the length of the maximal `0`-block or `F`-block starting at position `n+1`
  (`0` if digit `n+1` is neither). Defined with `Nat.find`; the existence proof uses that
  `π` is irrational, so the run is always finite and the definition needs no cap.
* `GuardSufficient n g`: `2·E(n,g) < 16^g · piDist n` with `E(n,g) = bbpGuardErr n g =
  4(n+g+1)+2`, the sufficient condition of `guardAgreesAt_of_dist` (`BBPConditionalAllN.lean`).
  `piNeed n` is the least such `g`.
* `piGapSeq` (from `BBPPi.Defs`): distance to the next hex digit `1` (`0` if none exists).

## Main results (all `n`)
1. `piRun_digit_ne_one`, `piRun_le_piGapSeq`: the run contains no `1`, so
   `piRun n ≤ piGapSeq (n+1)` (whenever some later digit is `1`).
2. Countdown: `piRun_succ` (`2 ≤ piRun n → piRun (n+1) = piRun n - 1`), `piRun_add`,
   `piGapSeq_countdown`, and `piRun_le_inter_one_gap` (a run inside a gap of size `s`
   between two `1`s has length `≤ s - 1`).
3. `piDist_run`: `16^-(piRun n + 1) < piDist n < 16^-(piRun n)`, both strict.
4. `piNeed_bounds`: with `c = Nat.clog 16 (2·E(n, piNeed n)) = ⌈log₁₆ (8n + 8·piNeed n + 12)⌉`,
   `piRun n + c ≤ piNeed n ≤ piRun n + c + 1`.
   `guardedLo_eq_hi_of_need`: the guarded certificate agrees at every depth `g ≥ piNeed n`.
* `forced_chain`: all of the above in one statement; `long_run_forces` the same for any
  lower bound `L ≤ piRun n`.
* `long_gap_short_run`: the converse fails at an explicit position: `piRun 77 = 0` but
  `piGapSeq 78 = 49` (digits 78–127 checked with `decide +kernel` on the BBP certificate).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (see `#print axioms` at the end).
No `sorry`, no `native_decide`.
-/

namespace BBPPi
namespace PiDigitStructure

open Real

/-! ### Scaled π and the floor recurrence -/

/-- `16^n · π`. -/
noncomputable def piScaled (n : ℕ) : ℝ := (16 : ℝ) ^ n * Real.pi

theorem piScaled_pos (n : ℕ) : 0 < piScaled n := by
  unfold piScaled; exact mul_pos (by positivity) Real.pi_pos

theorem piScaled_add (n k : ℕ) : piScaled (n + k) = (16 : ℝ) ^ k * piScaled n := by
  unfold piScaled; rw [pow_add]; ring

/-- The true digit, read as an integer residue of the floor. -/
theorem piHexDigit_cast (m : ℕ) : (piHexDigit m : ℤ) = ⌊piScaled m⌋ % 16 := by
  have h0 : 0 ≤ ⌊piScaled m⌋ := Int.floor_nonneg.mpr (piScaled_pos m).le
  unfold piHexDigit
  rw [Int.natCast_mod]
  unfold piScaled at h0 ⊢
  rw [Int.toNat_of_nonneg h0]
  rfl

theorem piHexDigit_lt (m : ℕ) : piHexDigit m < 16 := Nat.mod_lt _ (by norm_num)

/-- `⌊16^(m+1) π⌋ = 16 ⌊16^m π⌋ + d_{m+1}`. -/
theorem floor_piScaled_succ (m : ℕ) :
    ⌊piScaled (m + 1)⌋ = 16 * ⌊piScaled m⌋ + piHexDigit (m + 1) := by
  set y := piScaled m with hy
  have hs : piScaled (m + 1) = ((16 * ⌊y⌋ : ℤ) : ℝ) + 16 * Int.fract y := by
    rw [show m + 1 = m + 1 from rfl, piScaled_add m 1, ← hy]
    unfold Int.fract; push_cast; ring
  have e : ⌊piScaled (m + 1)⌋ = 16 * ⌊y⌋ + ⌊16 * Int.fract y⌋ := by
    rw [hs, Int.floor_intCast_add]
  have e0 : 0 ≤ ⌊16 * Int.fract y⌋ :=
    Int.floor_nonneg.mpr (by have := Int.fract_nonneg y; positivity)
  have e1 : ⌊16 * Int.fract y⌋ < 16 := by
    rw [Int.floor_lt]; push_cast
    have := Int.fract_lt_one y; linarith
  have hd := piHexDigit_cast (m + 1)
  rw [e] at hd ⊢
  omega

/-! ### The tail integer `T(n,k) = ⌊16^k · fract(16^n π)⌋` -/

/-- `T(n,k) = ⌊16^(n+k) π⌋ - 16^k ⌊16^n π⌋`: the integer spelled by digits `n+1, …, n+k`. -/
noncomputable def tailInt (n k : ℕ) : ℤ := ⌊piScaled (n + k)⌋ - 16 ^ k * ⌊piScaled n⌋

theorem tailInt_zero (n : ℕ) : tailInt n 0 = 0 := by simp [tailInt]

theorem tailInt_succ (n k : ℕ) :
    tailInt n (k + 1) = 16 * tailInt n k + piHexDigit (n + 1 + k) := by
  unfold tailInt
  rw [show n + (k + 1) = (n + k) + 1 from rfl, floor_piScaled_succ,
    show n + k + 1 = n + 1 + k by omega, pow_succ]
  ring

theorem tailInt_eq_floor (n k : ℕ) :
    tailInt n k = ⌊(16 : ℝ) ^ k * Int.fract (piScaled n)⌋ := by
  have h : piScaled (n + k) =
      (((16 : ℤ) ^ k * ⌊piScaled n⌋ : ℤ) : ℝ) + (16 : ℝ) ^ k * Int.fract (piScaled n) := by
    rw [piScaled_add]; unfold Int.fract; push_cast; ring
  unfold tailInt; rw [h, Int.floor_intCast_add]; ring

theorem tailInt_bounds (n k : ℕ) : 0 ≤ tailInt n k ∧ tailInt n k ≤ 16 ^ k - 1 := by
  rw [tailInt_eq_floor]
  have f0 := Int.fract_nonneg (piScaled n)
  have f1 := Int.fract_lt_one (piScaled n)
  have hp : (0 : ℝ) < 16 ^ k := by positivity
  refine ⟨Int.floor_nonneg.mpr (by positivity), ?_⟩
  have : ⌊(16 : ℝ) ^ k * Int.fract (piScaled n)⌋ < 16 ^ k := by
    rw [Int.floor_lt]; push_cast; nlinarith
  omega

/-! ### 0/F blocks -/

/-- Digits `n+1, …, n+k` are all `0` or all `F`. -/
def ZFBlock (n k : ℕ) : Prop :=
  (∀ j < k, piHexDigit (n + 1 + j) = 0) ∨ (∀ j < k, piHexDigit (n + 1 + j) = 15)

theorem forall_lt_succ_iff {P : ℕ → Prop} {k : ℕ} :
    (∀ j < k + 1, P j) ↔ (∀ j < k, P j) ∧ P k := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h1 j hj
    · exact h2

theorem zeros_iff_tailInt (n k : ℕ) :
    (∀ j < k, piHexDigit (n + 1 + j) = 0) ↔ tailInt n k = 0 := by
  induction k with
  | zero => simp [tailInt_zero]
  | succ k ih =>
    rw [forall_lt_succ_iff, ih, tailInt_succ]
    have := (tailInt_bounds n k).1
    omega

theorem fs_iff_tailInt (n k : ℕ) :
    (∀ j < k, piHexDigit (n + 1 + j) = 15) ↔ tailInt n k = 16 ^ k - 1 := by
  induction k with
  | zero => simp [tailInt_zero]
  | succ k ih =>
    rw [forall_lt_succ_iff, ih, tailInt_succ, pow_succ]
    have := (tailInt_bounds n k).2
    have := piHexDigit_lt (n + 1 + k)
    omega

/-! ### Irrationality and the distance to `ℤ` -/

/-- `16^k · fract(16^n π)` is never an integer (π is irrational). -/
theorem pow_mul_fract_ne_int (n k : ℕ) (a : ℤ) :
    (16 : ℝ) ^ k * Int.fract (piScaled n) ≠ a := by
  intro h
  apply irrational_pi
  refine ⟨((a + 16 ^ k * ⌊piScaled n⌋ : ℤ) : ℚ) / (16 : ℚ) ^ (k + n), ?_⟩
  push_cast
  rw [div_eq_iff (by positivity), pow_add]
  unfold Int.fract at h
  unfold piScaled at h ⊢
  linear_combination -h

/-- Distance from `16^n π` to the nearest integer. -/
noncomputable def piDist (n : ℕ) : ℝ := min (Int.fract (piScaled n)) (1 - Int.fract (piScaled n))

theorem fract_pos (n : ℕ) : 0 < Int.fract (piScaled n) := by
  rcases (Int.fract_nonneg (piScaled n)).lt_or_eq with h | h
  · exact h
  · exact absurd (by rw [← h]; simp) (pow_mul_fract_ne_int n 0 0)

theorem piDist_pos (n : ℕ) : 0 < piDist n := by
  unfold piDist
  have := fract_pos n; have := Int.fract_lt_one (piScaled n)
  exact lt_min (by linarith) (by linarith)

/-- `piDist n ≤ |16^n π − m|` for every integer `m`. -/
theorem piDist_le_abs (n : ℕ) (m : ℤ) : piDist n ≤ |piScaled n - m| := by
  unfold piDist
  have hf : Int.fract (piScaled n) = piScaled n - ⌊piScaled n⌋ := rfl
  rcases le_or_gt m ⌊piScaled n⌋ with hm | hm
  · have hm' : (m : ℝ) ≤ ⌊piScaled n⌋ := by exact_mod_cast hm
    exact (min_le_left _ _).trans (by rw [hf]; exact le_abs.mpr (Or.inl (by linarith)))
  · have hm' : (⌊piScaled n⌋ : ℝ) + 1 ≤ m := by exact_mod_cast hm
    exact (min_le_right _ _).trans (by rw [hf]; exact le_abs.mpr (Or.inr (by linarith)))

/-- `16^k · piDist n ≠ 1` (irrationality). -/
theorem pow_mul_piDist_ne_one (n k : ℕ) : (16 : ℝ) ^ k * piDist n ≠ 1 := by
  unfold piDist
  rcases min_choice (Int.fract (piScaled n)) (1 - Int.fract (piScaled n)) with h | h <;>
    rw [h]
  · exact_mod_cast pow_mul_fract_ne_int n k 1
  · intro h1
    apply pow_mul_fract_ne_int n k (16 ^ k - 1)
    push_cast; linarith

/-- **Block ↔ distance.** Digits `n+1..n+k` are all `0` or all `F` iff `16^k · dist < 1`. -/
theorem zfBlock_iff_dist (n k : ℕ) : ZFBlock n k ↔ (16 : ℝ) ^ k * piDist n < 1 := by
  set f := Int.fract (piScaled n) with hf
  have f0 := Int.fract_nonneg (piScaled n)
  have f1 := Int.fract_lt_one (piScaled n)
  have hP : (0 : ℝ) < 16 ^ k := by positivity
  have hT := tailInt_eq_floor n k
  rw [← hf] at hT
  have hz : tailInt n k = 0 ↔ (16 : ℝ) ^ k * f < 1 := by
    rw [hT, Int.floor_eq_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨by positivity, h⟩⟩
  have hF : tailInt n k = 16 ^ k - 1 ↔ (16 : ℝ) ^ k - 1 ≤ (16 : ℝ) ^ k * f := by
    rw [hT, Int.floor_eq_iff]; push_cast
    exact ⟨fun h => h.1, fun h => ⟨h, by nlinarith⟩⟩
  unfold ZFBlock
  rw [zeros_iff_tailInt, fs_iff_tailInt, hz, hF]
  unfold piDist; rw [← hf]
  constructor
  · rintro (h | h)
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_left _ _) hP.le) h
    · have hne : (16 : ℝ) ^ k * f ≠ ((16 ^ k - 1 : ℤ) : ℝ) := pow_mul_fract_ne_int n k _
      push_cast at hne
      have : (16 : ℝ) ^ k - 1 < 16 ^ k * f := lt_of_le_of_ne h (Ne.symm hne)
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_right _ _) hP.le) ?_
      linarith
  · intro h
    rcases min_choice f (1 - f) with hm | hm <;> rw [hm] at h
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem zfBlock_zero (n : ℕ) : ZFBlock n 0 := Or.inl (fun j hj => absurd hj (Nat.not_lt_zero j))

theorem zfBlock_mono {n k j : ℕ} (h : ZFBlock n k) (hjk : j ≤ k) : ZFBlock n j := by
  rcases h with h | h
  · exact Or.inl fun i hi => h i (by omega)
  · exact Or.inr fun i hi => h i (by omega)

/-- Every block ends: some `k` has digits `n+1..n+k+1` not all `0`/`F` (π irrational). -/
theorem exists_not_zfBlock (n : ℕ) : ∃ k, ¬ ZFBlock n (k + 1) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / piDist n) (by norm_num : (1 : ℝ) < 16)
  have hd := piDist_pos n
  refine ⟨k, fun hb => ?_⟩
  have h1 := (zfBlock_iff_dist n k).mp (zfBlock_mono hb (Nat.le_succ k))
  rw [div_lt_iff₀ hd] at hk
  linarith

/-! ### The run length -/

open Classical in
/-- **Run length** at `n`: the length of the maximal block of `0`s or of `F`s starting at
digit `n+1` (`0` if digit `n+1` is neither). Always finite because `π` is irrational. -/
noncomputable def piRun (n : ℕ) : ℕ := Nat.find (exists_not_zfBlock n)

theorem zfBlock_iff_le_piRun (n k : ℕ) : ZFBlock n k ↔ k ≤ piRun n := by
  classical
  have hspec : ¬ ZFBlock n (piRun n + 1) := by
    have := Nat.find_spec (exists_not_zfBlock n); unfold piRun; convert this
  have hrun : ZFBlock n (piRun n) := by
    rcases hr : piRun n with _ | m
    · exact zfBlock_zero n
    · have hlt : m < Nat.find (exists_not_zfBlock n) := by
        have : piRun n = Nat.find (exists_not_zfBlock n) := by unfold piRun; congr
        omega
      exact not_not.mp (Nat.find_min (exists_not_zfBlock n) hlt)
  constructor
  · intro h; by_contra hk; exact hspec (zfBlock_mono h (by omega))
  · intro h; exact zfBlock_mono hrun h

theorem zfBlock_piRun (n : ℕ) : ZFBlock n (piRun n) := (zfBlock_iff_le_piRun n _).mpr le_rfl

theorem not_zfBlock_piRun_succ (n : ℕ) : ¬ ZFBlock n (piRun n + 1) := by
  rw [zfBlock_iff_le_piRun]; omega

/-! ### Fact 1: the run contains no digit `1`, so it is bounded by the gap -/

theorem piRun_digit_ne_one {n j : ℕ} (hj : j < piRun n) : piHexDigit (n + 1 + j) ≠ 1 := by
  rcases zfBlock_piRun n with h | h <;> rw [h j hj] <;> norm_num

/-- If digit `m > n` is `1`, the run at `n` stops before it. -/
theorem piRun_le_of_digit_eq_one {n m : ℕ} (hm : piHexDigit m = 1) (hnm : n < m) :
    piRun n ≤ m - (n + 1) := by
  by_contra h
  exact piRun_digit_ne_one (n := n) (j := m - (n + 1)) (by omega)
    (by rw [show n + 1 + (m - (n + 1)) = m by omega]; exact hm)

/-- **Fact 1.** `piRun n ≤ piGapSeq (n+1)` whenever some digit after `n` is `1`. -/
theorem piRun_le_piGapSeq {n : ℕ} (h : ∃ k, piHexDigit (n + 1 + k) = 1) :
    piRun n ≤ piGapSeq (n + 1) := by
  classical
  unfold piGapSeq
  rw [dif_pos h]
  have hs := Nat.find_spec h
  have := piRun_le_of_digit_eq_one (n := n) (m := n + 1 + Nat.find h) hs (by omega)
  omega

/-! ### Fact 2: countdown -/

theorem zfBlock_shift {n k : ℕ} (h : ZFBlock n (k + 1)) : ZFBlock (n + 1) k := by
  rcases h with h | h
  · exact Or.inl fun j hj => by rw [show n + 1 + 1 + j = n + 1 + (j + 1) by omega]; exact h _ (by omega)
  · exact Or.inr fun j hj => by rw [show n + 1 + 1 + j = n + 1 + (j + 1) by omega]; exact h _ (by omega)

/-- **Run countdown.** -/
theorem piRun_succ {n : ℕ} (h : 2 ≤ piRun n) : piRun (n + 1) = piRun n - 1 := by
  set K := piRun n with hK
  have hle : K - 1 ≤ piRun (n + 1) := by
    rw [← zfBlock_iff_le_piRun]
    apply zfBlock_shift
    rw [show K - 1 + 1 = K by omega]; exact zfBlock_piRun n
  have hlt : ¬ ZFBlock (n + 1) K := by
    intro h1
    apply not_zfBlock_piRun_succ n
    rw [← hK]
    have h0 := zfBlock_piRun n
    rw [← hK] at h0
    have e : ∀ j, n + 1 + 1 + j = n + 1 + (j + 1) := fun j => by omega
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · refine Or.inl fun j hj => ?_
      rcases j with _ | j
      · exact h0 0 (by omega)
      · have := h1 j (by omega); rwa [e] at this
    · have a := h0 1 (by omega); have b := h1 0 (by omega)
      rw [e] at b; rw [b] at a; norm_num at a
    · have a := h0 1 (by omega); have b := h1 0 (by omega)
      rw [e] at b; rw [b] at a; norm_num at a
    · refine Or.inr fun j hj => ?_
      rcases j with _ | j
      · exact h0 0 (by omega)
      · have := h1 j (by omega); rwa [e] at this
  have : piRun (n + 1) < K := by
    by_contra hc; exact hlt ((zfBlock_iff_le_piRun _ _).mpr (by omega))
  omega

/-- Iterated countdown: inside a run of length `K`, the run at offset `j < K` is `K - j`. -/
theorem piRun_add {n j : ℕ} (h : j < piRun n) : piRun (n + j) = piRun n - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih' := ih (by omega)
    rw [show n + (j + 1) = (n + j) + 1 by omega, piRun_succ (by omega), ih']
    omega

/-- Gap countdown: the recursion for `piGapSeq` away from a digit `1`. -/
theorem piGapSeq_countdown (i : ℕ) (hi : piHexDigit i ≠ 1)
    (h : ∃ k, piHexDigit (i + 1 + k) = 1) : piGapSeq i = piGapSeq (i + 1) + 1 := by
  classical
  have h0 : ∃ k, piHexDigit (i + k) = 1 := by
    obtain ⟨k, hk⟩ := h; exact ⟨k + 1, by rwa [show i + (k + 1) = i + 1 + k by ring]⟩
  unfold piGapSeq; rw [dif_pos h0, dif_pos h]
  have hpos : Nat.find h0 ≠ 0 := by
    intro hz; have := Nat.find_spec h0; rw [hz] at this; simp at this; exact hi this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have e1 : Nat.find h0 ≤ Nat.find h + 1 := Nat.find_min' h0 (by
    have := Nat.find_spec h
    rwa [show i + 1 + Nat.find h = i + (Nat.find h + 1) by ring] at this)
  have e2 : Nat.find h ≤ j := Nat.find_min' h (by
    have := Nat.find_spec h0
    rw [hj] at this
    rwa [show i + j.succ = i + 1 + j by omega] at this)
  omega

/-- A `0`/`F` run starting inside a gap of size `s` (positions `a+1..a+s`, with digit
`a + s = 1`) has length at most `s - 1`. -/
theorem piRun_le_inter_one_gap {a s n : ℕ} (han : a ≤ n) (hns : n < a + s)
    (h1 : piHexDigit (a + s) = 1) : piRun n ≤ s - 1 := by
  have := piRun_le_of_digit_eq_one h1 hns
  omega

/-! ### Fact 3: the run pins the distance to `ℤ` -/

/-- **Fact 3 (multiplicative form).** `16^run · dist < 1 < 16^(run+1) · dist`. -/
theorem piDist_run_mul (n : ℕ) :
    (16 : ℝ) ^ piRun n * piDist n < 1 ∧ 1 < (16 : ℝ) ^ (piRun n + 1) * piDist n := by
  refine ⟨(zfBlock_iff_dist n _).mp (zfBlock_piRun n), ?_⟩
  have h := not_zfBlock_piRun_succ n
  rw [zfBlock_iff_dist, not_lt] at h
  exact lt_of_le_of_ne h (Ne.symm (pow_mul_piDist_ne_one n _))

/-- **Fact 3.** `16^-(run+1) < dist(16^n π, ℤ) < 16^-run`, both strict. -/
theorem piDist_run (n : ℕ) :
    1 / (16 : ℝ) ^ (piRun n + 1) < piDist n ∧ piDist n < 1 / (16 : ℝ) ^ piRun n := by
  obtain ⟨h1, h2⟩ := piDist_run_mul n
  constructor
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; linarith

/-- Which side: a nonempty `0`-run means `16^n π` sits just above an integer, an `F`-run
just below one. -/
theorem piRun_pos_cases {n : ℕ} (h : 1 ≤ piRun n) :
    (piHexDigit (n + 1) = 0 ∧ piDist n = Int.fract (piScaled n)) ∨
      (piHexDigit (n + 1) = 15 ∧ piDist n = 1 - Int.fract (piScaled n)) := by
  have hb := (zfBlock_iff_le_piRun n 1).mpr h
  have hT := tailInt_eq_floor n 1
  have f0 := Int.fract_nonneg (piScaled n)
  have f1 := Int.fract_lt_one (piScaled n)
  unfold piDist
  rcases hb with hb | hb
  · have hz := (zeros_iff_tailInt n 1).mp hb
    rw [hT, Int.floor_eq_zero_iff] at hz
    have : Int.fract (piScaled n) ≤ 1 - Int.fract (piScaled n) := by
      have := hz.2; simp at this; linarith
    exact Or.inl ⟨by simpa using hb 0 (by omega), min_eq_left this⟩
  · have hz := (fs_iff_tailInt n 1).mp hb
    rw [hT, Int.floor_eq_iff] at hz
    have : 1 - Int.fract (piScaled n) ≤ Int.fract (piScaled n) := by
      have := hz.1; push_cast at this; linarith
    exact Or.inr ⟨by simpa using hb 0 (by omega), min_eq_right this⟩

/-! ### The guard link (re-proved from `BBPConditionalAllN.lean` without its imports) -/

/-- `|16^(n+g)·π − S| ≤ E` (copy of `guardedSum_close`, `BBPConditionalAllN.lean`). -/
theorem guardedSum_close_pi (n g : ℕ) :
    |(16 : ℝ) ^ (n + g) * Real.pi - (bbpGuardedSum n g : ℝ)| ≤ (bbpGuardErr n g : ℝ) := by
  have hx := bbpSeries_scaled_split (n + g)
  have ht0 := bbpScaledTail_nonneg (n + g)
  have ht1 := bbpScaledTail_lt_one (n + g)
  obtain ⟨hs1, hs2⟩ := bbpSpigotSum_cast_bounds (n + g) (n + g + 1)
  have hhead : bbpScaledHead (n + g) =
      (16 : ℝ) ^ (n + g) * ∑ k ∈ Finset.range (n + g + 1), bbpSummand k := rfl
  have hS : bbpGuardedSum n g = bbpSpigotSum (n + g) (n + g + 1) := rfl
  have hE : ((bbpGuardErr n g : ℕ) : ℝ) = 4 * ((n : ℝ) + g + 1) + 2 := by
    simp [bbpGuardErr]
  have hcastK : ((n + g + 1 : ℕ) : ℝ) = (n : ℝ) + g + 1 := by push_cast; ring
  rw [hcastK] at hs1 hs2
  rw [← bbpSeries_eq_pi, hS, hE, abs_le]
  rw [hhead] at hx
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hg : (0:ℝ) ≤ g := Nat.cast_nonneg g
  constructor <;> linarith

/-- Sufficient condition for the guarded certificate to agree at `(n, g)`
(copy of `guardAgreesAt_of_dist`, `BBPConditionalAllN.lean`; the conclusion
`bbpGuardedLo n g = bbpGuardedHi n g` is `BBPGuardAgreesAt n g`). -/
theorem guardedLo_eq_hi_of_dist {n g : ℕ}
    (h : ∀ m : ℤ, 2 * (bbpGuardErr n g : ℝ) < (16 : ℝ) ^ g * |(16 : ℝ) ^ n * Real.pi - m|) :
    bbpGuardedLo n g = bbpGuardedHi n g := by
  by_contra hne
  set S := bbpGuardedSum n g with hS
  set E := bbpGuardErr n g with hE
  set M := 16 ^ g with hM
  have hMpos : 0 < M := by positivity
  have hle : bbpGuardedLo n g ≤ bbpGuardedHi n g :=
    Nat.div_le_div_right (by omega : S - E ≤ S + E)
  have hlt : bbpGuardedLo n g + 1 ≤ bbpGuardedHi n g := by omega
  have h1 : bbpGuardedHi n g * M ≤ S + E := Nat.div_mul_le_self _ _
  have h2 : S - E < (bbpGuardedLo n g + 1) * M := by
    have := Nat.lt_div_mul_add (a := S - E) (b := M) hMpos
    unfold bbpGuardedLo; rw [Nat.add_mul, Nat.one_mul]; exact this
  have h3 : (bbpGuardedLo n g + 1) * M ≤ bbpGuardedHi n g * M := Nat.mul_le_mul_right _ hlt
  set m : ℤ := (bbpGuardedHi n g : ℤ) with hm
  have hclose := guardedSum_close_pi n g
  rw [← hS, ← hE] at hclose
  have hMr : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
  have hMc : (M:ℝ) = (16:ℝ)^g := by rw [hM]; push_cast; rfl
  have r1 : ((bbpGuardedHi n g : ℕ) : ℝ) * M ≤ (S:ℝ) + E := by exact_mod_cast h1
  have r2 : (S:ℝ) < E + ((bbpGuardedHi n g : ℕ) : ℝ) * M := by
    have : S < E + bbpGuardedHi n g * M := by omega
    exact_mod_cast this
  have hpow : (16:ℝ)^(n+g) = (16:ℝ)^n * (16:ℝ)^g := pow_add _ _ _
  have key := h m
  have hmr : (m:ℝ) = ((bbpGuardedHi n g : ℕ) : ℝ) := by rw [hm]; simp
  rw [hmr, ← hMc] at key
  rw [hpow] at hclose
  rw [abs_le] at hclose
  have : (M:ℝ) * |(16:ℝ)^n * Real.pi - ((bbpGuardedHi n g : ℕ) : ℝ)| =
      |(16:ℝ)^n * Real.pi * M - ((bbpGuardedHi n g : ℕ) : ℝ) * M| := by
    rw [← abs_of_pos hMr, ← abs_mul, abs_of_pos hMr]; congr 1; ring
  rw [this] at key
  have hE2 : (0:ℝ) ≤ E := Nat.cast_nonneg _
  have : |(16:ℝ)^n * Real.pi * M - ((bbpGuardedHi n g : ℕ) : ℝ) * M| ≤ 2 * E := by
    rw [abs_le]
    obtain ⟨c1, c2⟩ := hclose
    constructor <;> nlinarith
  linarith

/-! ### Fact 4: the minimal guard is pinned by the run -/

/-- The sufficient guard condition `2·E(n,g) < 16^g · dist(16^n π, ℤ)`. -/
def GuardSufficient (n g : ℕ) : Prop := 2 * (bbpGuardErr n g : ℝ) < (16 : ℝ) ^ g * piDist n

theorem two_guardErr (n g : ℕ) : 2 * bbpGuardErr n g = 8 * n + 8 * g + 12 := by
  unfold bbpGuardErr; ring

theorem guardSufficient_succ {n g : ℕ} (h : GuardSufficient n g) : GuardSufficient n (g + 1) := by
  unfold GuardSufficient at *
  have e : (bbpGuardErr n (g + 1) : ℝ) = bbpGuardErr n g + 4 := by
    unfold bbpGuardErr; push_cast; ring
  have e6 : (6 : ℝ) ≤ bbpGuardErr n g := by
    exact_mod_cast (show 6 ≤ bbpGuardErr n g by unfold bbpGuardErr; omega)
  rw [e, pow_succ]
  nlinarith

theorem guardSufficient_mono {n g g' : ℕ} (h : GuardSufficient n g) (hg : g ≤ g') :
    GuardSufficient n g' := by
  induction hg with
  | refl => exact h
  | step _ ih => exact guardSufficient_succ ih

theorem nine_mul_le_pow (M : ℕ) (hM : 1 ≤ M) : 9 * M < 16 ^ M := by
  have h := Nat.lt_pow_self (n := M - 1) (show 1 < 16 by norm_num)
  have : 16 ^ M = 16 * 16 ^ (M - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem exists_guardSufficient (n : ℕ) : ∃ g, GuardSufficient n g := by
  set k := piRun n
  set G := 8 * n + 8 * k + 40
  refine ⟨k + 1 + G, ?_⟩
  have key : ∀ M : ℕ, 8 * n + 8 * k + 40 ≤ M → 2 * bbpGuardErr n (k + 1 + M) < 16 ^ M := by
    intro M hM; rw [two_guardErr]; have := nine_mul_le_pow M (by omega); omega
  have hN : 2 * bbpGuardErr n (k + 1 + G) < 16 ^ G := key G le_rfl
  have hR : (2 * (bbpGuardErr n (k + 1 + G) : ℝ)) < (16 : ℝ) ^ G := by exact_mod_cast hN
  have h1 := (piDist_run_mul n).2
  unfold GuardSufficient
  rw [show k + 1 + G = G + (k + 1) by omega, pow_add, mul_assoc]
  rw [show k + 1 + G = G + (k + 1) by omega] at hR
  have : (16 : ℝ) ^ G < (16 : ℝ) ^ G * ((16 : ℝ) ^ (k + 1) * piDist n) :=
    lt_mul_of_one_lt_right (by positivity) h1
  linarith

open Classical in
/-- **Need** at `n`: the least guard depth satisfying the sufficient condition. -/
noncomputable def piNeed (n : ℕ) : ℕ := Nat.find (exists_guardSufficient n)

theorem guardSufficient_iff (n g : ℕ) : GuardSufficient n g ↔ piNeed n ≤ g := by
  classical
  constructor
  · intro h; unfold piNeed; exact Nat.find_min' _ h
  · intro h; apply guardSufficient_mono _ h
    have := Nat.find_spec (exists_guardSufficient n); unfold piNeed; convert this

/-- The guarded certificate agrees at every depth from `piNeed n` on. -/
theorem guardedLo_eq_hi_of_need {n g : ℕ} (hg : piNeed n ≤ g) :
    bbpGuardedLo n g = bbpGuardedHi n g := by
  apply guardedLo_eq_hi_of_dist
  intro m
  have h := (guardSufficient_iff n g).mpr hg
  unfold GuardSufficient at h
  refine lt_of_lt_of_le h (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact piDist_le_abs n m

/-- **Fact 4.** With `c = Nat.clog 16 (2·E(n, piNeed n)) = ⌈log₁₆ (8n + 8·piNeed n + 12)⌉`,
`piRun n + c ≤ piNeed n ≤ piRun n + c + 1`. -/
theorem piNeed_bounds (n : ℕ) :
    piRun n + Nat.clog 16 (2 * bbpGuardErr n (piNeed n)) ≤ piNeed n ∧
      piNeed n ≤ piRun n + Nat.clog 16 (2 * bbpGuardErr n (piNeed n)) + 1 := by
  set r := piNeed n with hr
  set k := piRun n with hk
  set c := Nat.clog 16 (2 * bbpGuardErr n r) with hc
  have hd := piDist_pos n
  obtain ⟨hlo, hhi⟩ := piDist_run_mul n
  rw [← hk] at hlo hhi
  constructor
  · -- lower bound from `GuardSufficient n r` and `16^k · dist < 1`
    have hg : GuardSufficient n r := (guardSufficient_iff n r).mpr le_rfl
    unfold GuardSufficient at hg
    have hR : (2 * (bbpGuardErr n r : ℝ)) * (16 : ℝ) ^ k < (16 : ℝ) ^ r := by
      have : (16 : ℝ) ^ r * piDist n * (16 : ℝ) ^ k < (16 : ℝ) ^ r := by
        rw [mul_assoc, mul_comm (piDist n)]
        exact mul_lt_of_lt_one_right (by positivity) hlo
      nlinarith [pow_pos (show (0:ℝ) < 16 by norm_num) k]
    have hN : 2 * bbpGuardErr n r * 16 ^ k < 16 ^ r := by exact_mod_cast hR
    have hE1 : 1 ≤ 2 * bbpGuardErr n r := by rw [two_guardErr]; omega
    have hkr : k ≤ r := by
      have : 16 ^ k < 16 ^ r := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hE1) hN
      exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp this).le
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkr
    have hpow : (16 : ℕ) ^ r = 16 ^ j * 16 ^ k := by rw [hj, pow_add, mul_comm]
    rw [hpow] at hN
    have hN' : 2 * bbpGuardErr n r < 16 ^ j := Nat.lt_of_mul_lt_mul_right hN
    have : c ≤ j := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hN'.le
    omega
  · -- upper bound from `¬ GuardSufficient n (r-1)` and `1 < 16^(k+1) · dist`
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · omega
    obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hng : ¬ GuardSufficient n s := by rw [guardSufficient_iff]; omega
    unfold GuardSufficient at hng; rw [not_lt] at hng
    have hR : (16 : ℝ) ^ s < 2 * (bbpGuardErr n s : ℝ) * (16 : ℝ) ^ (k + 1) := by
      have : (16 : ℝ) ^ s < (16 : ℝ) ^ s * ((16 : ℝ) ^ (k + 1) * piDist n) :=
        lt_mul_of_one_lt_right (by positivity) hhi
      have h2 : (16 : ℝ) ^ s * piDist n * (16 : ℝ) ^ (k + 1) ≤
          2 * (bbpGuardErr n s : ℝ) * (16 : ℝ) ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hng (by positivity)
      nlinarith
    have hN : 16 ^ s < 2 * bbpGuardErr n s * 16 ^ (k + 1) := by exact_mod_cast hR
    by_contra hcon
    have hsk : k + 1 + c ≤ s := by omega
    have hpc : 2 * bbpGuardErr n r ≤ 16 ^ c := Nat.le_pow_clog (by norm_num) _
    have hEs : 2 * bbpGuardErr n s ≤ 2 * bbpGuardErr n r := by
      rw [two_guardErr, two_guardErr]; omega
    have : 16 ^ (k + 1 + c) ≤ 16 ^ s := Nat.pow_le_pow_right (by norm_num) hsk
    rw [pow_add] at this
    have : 2 * bbpGuardErr n s * 16 ^ (k + 1) ≤ 16 ^ (k + 1) * 16 ^ c := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (hEs.trans hpc)
    omega

/-! ### Fitting the four facts together -/

/-- **The forced chain.** For every `n`, with `k = piRun n` and `r = piNeed n`:
* the run contains no `1`, so (if a later `1` exists) `k ≤ piGapSeq (n+1)`;
* the run pins the distance: `16^-(k+1) < dist(16^n π, ℤ) < 16^-k`;
* the run pins the need: `k + c ≤ r ≤ k + c + 1`, `c = ⌈log₁₆ (8n + 8r + 12)⌉`;
* the guarded certificate agrees at every depth `g ≥ r`. -/
theorem forced_chain (n : ℕ) :
    (∀ j < piRun n, piHexDigit (n + 1 + j) ≠ 1) ∧
    ((∃ k, piHexDigit (n + 1 + k) = 1) → piRun n ≤ piGapSeq (n + 1)) ∧
    (1 / (16 : ℝ) ^ (piRun n + 1) < piDist n ∧ piDist n < 1 / (16 : ℝ) ^ piRun n) ∧
    (piRun n + Nat.clog 16 (2 * bbpGuardErr n (piNeed n)) ≤ piNeed n ∧
      piNeed n ≤ piRun n + Nat.clog 16 (2 * bbpGuardErr n (piNeed n)) + 1) ∧
    (∀ g, piNeed n ≤ g → bbpGuardedLo n g = bbpGuardedHi n g) :=
  ⟨fun _ hj => piRun_digit_ne_one hj, piRun_le_piGapSeq, piDist_run n, piNeed_bounds n,
    fun _ hg => guardedLo_eq_hi_of_need hg⟩

/-- **A long run forces everything.** If `L ≤ piRun n` then digits `n+1..n+L` contain no `1`
(so the gap is `≥ L` when a later `1` exists), `dist(16^n π, ℤ) < 16^-L`, and
`piNeed n ≥ L + ⌈log₁₆ (8n + 8·piNeed n + 12)⌉`. -/
theorem long_run_forces {n L : ℕ} (hL : L ≤ piRun n) :
    (∀ j < L, piHexDigit (n + 1 + j) ≠ 1) ∧
    ((∃ k, piHexDigit (n + 1 + k) = 1) → L ≤ piGapSeq (n + 1)) ∧
    piDist n < 1 / (16 : ℝ) ^ L ∧
    L + Nat.clog 16 (2 * bbpGuardErr n (piNeed n)) ≤ piNeed n := by
  obtain ⟨h1, h2, ⟨_, h3⟩, ⟨h4, _⟩, _⟩ := forced_chain n
  refine ⟨fun j hj => h1 j (by omega), fun h => (hL.trans (h2 h)), ?_, by omega⟩
  refine lt_of_lt_of_le h3 ?_
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hL)

/-! ### The converse fails: a long gap with no run (explicit, kernel-checked) -/

/-- Certificate digits equal true digits whenever the decidable guard check passes. -/
theorem piHexDigit_eq_cert {m : ℕ} (h : bbpGuardAgrees m) : piHexDigit m = bbpCertFloor m % 16 := by
  unfold piHexDigit
  rw [← bbpSeries_eq_pi, bbpCertFloor_eq_floor_series m h]
  simp

/-- Kernel-checked digits 78–127 of π (hex): `3` at 78, no `1` in 78–126, `1` at 127. -/
theorem cert_78_127 :
    (∀ j < 50, bbpGuardAgrees (78 + j)) ∧
    (∀ j < 49, bbpCertFloor (78 + j) % 16 ≠ 1) ∧
    bbpCertFloor 127 % 16 = 1 ∧ bbpCertFloor 78 % 16 = 3 := by
  decide +kernel

/-- **The converse fails.** At `n = 77` the run is `0` (digit 78 is `3`), yet the gap from
position 78 to the next `1` is `49`. So a long gap does not force a run, a small distance
or a large need: the implication in `forced_chain` goes one way only. -/
theorem long_gap_short_run : piRun 77 = 0 ∧ piGapSeq 78 = 49 := by
  classical
  obtain ⟨hg, hne, h127, h78⟩ := cert_78_127
  have d : ∀ j < 50, piHexDigit (78 + j) = bbpCertFloor (78 + j) % 16 :=
    fun j hj => piHexDigit_eq_cert (hg j hj)
  constructor
  · have hb : ¬ ZFBlock 77 1 := by
      have e := d 0 (by norm_num)
      simp only [Nat.add_zero] at e
      rintro (h | h) <;> have := h 0 (by norm_num) <;>
        rw [show (77 : ℕ) + 1 + 0 = 78 from rfl] at this <;> omega
    rw [zfBlock_iff_le_piRun] at hb; omega
  · have e127 := d 49 (by norm_num)
    rw [show (78 : ℕ) + 49 = 127 from rfl] at e127
    have h1 : piHexDigit (78 + 49) = 1 := by
      rw [show (78 : ℕ) + 49 = 127 from rfl, e127]; exact h127
    have hex : ∃ k, piHexDigit (78 + k) = 1 := ⟨49, h1⟩
    unfold piGapSeq
    rw [dif_pos hex, Nat.find_eq_iff]
    exact ⟨h1, fun j hj => by rw [d j (by omega)]; exact hne j hj⟩

end PiDigitStructure
end BBPPi
