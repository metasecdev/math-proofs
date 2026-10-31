import BBPPi.ExplicitGuard

/-!
# Conditional all-`n` digit correctness theorem from a π irrationality-measure hypothesis

* It is `sorry`-free. The axioms used are exactly `propext`, `Classical.choice`, `Quot.sound`
  (see `BBPPi/Axioms.lean`).
* The hypothesis `PiEffectiveMeasure` (an effective irrationality measure for π,
  `|π - p/q| ≥ C / q^μ` for all `q ≥ 2`) is a hypothesis in this file.
  Every `*_all_n` theorem below is conditional on it (or on the weaker `PiPow16Measure`,
  restricted to `q = 16^n`). The hypothesis is discharged for `q = 16^n` in `BBPPi.UnconditionalAllN`, `BBPPi.Mu658`
  and `BBPPi.Mu570`.
* Includes the sharper guard depth `gfun'` with slope `μ - 1` plus a `log` term.

-/

namespace BBPPi
open Real

/-! ### 0. Monotonicity (cheap): `(n+1, g-1)` ⇒ `(n, g)` -/

theorem BBPGuardAgreesAt.of_succ_pred {n g : ℕ} (hg : 1 ≤ g)
    (h : BBPGuardAgreesAt (n + 1) (g - 1)) : BBPGuardAgreesAt n g := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  unfold BBPGuardAgreesAt bbpGuardedLo bbpGuardedHi bbpGuardedSum bbpGuardErr at h ⊢
  have e : n + 1 + k = n + (k + 1) := by omega
  simp only [Nat.add_sub_cancel] at h
  rw [e] at h
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  rw [h]

/-- iterated: `(n+j, g-j)` ⇒ `(n, g)` for `j ≤ g`. -/
theorem BBPGuardAgreesAt.of_shift {n g : ℕ} :
    ∀ j, j ≤ g → BBPGuardAgreesAt (n + j) (g - j) → BBPGuardAgreesAt n g := by
  intro j
  induction j generalizing n g with
  | zero => intro _ h; simpa using h
  | succ j ih =>
    intro hj h
    have h1 : BBPGuardAgreesAt (n + 1 + j) (g - 1 - j) := by
      have e1 : n + 1 + j = n + (j + 1) := by omega
      have e2 : g - 1 - j = g - (j + 1) := by omega
      rw [e1, e2]; exact h
    exact BBPGuardAgreesAt.of_succ_pred (by omega) (ih (by omega) h1)

/-! ### 1. Sufficient condition -/

/-- `|16^(n+g)·π − S| ≤ E`. -/
theorem guardedSum_close (n g : ℕ) :
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

/-- **Sufficient condition.** If `16^g · |16^n π − m| > 2E = 8(n+g+1)+4` for every integer `m`
(i.e. `δ·16^g > 2E` with `δ = dist(16^n π, ℤ)`), then the guard agrees at `(n, g)`.
(The constant is `2E`, not `E`: one `E` from `|S − 16^(n+g)π| ≤ E`, one from the bracket width.) -/
theorem guardAgreesAt_of_dist {n g : ℕ}
    (h : ∀ m : ℤ, 2 * (bbpGuardErr n g : ℝ) < (16 : ℝ) ^ g * |(16 : ℝ) ^ n * Real.pi - m|) :
    BBPGuardAgreesAt n g := by
  by_contra hne
  set S := bbpGuardedSum n g with hS
  set E := bbpGuardErr n g with hE
  set M := 16 ^ g with hM
  have hMpos : 0 < M := by positivity
  have hle : bbpGuardedLo n g ≤ bbpGuardedHi n g :=
    Nat.div_le_div_right (by omega : S - E ≤ S + E)
  have hlt : bbpGuardedLo n g + 1 ≤ bbpGuardedHi n g := by
    unfold BBPGuardAgreesAt at hne; omega
  -- Hi*M ≤ S+E ;  S-E < (Lo+1)*M ≤ Hi*M
  have h1 : bbpGuardedHi n g * M ≤ S + E := Nat.div_mul_le_self _ _
  have h2 : S - E < (bbpGuardedLo n g + 1) * M := by
    have := Nat.lt_div_mul_add (a := S - E) (b := M) hMpos
    unfold bbpGuardedLo; rw [Nat.add_mul, Nat.one_mul]; exact this
  have h3 : (bbpGuardedLo n g + 1) * M ≤ bbpGuardedHi n g * M := Nat.mul_le_mul_right _ hlt
  set m : ℤ := (bbpGuardedHi n g : ℤ) with hm
  have hclose := guardedSum_close n g
  rw [← hS, ← hE] at hclose
  have hMr : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
  have hMc : (M:ℝ) = (16:ℝ)^g := by rw [hM]; push_cast; rfl
  -- real versions: |S - Hi*M| ≤ E
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

/-- Same with `δ := |x − round x| = dist(x, ℤ)` . -/
theorem guardAgreesAt_of_round {n g : ℕ}
    (h : 2 * (bbpGuardErr n g : ℝ) <
      (16 : ℝ) ^ g * |(16 : ℝ) ^ n * Real.pi - (round ((16 : ℝ) ^ n * Real.pi) : ℤ)|) :
    BBPGuardAgreesAt n g := by
  apply guardAgreesAt_of_dist
  intro m
  refine lt_of_lt_of_le h ?_
  exact mul_le_mul_of_nonneg_left (round_le _ m) (by positivity)

/-- Statement in the requested shape: `x = 16^n π`, `δ = dist x ℤ`, `δ·16^g > 2(4(n+g+1)+2)`. -/
theorem guardAgreesAt_of_dist_int {n g : ℕ}
    (h : 2 * (4 * ((n : ℝ) + g + 1) + 2) <
      (Metric.infDist ((16 : ℝ) ^ n * Real.pi) (Set.range ((↑) : ℤ → ℝ))) * (16 : ℝ) ^ g) :
    BBPGuardAgreesAt n g := by
  apply guardAgreesAt_of_dist
  intro m
  have hE : ((bbpGuardErr n g : ℕ) : ℝ) = 4 * ((n : ℝ) + g + 1) + 2 := by simp [bbpGuardErr]
  rw [hE]
  have : Metric.infDist ((16 : ℝ) ^ n * Real.pi) (Set.range ((↑) : ℤ → ℝ)) ≤
      |(16 : ℝ) ^ n * Real.pi - m| := by
    rw [← Real.dist_eq]
    exact Metric.infDist_le_dist_of_mem ⟨m, rfl⟩
  have hg : (0:ℝ) < (16:ℝ)^g := by positivity
  nlinarith

/-! ### 2. Effective-measure hypothesis -/

/-- `|π − p/q| > C / q^μ` for all integers `p` and all `q ≥ 2` (i.e. `C·q^(−μ)`). -/
def PiEffectiveMeasure (μ : ℕ) (C : ℝ) : Prop :=
  ∀ p : ℤ, ∀ q : ℕ, 2 ≤ q → |Real.pi - (p : ℝ) / (q : ℝ)| > C / (q : ℝ) ^ μ

/-- convenient form at `q = 16^n`, `n ≥ 1`: `|16^n π − p| · 16^(nμ) > C · 16^n`. -/
theorem PiEffectiveMeasure.at_pow16 {μ : ℕ} {C : ℝ} (H : PiEffectiveMeasure μ C)
    {n : ℕ} (hn : 1 ≤ n) (p : ℤ) :
    |(16 : ℝ) ^ n * Real.pi - p| * (16 : ℝ) ^ (n * μ) > C * (16 : ℝ) ^ n := by
  have hq : 2 ≤ 16 ^ n := by
    calc 2 ≤ 16 := by norm_num
      _ = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h := H p (16 ^ n) hq
  have hpos : (0:ℝ) < (16:ℝ)^n := by positivity
  have hqc : ((16 ^ n : ℕ) : ℝ) = (16:ℝ)^n := by push_cast; rfl
  rw [hqc] at h
  have hp : (0:ℝ) < (16:ℝ)^(n*μ) := by positivity
  have e : |(16 : ℝ) ^ n * Real.pi - p| = (16:ℝ)^n * |Real.pi - (p:ℝ) / (16:ℝ)^n| := by
    rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos]; congr 1; field_simp
  have e2 : ((16:ℝ)^n)^μ = (16:ℝ)^(n*μ) := (pow_mul _ _ _).symm
  rw [e2] at h
  rw [e, gt_iff_lt, div_lt_iff₀ hp] at *
  nlinarith [h]

/-! ### 3. Conditional all-`n` theorem with explicit linear `g = μ·n + 3 + ⌈(8μ+44)/C⌉` -/

/-- Explicit linear guard depth: `g(n) = μ·n + 3 + ⌈(8μ+44)/C⌉₊`. -/
noncomputable def gfun (μ : ℕ) (C : ℝ) (n : ℕ) : ℕ := μ * n + 3 + ⌈(8 * (μ : ℝ) + 44) / C⌉₊

private lemma sq_le_pow16 (j : ℕ) : (j + 1) ^ 2 ≤ 16 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    calc (j + 1 + 1) ^ 2 ≤ 16 * (j + 1) ^ 2 := by nlinarith [Nat.zero_le j]
      _ ≤ 16 * 16 ^ j := Nat.mul_le_mul_left _ ih
      _ = 16 ^ (j + 1) := by ring

private lemma one_add_15_le (n : ℕ) : (1 : ℝ) + 15 * n ≤ (16 : ℝ) ^ n := by
  have := one_add_mul_le_pow (a := (15:ℝ)) (by norm_num) n
  norm_num at this
  linarith

theorem pi_dist_int_gt (m : ℤ) : (14 : ℝ) / 100 < |Real.pi - m| := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  rcases le_or_gt m 3 with h | h
  · have : (m:ℝ) ≤ 3 := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have : (4:ℝ) ≤ m := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith

theorem pi_effective_guard_agrees {μ : ℕ} {C : ℝ} (hC : 0 < C) (H : PiEffectiveMeasure μ C)
    (n : ℕ) : BBPGuardAgreesAt n (gfun μ C n) := by
  set j : ℕ := ⌈(8 * (μ : ℝ) + 44) / C⌉₊ with hj
  have hjr : (8 * (μ : ℝ) + 44) / C ≤ j := Nat.le_ceil _
  have hjr' : 8 * (μ : ℝ) + 44 ≤ C * j := by
    rw [div_le_iff₀ hC] at hjr; linarith
  -- C * 16^j ≥ B (j+1),  B = 8μ+44
  have hCj : (8 * (μ : ℝ) + 44) * ((j:ℝ) + 1) ≤ C * (16:ℝ) ^ j := by
    have hsq : ((j:ℝ) + 1) ^ 2 ≤ (16:ℝ) ^ j := by exact_mod_cast sq_le_pow16 j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
  have hμ : (0:ℝ) ≤ μ := Nat.cast_nonneg μ
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  apply guardAgreesAt_of_dist
  intro m
  have hE : ((bbpGuardErr n (gfun μ C n) : ℕ) : ℝ) =
      4 * ((n : ℝ) + (gfun μ C n : ℕ) + 1) + 2 := by simp [bbpGuardErr]
  have hgf : ((gfun μ C n : ℕ) : ℝ) = μ * n + 3 + j := by simp [gfun, hj]
  rw [hE, hgf]
  have hg16 : (16:ℝ) ^ (gfun μ C n) = (16:ℝ)^(n*μ) * (16:ℝ)^3 * (16:ℝ)^j := by
    simp only [gfun, hj]; rw [pow_add, pow_add, mul_comm μ n]
  rw [hg16]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hd := pi_dist_int_gt m
    simp only [pow_zero, one_mul, zero_mul, Nat.cast_zero, mul_zero, zero_add]
    have h16 : (1:ℝ) + 15 * j ≤ (16:ℝ)^j := one_add_15_le j
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hd.le (by positivity : (0:ℝ) ≤ 4096 * (16:ℝ)^j)]
  · have hH := H.at_pow16 hpos m
    have h16n := one_add_15_le n
    -- |.| * 16^(nμ) > C 16^n
    set a := |(16 : ℝ) ^ n * Real.pi - m| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hp1 : (0:ℝ) < (16:ℝ)^(n*μ) := by positivity
    have hp3 : (0:ℝ) < (16:ℝ)^j := by positivity
    -- goal: 2(4(n + (μn+3+j) + 1)+2) < 16^(nμ)*16^3*16^j * a  (after rearrangement)
    have step : C * (16:ℝ)^n * ((16:ℝ)^3 * (16:ℝ)^j) <
        (16:ℝ)^(n*μ) * (16:ℝ)^3 * (16:ℝ)^j * a := by
      have := mul_lt_mul_of_pos_right hH (by positivity : (0:ℝ) < (16:ℝ)^3 * (16:ℝ)^j)
      nlinarith [this]
    refine lt_of_lt_of_le ?_ step.le
    -- need  2(4(n+μn+3+j+1)+2) < C 16^n 16^3 16^j
    have hb : C * (16:ℝ)^j ≥ (8 * (μ:ℝ) + 44) * ((j:ℝ) + 1) := hCj
    have hB : 0 ≤ (8 * (μ:ℝ) + 44) := by positivity
    have : (8 * (μ:ℝ) + 44) * ((j:ℝ) + 1) * (1 + 15 * n) * 4096 ≤
        C * (16:ℝ)^n * ((16:ℝ)^3 * (16:ℝ)^j) := by
      have e : C * (16:ℝ)^n * ((16:ℝ)^3 * (16:ℝ)^j) = (C * (16:ℝ)^j) * (16:ℝ)^n * 4096 := by
        norm_num; ring
      rw [e]
      have h1 : (8 * (μ:ℝ) + 44) * ((j:ℝ) + 1) * (1 + 15 * n) ≤ (C * (16:ℝ)^j) * (16:ℝ)^n :=
        mul_le_mul hb h16n (by positivity) (by positivity)
      linarith
    refine lt_of_lt_of_le ?_ this
    nlinarith [mul_nonneg hμ hn0, mul_nonneg hj0 hn0, mul_nonneg hμ hj0,
      mul_nonneg (mul_nonneg hμ hj0) hn0]

/-- **Conditional all-`n` theorem.** -/
theorem pi_effective_measure_guard_all_n {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiEffectiveMeasure μ C) :
    ∀ n : ℕ, BBPGuardAgreesAt n (gfun μ C n) :=
  pi_effective_guard_agrees hC H

/-- and then the digit/floor are certified with the explicit linear depth. -/
theorem pi_effective_measure_digit_all_n {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiEffectiveMeasure μ C) (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n (gfun μ C n) : ℤ) ∧
      bbpCertDigitAt n (gfun μ C n) = bbpHexDigitReal n :=
  ⟨(pi_effective_guard_agrees hC H n).floor_pi, (pi_effective_guard_agrees hC H n).digit_pi⟩

/-! ### 4. Sharpened depth: slope `μ − 1` plus a logarithmic term -/

/-- Weaker hypothesis actually needed: the effective measure only at denominators `q = 16^n`
(`n ≥ 1`): `|16^n π − p| · 16^(nμ) > C · 16^n`. -/
def PiPow16Measure (μ : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℤ, |(16 : ℝ) ^ n * Real.pi - p| * (16 : ℝ) ^ (n * μ) > C * (16 : ℝ) ^ n

theorem PiEffectiveMeasure.toPow16 {μ : ℕ} {C : ℝ} (H : PiEffectiveMeasure μ C) :
    PiPow16Measure μ C := fun _ hn p => H.at_pow16 hn p

/-- Sharper guard depth: `g'(n) = (μ−1)·n + (⌊log₁₆(n+1)⌋ + 1) + ⌈(8μ+20)/C⌉₊`. -/
noncomputable def gfun' (μ : ℕ) (C : ℝ) (n : ℕ) : ℕ :=
  (μ - 1) * n + (Nat.log 16 (n + 1) + 1) + ⌈(8 * (μ : ℝ) + 20) / C⌉₊

private lemma log16_succ_le (n : ℕ) : Nat.log 16 (n + 1) ≤ n := by
  have : Nat.log 16 (n + 1) < 16 ^ (Nat.log 16 (n+1)) := Nat.lt_pow_self (by norm_num)
  have h2 : Nat.log 16 (n + 1) ≤ Nat.log 16 (n + 1) := le_rfl
  have h3 : 16 ^ (Nat.log 16 (n + 1)) ≤ n + 1 := Nat.pow_log_le_self 16 (by omega)
  omega

theorem pi_effective_guard_agrees' {μ : ℕ} {C : ℝ} (hC : 0 < C) (hμ1 : 1 ≤ μ)
    (H : PiPow16Measure μ C) (n : ℕ) : BBPGuardAgreesAt n (gfun' μ C n) := by
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  set j : ℕ := ⌈(8 * ((k + 1 : ℕ) : ℝ) + 20) / C⌉₊ with hj
  set L : ℕ := Nat.log 16 (n + 1) + 1 with hL
  have hBpos : (0:ℝ) < (8 * ((k + 1 : ℕ) : ℝ) + 20) / C := by positivity
  have hj1 : 1 ≤ j := Nat.ceil_pos.mpr hBpos
  have hjr : (8 * ((k + 1 : ℕ) : ℝ) + 20) / C ≤ j := Nat.le_ceil _
  have hjr' : 8 * ((k + 1 : ℕ) : ℝ) + 20 ≤ C * j := by
    rw [div_le_iff₀ hC] at hjr; linarith
  have hCj : (8 * ((k + 1 : ℕ) : ℝ) + 20) * ((j:ℝ) + 1) ≤ C * (16:ℝ) ^ j := by
    have hsq : ((j:ℝ) + 1) ^ 2 ≤ (16:ℝ) ^ j := by exact_mod_cast sq_le_pow16 j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hLle : (L : ℝ) ≤ n + 1 := by
    have := log16_succ_le n
    have : L ≤ n + 1 := by omega
    exact_mod_cast this
  have hL16 : ((n:ℝ) + 1) ≤ (16:ℝ) ^ L := by
    have : n + 1 < 16 ^ (Nat.log 16 (n + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    have : n + 1 ≤ 16 ^ L := this.le
    exact_mod_cast this
  apply guardAgreesAt_of_dist
  intro m
  have hE : ((bbpGuardErr n (gfun' (k+1) C n) : ℕ) : ℝ) =
      4 * ((n : ℝ) + (gfun' (k+1) C n : ℕ) + 1) + 2 := by simp [bbpGuardErr]
  have hgf : ((gfun' (k+1) C n : ℕ) : ℝ) = k * n + L + j := by
    simp [gfun', hj, hL]
  rw [hE, hgf]
  have hg16 : (16:ℝ) ^ (gfun' (k+1) C n) = (16:ℝ)^(n*k) * (16:ℝ)^L * (16:ℝ)^j := by
    simp only [gfun', hj, hL, Nat.add_sub_cancel]
    rw [pow_add, pow_add, mul_comm k n]
  rw [hg16]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hd := pi_dist_int_gt m
    have hL1 : L = 1 := by simp [hL]
    rw [hL1]
    simp only [pow_zero, one_mul, mul_zero, zero_mul, Nat.cast_zero, zero_add, Nat.cast_one,
      pow_one]
    have h16 : (1:ℝ) + 15 * j ≤ (16:ℝ)^j := one_add_15_le j
    have hj1r : (1:ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith [mul_le_mul_of_nonneg_left hd.le (by positivity : (0:ℝ) ≤ 16 * (16:ℝ)^j)]
  · have hH := H n hpos m
    set a := |(16 : ℝ) ^ n * Real.pi - m| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hpn : (0:ℝ) < (16:ℝ)^n := by positivity
    have hpk : (0:ℝ) < (16:ℝ)^(n*k) := by positivity
    have hnk : (16:ℝ)^(n*(k+1)) = (16:ℝ)^n * (16:ℝ)^(n*k) := by
      rw [mul_add, mul_one, pow_add, mul_comm]
    -- a * 16^(nk) > C
    have hC' : C < a * (16:ℝ)^(n*k) := by
      have h1 : C * (16:ℝ)^n < (a * (16:ℝ)^(n*k)) * (16:ℝ)^n := by
        have := hH
        rw [hnk] at this
        nlinarith [this]
      exact lt_of_mul_lt_mul_right h1 hpn.le
    have step : C * (16:ℝ)^L * (16:ℝ)^j <
        (16:ℝ)^(n*k) * (16:ℝ)^L * (16:ℝ)^j * a := by
      have hp : (0:ℝ) < (16:ℝ)^L * (16:ℝ)^j := by positivity
      have := mul_lt_mul_of_pos_right hC' hp
      nlinarith [this]
    refine lt_of_lt_of_le ?_ step.le
    have hb := hCj
    have h1 : (8 * ((k + 1 : ℕ) : ℝ) + 20) * ((j:ℝ) + 1) * ((n:ℝ) + 1) ≤
        (C * (16:ℝ)^j) * (16:ℝ)^L :=
      mul_le_mul hb hL16 (by positivity) (by positivity)
    have e : C * (16:ℝ)^L * (16:ℝ)^j = (C * (16:ℝ)^j) * (16:ℝ)^L := by ring
    rw [e]
    refine lt_of_lt_of_le ?_ h1
    push_cast
    nlinarith [mul_nonneg hk hn0, mul_nonneg hj0 hn0, mul_nonneg hk hj0,
      mul_nonneg (mul_nonneg hk hj0) hn0]

/-- **Sharpened conditional all-`n` theorem** (slope `μ − 1` plus `log₁₆(n+1)` term). -/
theorem pi_effective_measure_guard_all_n' {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiEffectiveMeasure μ C) (hμ : 1 ≤ μ) :
    ∀ n : ℕ, BBPGuardAgreesAt n (gfun' μ C n) :=
  pi_effective_guard_agrees' hC hμ H.toPow16

/-- Same, from the weaker `16^n`-only hypothesis. -/
theorem pi_pow16_measure_guard_all_n' {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiPow16Measure μ C) (hμ : 1 ≤ μ) :
    ∀ n : ℕ, BBPGuardAgreesAt n (gfun' μ C n) :=
  pi_effective_guard_agrees' hC hμ H

theorem pi_effective_measure_digit_all_n' {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiEffectiveMeasure μ C) (hμ : 1 ≤ μ) (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n (gfun' μ C n) : ℤ) ∧
      bbpCertDigitAt n (gfun' μ C n) = bbpHexDigitReal n :=
  ⟨(pi_effective_guard_agrees' hC hμ H.toPow16 n).floor_pi,
   (pi_effective_guard_agrees' hC hμ H.toPow16 n).digit_pi⟩

end BBPPi
