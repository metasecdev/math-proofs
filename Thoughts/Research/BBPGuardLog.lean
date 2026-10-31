import Thoughts.Research.BBPUnconditionalAllN

/-!
# Round 5, priority 1: logarithmic additive constant in the guard depth

`gfun' μ C n = (μ-1)n + (⌊log₁₆(n+1)⌋+1) + ⌈(8μ+20)/C⌉₊` has an additive constant that is
*linear* in `1/C`. Here we replace it by
`guardLogConst μ C = ℓ + (⌊log₁₆(2ℓ)⌋ + 1)`, `ℓ = ⌊log₁₆ ⌈(8μ+20)/C⌉₊⌋ + 1`,
i.e. `log₁₆((8μ+20)/C) + O(log log)`, and re-derive the all-`n` guard theorem from the same
hypothesis `PiPow16Measure μ C`.

With the existing unconditional constants (`μ = 851967`, `C = 2^-17170446`) the additive constant
becomes exactly `4292624` (was ≈ 2^17170469).
-/

namespace FinitistProved
open Real

/-- `ℓ = ⌊log₁₆ ⌈(8μ+20)/C⌉₊⌋ + 1` (so `(8μ+20)/C < 16^ℓ`). -/
noncomputable def guardLogL (μ : ℕ) (C : ℝ) : ℕ := Nat.log 16 ⌈(8 * (μ : ℝ) + 20) / C⌉₊ + 1

/-- additive constant `j = ℓ + ⌊log₁₆(2ℓ)⌋ + 1`. -/
noncomputable def guardLogConst (μ : ℕ) (C : ℝ) : ℕ :=
  guardLogL μ C + (Nat.log 16 (2 * guardLogL μ C) + 1)

/-- **Logarithmic guard depth**: `g''(n) = (μ−1)·n + (⌊log₁₆(n+1)⌋ + 1) + guardLogConst μ C`. -/
noncomputable def gfun'' (μ : ℕ) (C : ℝ) (n : ℕ) : ℕ :=
  (μ - 1) * n + (Nat.log 16 (n + 1) + 1) + guardLogConst μ C

private lemma two_mul_lt_pow16 {l : ℕ} (hl : 1 ≤ l) : 2 * l < 16 ^ l := by
  have h1 : l < 2 ^ l := Nat.lt_two_pow_self
  have h2 : 2 ^ (l + 1) ≤ 16 ^ l := by
    calc 2 ^ (l + 1) ≤ 2 ^ (4 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 ^ l := by rw [pow_mul]; norm_num
  have : 2 * l < 2 ^ (l + 1) := by rw [pow_succ]; omega
  omega

/-- the key property of `guardLogConst`: `(8μ+20)(j+1) ≤ C·16^j`. -/
theorem guardLogConst_spec {μ : ℕ} {C : ℝ} (hC : 0 < C) :
    (8 * (μ : ℝ) + 20) * ((guardLogConst μ C : ℝ) + 1) ≤ C * (16 : ℝ) ^ guardLogConst μ C := by
  set B : ℝ := (8 * (μ : ℝ) + 20) / C with hB
  set t : ℕ := ⌈B⌉₊ with ht
  set l : ℕ := guardLogL μ C with hl
  set l2 : ℕ := Nat.log 16 (2 * l) + 1 with hl2
  have hl1 : 1 ≤ l := by simp [hl, guardLogL]
  have hj : guardLogConst μ C = l + l2 := rfl
  have htl : t < 16 ^ l := Nat.lt_pow_succ_log_self (by norm_num) t
  have hBt : B ≤ t := Nat.le_ceil B
  have h2l : 2 * l < 16 ^ l2 := Nat.lt_pow_succ_log_self (by norm_num) (2 * l)
  have hl2l : l2 ≤ l := by
    have := Nat.log_lt_of_lt_pow (b := 16) (by omega) (two_mul_lt_pow16 hl1)
    omega
  have hjl : l + l2 + 1 ≤ 16 ^ l2 := by omega
  rw [hj]
  have hB16 : B ≤ (16 : ℝ) ^ l := by
    have : (t : ℝ) ≤ ((16 ^ l : ℕ) : ℝ) := by exact_mod_cast htl.le
    push_cast at this; linarith
  have hCB : 8 * (μ : ℝ) + 20 = C * B := by rw [hB]; field_simp
  have hj16 : ((l + l2 : ℕ) : ℝ) + 1 ≤ (16 : ℝ) ^ l2 := by exact_mod_cast hjl
  rw [hCB, pow_add]
  have hB0 : 0 ≤ B := by positivity
  calc C * B * (((l + l2 : ℕ) : ℝ) + 1) ≤ C * (16 : ℝ) ^ l * (16 : ℝ) ^ l2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hB16 hC.le) hj16 (by positivity)
          (by positivity)
    _ = _ := by ring

theorem one_le_guardLogConst (μ : ℕ) (C : ℝ) : 1 ≤ guardLogConst μ C := by
  unfold guardLogConst; omega

private lemma sq_le_pow16' (j : ℕ) : (j + 1) ^ 2 ≤ 16 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    calc (j + 1 + 1) ^ 2 ≤ 16 * (j + 1) ^ 2 := by nlinarith [Nat.zero_le j]
      _ ≤ 16 * 16 ^ j := Nat.mul_le_mul_left _ ih
      _ = 16 ^ (j + 1) := by ring

private lemma one_add_15_le' (n : ℕ) : (1 : ℝ) + 15 * n ≤ (16 : ℝ) ^ n := by
  have := one_add_mul_le_pow (a := (15:ℝ)) (by norm_num) n
  norm_num at this
  linarith

private lemma log16_succ_le' (n : ℕ) : Nat.log 16 (n + 1) ≤ n := by
  have : Nat.log 16 (n + 1) < 16 ^ (Nat.log 16 (n+1)) := Nat.lt_pow_self (by norm_num)
  have h3 : 16 ^ (Nat.log 16 (n + 1)) ≤ n + 1 := Nat.pow_log_le_self 16 (by omega)
  omega

/-- **Generic guard lemma**: any additive constant `j ≥ 1` with `(8μ+20)(j+1) ≤ C·16^j` works. -/
theorem guard_agrees_of_const {μ : ℕ} {C : ℝ} (hμ1 : 1 ≤ μ) (H : PiPow16Measure μ C)
    (j : ℕ) (hj1 : 1 ≤ j) (hCj : (8 * (μ : ℝ) + 20) * ((j : ℝ) + 1) ≤ C * (16 : ℝ) ^ j)
    (n : ℕ) : BBPGuardAgreesAt n ((μ - 1) * n + (Nat.log 16 (n + 1) + 1) + j) := by
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  set L : ℕ := Nat.log 16 (n + 1) + 1 with hL
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hL16 : ((n:ℝ) + 1) ≤ (16:ℝ) ^ L := by
    have : n + 1 < 16 ^ (Nat.log 16 (n + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    have : n + 1 ≤ 16 ^ L := this.le
    exact_mod_cast this
  have hLle : (L : ℝ) ≤ n + 1 := by
    have := log16_succ_le' n
    have : L ≤ n + 1 := by omega
    exact_mod_cast this
  apply guardAgreesAt_of_dist
  intro m
  have hE : ((bbpGuardErr n ((k + 1 - 1) * n + L + j) : ℕ) : ℝ) =
      4 * ((n : ℝ) + (((k + 1 - 1) * n + L + j : ℕ) : ℝ) + 1) + 2 := by simp [bbpGuardErr]
  have hgf : ((((k + 1 - 1) * n + L + j : ℕ)) : ℝ) = k * n + L + j := by
    simp
  rw [hE, hgf]
  have hg16 : (16:ℝ) ^ ((k + 1 - 1) * n + L + j) = (16:ℝ)^(n*k) * (16:ℝ)^L * (16:ℝ)^j := by
    rw [Nat.add_sub_cancel, pow_add, pow_add, mul_comm k n]
  rw [hg16]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hd := pi_dist_int_gt m
    have hL1 : L = 1 := by simp [hL]
    rw [hL1]
    simp only [pow_zero, one_mul, mul_zero, zero_mul, Nat.cast_zero, zero_add, Nat.cast_one,
      pow_one]
    have h16 : (1:ℝ) + 15 * j ≤ (16:ℝ)^j := one_add_15_le' j
    have hj1r : (1:ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith [mul_le_mul_of_nonneg_left hd.le (by positivity : (0:ℝ) ≤ 16 * (16:ℝ)^j)]
  · have hH := H n hpos m
    set a := |(16 : ℝ) ^ n * Real.pi - m| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hpn : (0:ℝ) < (16:ℝ)^n := by positivity
    have hnk : (16:ℝ)^(n*(k+1)) = (16:ℝ)^n * (16:ℝ)^(n*k) := by
      rw [mul_add, mul_one, pow_add, mul_comm]
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
    have h1 : (8 * ((k + 1 : ℕ) : ℝ) + 20) * ((j:ℝ) + 1) * ((n:ℝ) + 1) ≤
        (C * (16:ℝ)^j) * (16:ℝ)^L :=
      mul_le_mul hCj hL16 (by positivity) (le_trans (by positivity) hCj)
    have e : C * (16:ℝ)^L * (16:ℝ)^j = (C * (16:ℝ)^j) * (16:ℝ)^L := by ring
    rw [e]
    refine lt_of_lt_of_le ?_ h1
    push_cast
    nlinarith [mul_nonneg hk hn0, mul_nonneg hj0 hn0, mul_nonneg hk hj0,
      mul_nonneg (mul_nonneg hk hj0) hn0]

/-- **All-`n` guard theorem with logarithmic constant** (from `PiPow16Measure`). -/
theorem pi_pow16_measure_guard_all_n'' {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiPow16Measure μ C) (hμ : 1 ≤ μ) :
    ∀ n : ℕ, BBPGuardAgreesAt n (gfun'' μ C n) := fun n =>
  guard_agrees_of_const hμ H _ (one_le_guardLogConst μ C) (guardLogConst_spec hC) n

theorem pi_effective_measure_guard_all_n'' {μ : ℕ} {C : ℝ} (hC : 0 < C)
    (H : PiEffectiveMeasure μ C) (hμ : 1 ≤ μ) :
    ∀ n : ℕ, BBPGuardAgreesAt n (gfun'' μ C n) :=
  pi_pow16_measure_guard_all_n'' hC H.toPow16 hμ

/-- `gfun''` is never worse than `gfun'` (the constant `log₁₆` vs linear). -/
theorem guardLogConst_le_ceil {μ : ℕ} {C : ℝ} (hC : 0 < C) :
    guardLogConst μ C ≤ ⌈(8 * (μ : ℝ) + 20) / C⌉₊ + 1 := by
  set t := ⌈(8 * (μ : ℝ) + 20) / C⌉₊
  have ht1 : 1 ≤ t := Nat.ceil_pos.mpr (by positivity)
  -- l ≤ log t + 1, l2 ≤ l; both are ≤ t/2-ish; crude: l + l2 ≤ 2(log t + 1) ≤ t + 1
  have hlog : Nat.log 16 t < t := Nat.log_lt_self 16 (by omega)
  have hl : guardLogL μ C = Nat.log 16 t + 1 := rfl
  have hl2 : Nat.log 16 (2 * guardLogL μ C) < guardLogL μ C :=
    Nat.log_lt_of_lt_pow (by rw [hl]; omega) (two_mul_lt_pow16 (by rw [hl]; omega))
  -- 2(log16 t + 1) ≤ t + 1 needs log16 t small relative to t
  have hlt : 2 * (Nat.log 16 t + 1) ≤ t + 1 := by
    rcases Nat.lt_or_ge t 16 with h | h
    · have : Nat.log 16 t = 0 := Nat.log_of_lt h
      omega
    · have h16 : 16 ^ Nat.log 16 t ≤ t := Nat.pow_log_le_self 16 (by omega)
      have hL1 : 1 ≤ Nat.log 16 t := Nat.le_log_of_pow_le (by norm_num) (by simpa using h)
      have := two_mul_lt_pow16 hL1
      omega
  have hgl : guardLogConst μ C = guardLogL μ C + (Nat.log 16 (2 * guardLogL μ C) + 1) := rfl
  rw [hgl, hl] at *
  omega

/-! ### Unconditional instance with the Round-4 constants -/

/-- additive constant for `μ = 851967`, `C = 2^-17170446`: exactly `4292624`. -/
private lemma natLog16_mul_pow (c N e : ℕ) (hc1 : 16 ^ e ≤ c) (hc2 : c < 16 ^ (e + 1)) :
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

theorem guardLogL_piMu_piC : guardLogL piMu piC = 4292618 := by
  unfold guardLogL piMu piC
  rw [MahlerPiMeasure.muPi_def, MahlerPiMeasure.Aexp_def]
  have hceil : ⌈(8 * ((851967 : ℕ) : ℝ) + 20) / (1 / 2 ^ (17170445 + 1))⌉₊ =
      27263024 * 16 ^ 4292611 := by
    have e : (8 * ((851967 : ℕ) : ℝ) + 20) / (1 / 2 ^ (17170445 + 1)) =
        ((27263024 * 16 ^ 4292611 : ℕ) : ℝ) := by
      rw [div_div_eq_mul_div, div_one]
      have h2 : (2 : ℝ) ^ (17170445 + 1) = 4 * 16 ^ 4292611 := by
        rw [show 17170445 + 1 = 2 + 4 * 4292611 by norm_num, pow_add, pow_mul]; norm_num
      rw [h2]; push_cast; ring
    rw [e, Nat.ceil_natCast]
  rw [hceil, natLog16_mul_pow 27263024 4292611 6 (by norm_num) (by norm_num)]

theorem guardLogConst_piMu_piC : guardLogConst piMu piC = 4292624 := by
  unfold guardLogConst
  rw [guardLogL_piMu_piC]
  have : Nat.log 16 (2 * 4292618) = 5 := by
    rw [Nat.log_eq_iff (Or.inl (by norm_num))]; norm_num
  rw [this]

/-- **Unconditional all-`n` P-BBP-01 with logarithmic guard constant**:
for every `n`, the guard agrees at depth `851966·n + ⌊log₁₆(n+1)⌋ + 1 + 4292624`. -/
theorem bbp_guard_all_n_unconditional'' (n : ℕ) :
    BBPGuardAgreesAt n (851966 * n + (Nat.log 16 (n + 1) + 1) + 4292624) := by
  have h := pi_pow16_measure_guard_all_n'' piC_pos pi_pow16_measure_unconditional piMu_pos n
  have hmu : piMu - 1 = 851966 := by unfold piMu; rw [MahlerPiMeasure.muPi_def]
  unfold gfun'' at h
  rwa [hmu, guardLogConst_piMu_piC] at h

theorem bbp_digit_all_n_unconditional'' (n : ℕ) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ =
        (bbpCertFloorAt n (851966 * n + (Nat.log 16 (n + 1) + 1) + 4292624) : ℤ) ∧
      bbpCertDigitAt n (851966 * n + (Nat.log 16 (n + 1) + 1) + 4292624) = bbpHexDigitReal n :=
  ⟨(bbp_guard_all_n_unconditional'' n).floor_pi, (bbp_guard_all_n_unconditional'' n).digit_pi⟩

end FinitistProved

#print axioms FinitistProved.guardLogConst_spec
#print axioms FinitistProved.guard_agrees_of_const
#print axioms FinitistProved.pi_pow16_measure_guard_all_n''
#print axioms FinitistProved.pi_effective_measure_guard_all_n''
#print axioms FinitistProved.guardLogConst_le_ceil
#print axioms FinitistProved.guardLogConst_piMu_piC
#print axioms FinitistProved.bbp_guard_all_n_unconditional''
#print axioms FinitistProved.bbp_digit_all_n_unconditional''
