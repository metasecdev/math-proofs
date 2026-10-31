/-
  The guard check `∀ n, bbpGuardAgrees n` is FALSE as defined.

  `bbpCertGuard n = bbpGuardSearch n 16 4` only ever tries guard depths `g ≤ 68`. The guarded
  bracket `[(S-E)/16^g, (S+E)/16^g]` has width about `2E/16^g` with `E = 4(n+g+1)+2` growing
  linearly in `n`; once `2E ≥ 16^68 = 2^272` (i.e. `n ≥ 2^269`) the two ends differ for EVERY
  digit pattern of π, because `S ≥ E` and `(S+E)/m ≥ (S-E)/m + 1` when `2E ≥ m`.

  Consequence: `PBBP01General_of_guard` (hypothesis `∀ n, bbpGuardAgrees n`) has a refutable
  hypothesis, so it cannot be used to prove `PBBP01General`. This does NOT refute
  `PBBP01General` itself (nothing here says anything about the digits of π), and does not
  weaken any finite result (`n ≤ 300`, `n ≤ 1000`).
-/
import BBPPi.Tail

namespace BBPPi

/-- The search never goes below its start or beyond `start + 4·fuel`. -/
theorem bbpGuardSearch_bounds (n : ℕ) : ∀ (fuel g : ℕ),
    g ≤ bbpGuardSearch n fuel g ∧ bbpGuardSearch n fuel g ≤ g + 4 * fuel := by
  intro fuel
  induction fuel with
  | zero => intro g; simp [bbpGuardSearch]
  | succ f ih =>
    intro g
    unfold bbpGuardSearch
    split_ifs
    · omega
    · have := ih (g + 4)
      omega

theorem bbpCertGuard_le (n : ℕ) : bbpCertGuard n ≤ 68 := by
  have := (bbpGuardSearch_bounds n 16 bbpGuardDigits).2
  unfold bbpCertGuard
  have h4 : bbpGuardDigits = 4 := rfl
  omega

/-- The guarded sum dominates its `k = 0` term. -/
theorem bbpSpigotSum_ge_term_zero (N : ℕ) : ∀ K, 1 ≤ K → bbp_term 0 N ≤ bbpSpigotSum N K := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp [bbpSpigotSum]
  | succ K hK ih => simp only [bbpSpigotSum]; omega

theorem bbpGuardedSum_ge_err (n g : ℕ) (hn : 1 ≤ n) : bbpGuardErr n g ≤ bbpGuardedSum n g := by
  set N := n + g with hN
  have hX : 4 * N < 16 ^ N := by
    have h := Nat.lt_two_pow_self (n := 4 * N)
    have : (2 : ℕ) ^ (4 * N) = 16 ^ N := by rw [pow_mul]; norm_num
    omega
  have h0 : bbp_term 0 N ≤ bbpGuardedSum n g :=
    bbpSpigotSum_ge_term_zero N (N + 1) (by omega)
  have h1 : bbp_term 0 N = 4 * 16 ^ N - 2 * 16 ^ N / 4 - 16 ^ N / 5 - 16 ^ N / 6 := by
    simp [bbp_term, bbpSpigotTerm]
  unfold bbpGuardErr
  rw [h1] at h0
  have : 1 ≤ N := by omega
  omega

/-- For `n ≥ 2^270` the guard check fails: the bracket is wider than one guard unit. -/
theorem not_bbpGuardAgrees_of_ge (n : ℕ) (hn : 2 ^ 270 ≤ n) : ¬ bbpGuardAgrees n := by
  intro h
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) hn
  set g := bbpCertGuard n with hg
  have hg68 : g ≤ 68 := bbpCertGuard_le n
  have hm : 16 ^ g ≤ 16 ^ 68 := Nat.pow_le_pow_right (by norm_num) hg68
  have h16 : (16 : ℕ) ^ 68 = 2 ^ 272 := by decide +kernel
  have h2 : (2 : ℕ) ^ 272 = 4 * 2 ^ 270 := by decide +kernel
  have hE : 16 ^ g ≤ 2 * bbpGuardErr n g := by
    unfold bbpGuardErr; omega
  have hS := bbpGuardedSum_ge_err n g hn1
  unfold bbpGuardAgrees at h
  rw [← hg] at h
  unfold bbpGuardedLo bbpGuardedHi at h
  have hpos : 0 < 16 ^ g := by positivity
  have hq : ((bbpGuardedSum n g - bbpGuardErr n g) / 16 ^ g) * 16 ^ g ≤
      bbpGuardedSum n g - bbpGuardErr n g := Nat.div_mul_le_self _ _
  have hle : ((bbpGuardedSum n g - bbpGuardErr n g) / 16 ^ g + 1) * 16 ^ g ≤
      bbpGuardedSum n g + bbpGuardErr n g := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have := (Nat.le_div_iff_mul_le hpos).2 hle
  omega

/-- `∀ n, bbpGuardAgrees n` is false. -/
theorem not_forall_bbpGuardAgrees : ¬ ∀ n, bbpGuardAgrees n :=
  fun h => not_bbpGuardAgrees_of_ge (2 ^ 270) le_rfl (h _)

end BBPPi
