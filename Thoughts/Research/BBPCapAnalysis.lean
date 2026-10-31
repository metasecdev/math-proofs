import Thoughts.Research.BBPMu570Fixed
import Thoughts.Proved.BBPGuardCap
import Thoughts.Proved.BBPFastGuard
import Thoughts.Proved.BBPPiIdentity

/-!
# P-BBP-01: precise analysis of the capped statement (2026-10-28)

`PBBP01General : ∀ n, bbp_hex_digit n = bbpHexDigitReal n` uses the capped certificate
(`bbpCertGuard n ≤ 68`).  This module pins down exactly what the *proved* tools do and do not give
for a capped guard, and isolates the open part as two named `Prop`s.

## (2) which cap `G` is certifiable by the proved measure
* `mu570_cert_of_cap` : `570·n + 2273496 ≤ G → BBPGuardAgreesAt n G ∧ digit correct`  (reuse).
* `cap_certifiable_iff` : that hypothesis is exactly `n ≤ (G − 2273496)/570` (and `G ≥ 2273496`).
* `cap68_certifies_nothing` : for `G ≤ 68` (the cap of `bbpCertGuard`) the measure certifies *no* `n`.
  (The only `n` covered by the capped certificate are therefore the kernel-checked ones.)

## fixed cap fails for large `n` (generalises `not_bbpGuardAgrees_of_ge`)
* `not_guardAgreesAt_of_cap` : `16^g ≤ 8·n ⇒ ¬ BBPGuardAgreesAt n g`  (any `g`, `n ≥ 1`).
* `no_guard_below_cap` : `16^G ≤ 8·n ⇒ ∀ g ≤ G, ¬ BBPGuardAgreesAt n g`.

## (3) the gap as named open `Prop`s
* `GuardWindow`    : `∀ n < 2^270, bbpGuardAgrees n`           (capped guard works in the window)
* `CertDigitTail`  : `∀ n ≥ 2^270, BBPSpigotDigitCorrect n`    (digits at astronomically large `n`)
* `PBBP01OpenGap := GuardWindow ∧ CertDigitTail`, `PBBP01General_of_gap : PBBP01OpenGap → PBBP01General`.
* `GuardWindow_of_depth`, `GuardWindow_of_dist` : concrete sufficient conditions for `GuardWindow`
  (guard depth in the search grid, or a distance-from-integers lower bound `2E < 16^g·dist`).
Nothing here claims `GuardWindow` or `CertDigitTail` holds.
-/

namespace FinitistProved
open Real

/-! ### Fixed-cap failure -/

theorem not_guardAgreesAt_of_cap (n g : ℕ) (hn : 1 ≤ n) (h8 : 16 ^ g ≤ 8 * n) :
    ¬ BBPGuardAgreesAt n g := by
  intro h
  have hE : 16 ^ g ≤ 2 * bbpGuardErr n g := by unfold bbpGuardErr; omega
  have hS := bbpGuardedSum_ge_err n g hn
  unfold BBPGuardAgreesAt bbpGuardedLo bbpGuardedHi at h
  have hpos : 0 < 16 ^ g := by positivity
  have hq : ((bbpGuardedSum n g - bbpGuardErr n g) / 16 ^ g) * 16 ^ g ≤
      bbpGuardedSum n g - bbpGuardErr n g := Nat.div_mul_le_self _ _
  have hle : ((bbpGuardedSum n g - bbpGuardErr n g) / 16 ^ g + 1) * 16 ^ g ≤
      bbpGuardedSum n g + bbpGuardErr n g := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have := (Nat.le_div_iff_mul_le hpos).2 hle
  omega

/-- Any cap `G`: once `16^G ≤ 8n` no guard depth `g ≤ G` can agree. -/
theorem no_guard_below_cap (G n : ℕ) (hn : 1 ≤ n) (h8 : 16 ^ G ≤ 8 * n) :
    ∀ g ≤ G, ¬ BBPGuardAgreesAt n g := fun g hg =>
  not_guardAgreesAt_of_cap n g hn (le_trans (Nat.pow_le_pow_right (by norm_num) hg) h8)

/-- The `G = 68` instance (what `bbpCertGuard` can ever reach): all `n ≥ 2^269` fail at every
searched depth (`16^68 = 2^272 ≤ 8n`). -/
theorem no_guard_cap68 (n : ℕ) (hn : 2 ^ 269 ≤ n) : ∀ g ≤ 68, ¬ BBPGuardAgreesAt n g := by
  have h1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  apply no_guard_below_cap 68 n h1
  have h16 : (16 : ℕ) ^ 68 = 2 ^ 272 := by decide +kernel
  have h2 : (2 : ℕ) ^ 272 = 8 * 2 ^ 269 := by decide +kernel
  omega

/-! ### What the proved measure certifies under a cap -/

theorem mu570_cert_of_cap (n G : ℕ) (h : 570 * n + 2273496 ≤ G) :
    BBPGuardAgreesAt n G ∧
      (⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloorAt n G : ℤ) ∧
        bbpCertDigitAt n G = bbpHexDigitReal n) :=
  ⟨bbp_guard_mu570_of_ge n G (le_trans (guard570_le n) h), bbp_digit_all_n_fixed n G h⟩

theorem cap_certifiable_iff (n G : ℕ) :
    570 * n + 2273496 ≤ G ↔ 2273496 ≤ G ∧ n ≤ (G - 2273496) / 570 := by
  constructor
  · intro h; refine ⟨by omega, ?_⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  · rintro ⟨h1, h2⟩
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 570)).1 h2
    omega

/-- Under the proved measure the cap `G ≤ 68` certifies no `n` at all. -/
theorem cap68_certifies_nothing (n G : ℕ) (hG : G ≤ 68) : ¬ (570 * n + 2273496 ≤ G) := by omega

/-- Smallest cap certifiable for `n = 0` is `2273496` (≫ 68). -/
theorem cap_certifiable_zero : (570 * 0 + 2273496 : ℕ) = 2273496 := rfl

/-! ### The open gap, named -/

/-- The capped guard certificate agrees for all `n` in the window `n < 2^270`. -/
def GuardWindow : Prop := ∀ n < 2 ^ 270, bbpGuardAgrees n

/-- The capped certificate digit is right for `n ≥ 2^270` (there the guard check provably fails
(`not_bbpGuardAgrees_of_ge`), so this is a statement about π's hex digits at huge positions). -/
def CertDigitTail : Prop := ∀ n, 2 ^ 270 ≤ n → BBPSpigotDigitCorrect n

/-- The single named open gap for `PBBP01General`. -/
def PBBP01OpenGap : Prop := GuardWindow ∧ CertDigitTail

theorem PBBP01General_of_gap (h : PBBP01OpenGap) : PBBP01General := by
  intro n
  by_cases hn : n < 2 ^ 270
  · exact BBPSpigotDigitCorrect_of_guard bbpPiEqualsSeries_proved n (h.1 n hn)
  · exact h.2 n (by omega)

theorem PBBP01General_of_split (hw : GuardWindow) (ht : CertDigitTail) : PBBP01General :=
  PBBP01General_of_gap ⟨hw, ht⟩

/-- Conversely `CertDigitTail` is *implied* by `PBBP01General` (so it is no stronger). -/
theorem CertDigitTail_of_general (h : PBBP01General) : CertDigitTail := fun n _ => h n

/-- Sufficient for `GuardWindow`: for every `n` in the window some depth `4 + 4t` (`t < 16`)
agrees (the depths the guard search tries). -/
theorem GuardWindow_of_depth
    (h : ∀ n < 2 ^ 270, ∃ t < 16, BBPGuardAgreesAt n (4 + 4 * t)) : GuardWindow := by
  intro n hn
  obtain ⟨t, ht, hag⟩ := h n hn
  unfold bbpGuardAgrees bbpCertGuard bbpGuardDigits
  exact bbpGuardSearch_of_agree n 16 4 t ht (by omega) hag

/-- Sufficient for `GuardWindow` in terms of π only: `16^n π` stays `2E/16^g`-far from every
integer for some `g = 4 + 4t` in the grid. -/
theorem GuardWindow_of_dist
    (h : ∀ n < 2 ^ 270, ∃ t < 16, ∀ m : ℤ,
      2 * (bbpGuardErr n (4 + 4 * t) : ℝ) <
        (16 : ℝ) ^ (4 + 4 * t) * |(16 : ℝ) ^ n * Real.pi - m|) : GuardWindow :=
  GuardWindow_of_depth fun n hn => by
    obtain ⟨t, ht, hd⟩ := h n hn
    exact ⟨t, ht, guardAgreesAt_of_dist hd⟩

/-- The proved explicit-guard depth function (μ = 570): `∀ n`, agreement at this depth. -/
def gMu570 (n : ℕ) : ℕ := 569 * n + (Nat.log 16 (n + 1) + 1) + 2273495

theorem gMu570_agrees (n : ℕ) : BBPGuardAgreesAt n (gMu570 n) := bbp_guard_mu570_of_ge n _ le_rfl

/-- The measure-derived depth is never inside the capped search grid. -/
theorem gMu570_gt_cap (n : ℕ) : 68 < gMu570 n := by unfold gMu570; omega

end FinitistProved

#print axioms FinitistProved.not_guardAgreesAt_of_cap
#print axioms FinitistProved.no_guard_cap68
#print axioms FinitistProved.mu570_cert_of_cap
#print axioms FinitistProved.PBBP01General_of_gap
#print axioms FinitistProved.GuardWindow_of_dist
