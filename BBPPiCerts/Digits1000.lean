/-
  digit correctness unconditionally for every `n ≤ 1000` (2026-09-30 extension of
  `BBPDigitsUnconditional.lean`, which is left intact and still gives `n ≤ 300`).

  * The guard check `bbpGuardAgrees n` for `n ≤ 1000` is `bbpGuardAgrees_of_lt_1001`
    (`BBPGuardedCertsExt.lean`, generated, `decide +kernel`).
  * The analytic part is the proved `bbpGuarded_bracket` (no π hypothesis, `BBPGuarded.lean`)
    and the proved identity `bbpPiEqualsSeries_proved` (the BBP identity, `BBPPiIdentity.lean`).

  The bound 1000 is a build-cost choice, not a mathematical limit. NOT proved here:
  `PBBP01General` (all `n`). Note `∀ n, bbpGuardAgrees n` is itself FALSE (`not_forall_bbpGuardAgrees`,
  `BBPGuardCap.lean`), so that reduction cannot be completed; see `docs/PBBP01_EXTENSION_ANALYSIS.md`.
-/
import BBPPi.Identity
import BBPPi.Guarded
import BBPPi.Spigot
import BBPPiCerts.Digits300
import BBPPiCerts.GuardedCertsExt

namespace BBPPi

open Real

theorem bbpCertFloor_eq_floor_series_of_le_1000 (n : ℕ) (hn : n ≤ 1000) :
    ⌊(16 : ℝ) ^ n * bbpSeries⌋ = (bbpCertFloor n : ℤ) :=
  bbpCertFloor_eq_floor_series n (bbpGuardAgrees_of_lt_1001 n (by omega))

theorem bbpCertFloor_bracket_pi_of_le_1000_unconditional (n : ℕ) (hn : n ≤ 1000) :
    (bbpCertFloor n : ℝ) ≤ (16 : ℝ) ^ n * Real.pi ∧
      (16 : ℝ) ^ n * Real.pi < (bbpCertFloor n : ℝ) + 1 :=
  bbpCertFloor_bracket_pi bbpPiEqualsSeries_proved n (bbpGuardAgrees_of_lt_1001 n (by omega))

theorem bbpCertFloor_eq_floor_pi_of_le_1000_unconditional (n : ℕ) (hn : n ≤ 1000) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloor n : ℤ) :=
  bbpCertFloor_eq_floor_pi bbpPiEqualsSeries_proved n (bbpGuardAgrees_of_lt_1001 n (by omega))

/-- **digit correctness for every `n ≤ 1000`, unconditionally** (the BBP identity is proved in `BBPPiIdentity`). -/
theorem BBPSpigotDigitCorrect_of_le_1000_unconditional (n : ℕ) (hn : n ≤ 1000) :
    BBPSpigotDigitCorrect n :=
  BBPSpigotDigitCorrect_of_guard bbpPiEqualsSeries_proved n (bbpGuardAgrees_of_lt_1001 n (by omega))

end BBPPi
