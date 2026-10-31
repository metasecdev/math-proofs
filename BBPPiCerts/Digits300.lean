/-
  Unconditional versions of the the BBP identity-conditional digit correctness results (2026-09).

  `BBPPiIdentity.lean` proves `bbpPiEqualsSeries_proved : BBPPiEqualsSeries`
  (i.e. `bbpSeries = Real.pi`). `BBPSeries.lean` cannot import it (import cycle), so the
  conditional theorems in `BBPGuarded.lean`, `BBPSpigot.lean` and `BBPGuardedCerts.lean`
  are left untouched and this file discharges their `hπ : BBPPiEqualsSeries` argument:

  * `BBPSpigotDigitCorrect_of_le_300_unconditional`: digit correctness for every `n ≤ 300`.
  * `bbpCertFloor_bracket_pi_of_le_300_unconditional`,
    `bbpCertFloor_eq_floor_pi_unconditional`, `bbpCertFloor_bracket_pi_unconditional`.
  * Tier-1 (n = 5, 17, 18, 24, 29, 32, 40, 42): `BBPSpigotDigitCorrect_<n>_unconditional`,
    `bbpHexDigitReal_<n>_unconditional`, `bbpPi_bracket_<n>_unconditional`.

  NOT proved here: digit correctness for general `n > 300` (`PBBP01General`) stays open; the only
  general-`n` reduction is `PBBP01General_of_guard_unconditional` (needs the guard ∀ n).
-/
import BBPPi.Identity
import BBPPi.Guarded
import BBPPi.Spigot
import BBPPiCerts.GuardedCerts

namespace BBPPi

open Real

theorem bbpCertFloor_eq_floor_pi_unconditional (n : ℕ) (h : bbpGuardAgrees n) :
    ⌊(16 : ℝ) ^ n * Real.pi⌋ = (bbpCertFloor n : ℤ) :=
  bbpCertFloor_eq_floor_pi bbpPiEqualsSeries_proved n h

theorem bbpCertFloor_bracket_pi_unconditional (n : ℕ) (h : bbpGuardAgrees n) :
    (bbpCertFloor n : ℝ) ≤ (16 : ℝ) ^ n * Real.pi ∧
      (16 : ℝ) ^ n * Real.pi < (bbpCertFloor n : ℝ) + 1 :=
  bbpCertFloor_bracket_pi bbpPiEqualsSeries_proved n h

theorem bbpCertFloor_bracket_pi_of_le_300_unconditional (n : ℕ) (hn : n ≤ 300) :
    (bbpCertFloor n : ℝ) ≤ (16 : ℝ) ^ n * Real.pi ∧
      (16 : ℝ) ^ n * Real.pi < (bbpCertFloor n : ℝ) + 1 :=
  bbpCertFloor_bracket_pi_of_le_300 bbpPiEqualsSeries_proved n hn

/-- **digit correctness for every `n ≤ 300`, unconditionally** (the BBP identity is proved in `BBPPiIdentity`). -/
theorem BBPSpigotDigitCorrect_of_le_300_unconditional (n : ℕ) (hn : n ≤ 300) :
    BBPSpigotDigitCorrect n :=
  BBPSpigotDigitCorrect_of_le_300 bbpPiEqualsSeries_proved n hn

/-- Reduction only: digit correctness for all `n` follows from the guard check at all `n`
(the guard is verified only for `n ≤ 300`, so this does NOT prove general `n`). -/
theorem PBBP01General_of_guard_unconditional (h : ∀ n, bbpGuardAgrees n) :
    PBBP01General :=
  PBBP01General_of_guard bbpPiEqualsSeries_proved h

/-! ### Tier-1 (n = 5, 17, 18, 24, 29, 32, 40, 42) -/

theorem BBPSpigotDigitCorrect_five_unconditional : BBPSpigotDigitCorrect 5 :=
  BBPSpigotDigitCorrect_five bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_five_unconditional : bbpHexDigitReal 5 = 6 :=
  bbpHexDigitReal_five bbpPiEqualsSeries_proved

theorem bbpPi_bracket_five_unconditional :
    (3294198 : ℝ) ≤ (16 : ℝ) ^ 5 * Real.pi ∧
      (16 : ℝ) ^ 5 * Real.pi < (3294198 : ℝ) + 1 :=
  bbpPi_bracket_five bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_seventeen_unconditional : BBPSpigotDigitCorrect 17 :=
  BBPSpigotDigitCorrect_seventeen bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_seventeen_unconditional : bbpHexDigitReal 17 = 1 :=
  bbpHexDigitReal_seventeen bbpPiEqualsSeries_proved

theorem bbpPi_bracket_seventeen_unconditional :
    (927234490633871723825 : ℝ) ≤ (16 : ℝ) ^ 17 * Real.pi ∧
      (16 : ℝ) ^ 17 * Real.pi < (927234490633871723825 : ℝ) + 1 :=
  bbpPi_bracket_seventeen bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_eighteen_unconditional : BBPSpigotDigitCorrect 18 :=
  BBPSpigotDigitCorrect_eighteen bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_eighteen_unconditional : bbpHexDigitReal 18 = 3 :=
  bbpHexDigitReal_eighteen bbpPiEqualsSeries_proved

theorem bbpPi_bracket_eighteen_unconditional :
    (14835751850141947581203 : ℝ) ≤ (16 : ℝ) ^ 18 * Real.pi ∧
      (16 : ℝ) ^ 18 * Real.pi < (14835751850141947581203 : ℝ) + 1 :=
  bbpPi_bracket_eighteen bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_twenty_four_unconditional : BBPSpigotDigitCorrect 24 :=
  BBPSpigotDigitCorrect_twenty_four bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_twenty_four_unconditional : bbpHexDigitReal 24 = 14 :=
  bbpHexDigitReal_twenty_four bbpPiEqualsSeries_proved

theorem bbpPi_bracket_twenty_four_unconditional :
    (248902613312231085230521944622 : ℝ) ≤ (16 : ℝ) ^ 24 * Real.pi ∧
      (16 : ℝ) ^ 24 * Real.pi < (248902613312231085230521944622 : ℝ) + 1 :=
  bbpPi_bracket_twenty_four bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_twenty_nine_unconditional : BBPSpigotDigitCorrect 29 :=
  BBPSpigotDigitCorrect_twenty_nine bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_twenty_nine_unconditional : bbpHexDigitReal 29 = 7 :=
  bbpHexDigitReal_twenty_nine bbpPiEqualsSeries_proved

theorem bbpPi_bracket_twenty_nine_unconditional :
    (260993306656486022426679778603972359 : ℝ) ≤ (16 : ℝ) ^ 29 * Real.pi ∧
      (16 : ℝ) ^ 29 * Real.pi < (260993306656486022426679778603972359 : ℝ) + 1 :=
  bbpPi_bracket_twenty_nine bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_thirty_two_unconditional : BBPSpigotDigitCorrect 32 :=
  BBPSpigotDigitCorrect_thirty_two bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_thirty_two_unconditional : bbpHexDigitReal 32 = 4 :=
  bbpHexDigitReal_thirty_two bbpPiEqualsSeries_proved

theorem bbpPi_bracket_thirty_two_unconditional :
    (1069028584064966747859680373161870783300 : ℝ) ≤ (16 : ℝ) ^ 32 * Real.pi ∧
      (16 : ℝ) ^ 32 * Real.pi < (1069028584064966747859680373161870783300 : ℝ) + 1 :=
  bbpPi_bracket_thirty_two bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_forty_unconditional : BBPSpigotDigitCorrect 40 :=
  BBPSpigotDigitCorrect_forty bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_forty_unconditional : bbpHexDigitReal 40 = 2 :=
  bbpHexDigitReal_forty bbpPiEqualsSeries_proved

theorem bbpPi_bracket_forty_unconditional :
    (4591442807048218921384805199743311128454155024418 : ℝ) ≤ (16 : ℝ) ^ 40 * Real.pi ∧
      (16 : ℝ) ^ 40 * Real.pi < (4591442807048218921384805199743311128454155024418 : ℝ) + 1 :=
  bbpPi_bracket_forty bbpPiEqualsSeries_proved

theorem BBPSpigotDigitCorrect_forty_two_unconditional : BBPSpigotDigitCorrect 42 :=
  BBPSpigotDigitCorrect_forty_two bbpPiEqualsSeries_proved

theorem bbpHexDigitReal_forty_two_unconditional : bbpHexDigitReal 42 = 9 :=
  bbpHexDigitReal_forty_two bbpPiEqualsSeries_proved

theorem bbpPi_bracket_forty_two_unconditional :
    (1175409358604344043874510131134287648884263686251049 : ℝ) ≤ (16 : ℝ) ^ 42 * Real.pi ∧
      (16 : ℝ) ^ 42 * Real.pi < (1175409358604344043874510131134287648884263686251049 : ℝ) + 1 :=
  bbpPi_bracket_forty_two bbpPiEqualsSeries_proved

end BBPPi
