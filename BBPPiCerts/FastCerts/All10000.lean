/-
  `bbpGuardAgrees_of_lt_10001 : ∀ n < 10001, bbpGuardAgrees n`.
  n < 8300 : `BBPFastCerts8299` (parts CH=100); 8300 ≤ n ≤ 10000 : `BBPFastCertsT8300to10000` (CH=40 parts).
-/
import BBPPiCerts.FastCerts.Upto8299
import BBPPiCerts.FastCerts.From8300

namespace BBPPi

theorem bbpGuardAgrees_of_lt_10001 (n : ℕ) (hn : n < 10001) : bbpGuardAgrees n := by
  by_cases h : n < 8300
  · exact bbpGuardAgrees_of_lt_8300 n h
  · exact bbpGuardAgrees_Ico_8300_10001 n (by omega) hn

end BBPPi
