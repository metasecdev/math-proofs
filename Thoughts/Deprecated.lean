import Thoughts.Proved.BBPExplicitGuard
import Thoughts.Research.MahlerSharp7b
import Thoughts.Research.BBPMu570b
import Thoughts.Research.BBPMu658

/-!
# Deprecated names

The headline theorems were given Mathlib-style names in the namespace `BBPPi` on 2026-11-01
(release `v1.0.0`). The earlier names are kept here as deprecated aliases, so that existing
references still resolve (with a deprecation warning).

| Old name | New name |
|---|---|
| `FinitistProved.bbp_guard_all_n_mu570b` | `BBPPi.guardAgreesAt_guard570` |
| `FinitistProved.bbp_digit_all_n_mu570b` | `BBPPi.floor_digit_eq_guard570` |
| `FinitistProved.bbp_guard_mu570b_of_ge` | `BBPPi.guardAgreesAt_of_guard570_le` |
| `FinitistProved.bbp_digit_all_n_fixed7b` | `BBPPi.bbpDigit_eq_of_guard_ge` |
| `FinitistProved.bbp_digit_all_n_at_G7b` | `BBPPi.bbpDigit_eq_at_guard570_simple` |
| `FinitistProved.bbp_guard_all_n_mu658` | `BBPPi.guardAgreesAt_guard658` |
| `FinitistProved.bbp_digit_all_n_mu658` | `BBPPi.floor_digit_eq_guard658` |
| `FinitistProved.bbp_explicit_guard_all_n` | `BBPPi.exists_guard_floor_digit_eq` |
| `MahlerSharp7b.pi_pow16_measure7` | `BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure` |

The heavy capped-certificate modules (library `BBPHeavyCerts`) are not renamed.
-/

namespace FinitistProved

@[deprecated BBPPi.guardAgreesAt_guard570 (since := "2026-11-01")]
alias bbp_guard_all_n_mu570b := BBPPi.guardAgreesAt_guard570
@[deprecated BBPPi.floor_digit_eq_guard570 (since := "2026-11-01")]
alias bbp_digit_all_n_mu570b := BBPPi.floor_digit_eq_guard570
@[deprecated BBPPi.guardAgreesAt_of_guard570_le (since := "2026-11-01")]
alias bbp_guard_mu570b_of_ge := BBPPi.guardAgreesAt_of_guard570_le
@[deprecated BBPPi.bbpDigit_eq_of_guard_ge (since := "2026-11-01")]
alias bbp_digit_all_n_fixed7b := BBPPi.bbpDigit_eq_of_guard_ge
@[deprecated BBPPi.bbpDigit_eq_at_guard570_simple (since := "2026-11-01")]
alias bbp_digit_all_n_at_G7b := BBPPi.bbpDigit_eq_at_guard570_simple
@[deprecated BBPPi.guardAgreesAt_guard658 (since := "2026-11-01")]
alias bbp_guard_all_n_mu658 := BBPPi.guardAgreesAt_guard658
@[deprecated BBPPi.floor_digit_eq_guard658 (since := "2026-11-01")]
alias bbp_digit_all_n_mu658 := BBPPi.floor_digit_eq_guard658
@[deprecated BBPPi.exists_guard_floor_digit_eq (since := "2026-11-01")]
alias bbp_explicit_guard_all_n := BBPPi.exists_guard_floor_digit_eq

end FinitistProved

namespace MahlerSharp7b

@[deprecated BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure (since := "2026-11-01")]
alias pi_pow16_measure7 := BBPPi.MahlerSharp7b.pi_pow16_irrationality_measure

end MahlerSharp7b
