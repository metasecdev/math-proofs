import BBPPi.ExplicitGuard
import BBPPi.Mu570
import BBPPi.Mu658

/-!
# Deprecated names

Names used in earlier versions of these proofs (and in the first version of the accompanying
paper), kept as deprecated aliases so that old references still resolve.
The earlier namespace `FinitistProved` is now `BBPPi`.
-/

namespace BBPPi

@[deprecated guardAgreesAt_guard570 (since := "2026-10-31")]
alias bbp_guard_all_n_mu570b := guardAgreesAt_guard570
@[deprecated floor_digit_eq_guard570 (since := "2026-10-31")]
alias bbp_digit_all_n_mu570b := floor_digit_eq_guard570
@[deprecated guardAgreesAt_of_guard570_le (since := "2026-10-31")]
alias bbp_guard_mu570b_of_ge := guardAgreesAt_of_guard570_le
@[deprecated bbpDigit_eq_of_guard_ge (since := "2026-10-31")]
alias bbp_digit_all_n_fixed7b := bbpDigit_eq_of_guard_ge
@[deprecated bbpDigit_eq_at_guard570_simple (since := "2026-10-31")]
alias bbp_digit_all_n_at_G7b := bbpDigit_eq_at_guard570_simple
@[deprecated guardAgreesAt_guard658 (since := "2026-10-31")]
alias bbp_guard_all_n_mu658 := guardAgreesAt_guard658
@[deprecated floor_digit_eq_guard658 (since := "2026-10-31")]
alias bbp_digit_all_n_mu658 := floor_digit_eq_guard658
@[deprecated exists_guard_floor_digit_eq (since := "2026-10-31")]
alias bbp_explicit_guard_all_n := exists_guard_floor_digit_eq

namespace MahlerSharp7b

@[deprecated pi_pow16_irrationality_measure (since := "2026-10-31")]
alias pi_pow16_measure7 := pi_pow16_irrationality_measure

end MahlerSharp7b

end BBPPi
