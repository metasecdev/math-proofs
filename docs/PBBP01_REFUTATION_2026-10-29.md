# P-BBP-01, literal capped form: REFUTED (2026-10-29)

**Result.** `PBBP01General` (`∀ n, bbp_hex_digit n = bbpHexDigitReal n`, the capped certificate with
guard search `4, 8, …, 64`, fallback depth 68) is **false**. Lean: `FinitistProved.not_PBBP01General`
in `Thoughts/Research/BBPCapRefutation.lean`. Consequently `CertDigitTail` and the named gap
`PBBP01OpenGap := GuardWindow ∧ CertDigitTail` are refuted (`not_CertDigitTail`, `not_PBBP01OpenGap`).
Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`, no digit of π computed.

The explicit-guard form `bbp_digit_all_n_unconditional` (∀ n ∃ g, …) is unaffected and remains proved.
The finite checks (capped form correct for every n ≤ 10000) remain true; the capped form simply
fails later, for every n in `[2^272, 2^273]`.

## Argument (structural, not enumeration)
Let `K = n+g+1`, `S = bbpGuardedSum n g`, `E = 4K+2`, `lo = (S−E)/16^g`, `x = 16^n π`.
1. Per-term floor error of `bbp_term` lies in `(−1, 3)` (reused `bbp_term_cast_bounds`), the omitted
   tail lies in `[0,1)` (reused `bbpScaledTail_*`), and `bbpSeries = π` (reused `bbpSeries_eq_pi`). Hence
   `16^g x − (5K+3) − 16^g < lo·16^g ≤ 16^g x − (K+2)` (`guardedLo_position`, new).
   The lower bracket end is always pushed *down* by at least `(K+2)/16^g` units.
2. If `16^g ≤ K+2` and `5K+3 ≤ 14·16^g`, then `1 ≤ ⌊x⌋ − lo ≤ 14`, so `lo mod 16 ≠ ⌊x⌋ mod 16`
   (`lo_digit_ne_of_window`, new).
3. For `n ≥ 2^253`, `16^64 ≤ 8n`, so every searched depth fails (reused `no_guard_below_cap`) and the search
   returns `bbpCertGuard n = 68` (`bbpGuardSearch_of_all_fail`, `bbpCertGuard_eq_68`, new).
4. For `2^272 ≤ n ≤ 2^273`, `g = 68` (`16^68 = 2^272`) satisfies both inequalities in step 2.

Numerical sanity (Python, scaled analogue with fixed g = 1, 2): whenever `K/16^g ∈ (1, 3)`,
`⌊16^n π⌋ − lo` was 3–9 and the digit was wrong in every case tested, consistent with step 1.

## Why earlier analysis said "undecidable in practice"
`docs/PBBP01_CAP_ANALYSIS_2026-10-28.md` expected the tail digit could agree "by chance". That was wrong:
the offset of `lo` is not random noise of size < 1 but a deterministic shift ≥ (K+2)/16^g, which exceeds
one unit once `16^68 ≤ K+2`, and stays below 15 units until `K ≈ 2.8·2^272`.

## Status of the remaining pieces
* `GuardWindow` (`∀ n < 2^270, bbpGuardAgrees n`) is still open but now irrelevant to `PBBP01General`.
  Step 1 also shows agreement at depth g forces `16^g > K+2`.
* Dead end recorded: proving `CertDigitTail` — it is false.
