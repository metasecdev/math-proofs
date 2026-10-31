# P-BBP-01: cap analysis, fast kernel check, and the single open Prop (2026-10-28)

Branch `proof/pbbp01-capped-analysis`, base `main` @ 1597f1b. PR left open, not merged (Brian's rule, 2026-10-27 11:59 PM ET).
No `sorry` in anything labelled proved.

Two statements, kept apart throughout:

* **Explicit-guard form** (`bbp_digit_all_n_unconditional`, `bbp_guard_all_n_mu570`): proved for every `n`, depth
  `569n + (⌊log₁₆(n+1)⌋+1) + 2273495` (Mahler–Mignotte μ = 570). Unchanged.
* **Literal capped form** `PBBP01General := ∀ n, BBPSpigotDigitCorrect n` (guard search over `g ∈ {4,8,…,64}`, fallback 68):
  proved only for a finite range of `n`. This document says exactly how far, and why not further.

## 1. Path 2: which cap is certifiable under the proved measure

Proved in `Thoughts/Research/BBPCapAnalysis.lean` (axioms: propext, Classical.choice, Quot.sound):

* `mu570_cert_of_cap`: `570n + 2273496 ≤ G → BBPGuardAgreesAt n G`.
* `cap_certifiable_iff`: for a cap `G`, the proved measure certifies `n` iff `570n + 2273496 ≤ G`.
* `cap68_certifies_nothing`: for every `G ≤ 68`, `570n + 2273496 ≤ G` is false for every `n`. **The proved measure certifies
  no `n` at all under the real cap 68.** A cap `G` is certifiable only for `n ≤ (G − 2273496)/570`; below `G = 2273496` nothing.
* Any irrationality measure μ gives depth linear in `n` (`g ≈ (μ−1)·n·log₁₆(…)`), so no measure of this type can reach a fixed cap.
  Dead end, reason: depth must grow with `n`; the cap does not.

Refutation direction (also proved): `not_guardAgreesAt_of_cap : 1 ≤ n → 16^g ≤ 8n → ¬ BBPGuardAgreesAt n g`, hence
`no_guard_below_cap` (any fixed cap `G` fails for all `n` with `16^G ≤ 8n`) and `no_guard_cap68`: for `n ≥ 2^269`,
**no `g ≤ 68` works**, so `bbpGuardAgrees n` is false there (and `not_forall_bbpGuardAgrees` already existed).
This does **not** refute `PBBP01General`: when the search falls back to g = 68 the digit can still be correct by chance
(heuristically probability ≈ 1/16 per `n`). So for `n ≥ 2^270` the capped statement is almost surely **false** but
the falsity is not provable here: exhibiting a counterexample needs a hex digit of π at a position ≈ 2^270 (out of reach);
and "digit correct" at such `n` is not a decidable-by-feasible-computation question.

## 2. Path 3: the single named open Prop

```
def GuardWindow     : Prop := ∀ n < 2^270, bbpGuardAgrees n
def CertDigitTail   : Prop := ∀ n, 2^270 ≤ n → BBPSpigotDigitCorrect n
def PBBP01OpenGap   : Prop := GuardWindow ∧ CertDigitTail
theorem PBBP01General_of_gap   : PBBP01OpenGap → PBBP01General
theorem CertDigitTail_of_general : PBBP01General → CertDigitTail   -- so CertDigitTail is necessary
```

* `GuardWindow` (the capped guard search succeeds for all `n < 2^270`) is the *only* part that could be closed by
  a guard-depth bound: `GuardWindow_of_depth` (a per-n depth `t < 16` with agreement at `g+4t` suffices, via
  `bbpGuardSearch_of_agree`) and `GuardWindow_of_dist` (a lower bound on distance of `16^n·π` to an integer, via
  `guardAgreesAt_of_dist`). Neither hypothesis is proved for all `n < 2^270`; the heuristic failure probability at `n` is
  roughly `16^-(68 − log₁₆ n)`, summing to expected failures concentrated just below `2^270`;
  heuristic only). Honestly: **not known true for `n < 2^270`**, only forced false at/after `2^269` (`no_guard_cap68`).
  `GuardWindow` is therefore plausibly true for `n` up to roughly `2^260` but is not provable by any feasible chunk check
  and is likely false somewhere in the last few bits before `2^270`.
* `CertDigitTail` is necessary and almost certainly false. Therefore `PBBP01General` as literally stated is likely
  **false**; the mathematically meaningful statement is the explicit-guard form, which is proved.

## 3. Path 1: kernel check beyond n = 2000

Old method (`BBPGuardedCertsExt2000*`): `decide +kernel` of `bbpGuardAgrees n` with ~4n-bit sums: ~1 s/n average, 8–11 GB RSS,
17 min for n ≤ 2000; memory ~ N³ bits. Dead end past ~3000.

New method (`Thoughts/Proved/BBPFastGuard.lean`, new, sorry-free, no native_decide):

* Agreement `lo = hi` depends only on `s = S mod 16^g`: it holds iff `E ≤ s ∧ s + E < 16^g`, `E = 4(n+g+1)+2`
  (`fastAgreeAt_sound`).
* `S mod M` is computed termwise with each floor reduced by `(X/d) % M = (X % (d·M))/d` after cancelling `16^k`
  (`bbp_term_mod`, `termModR_eq`), summed in blocks of 128 (`fsum_eq`), so no number larger than ~`(8k+6)·M` appears.
* `chkFrom_sound`: the list-driven check implies `bbpGuardAgrees (a+i)` for the whole chunk.
* Kernel cost is interpretive overhead, not bignum arithmetic. Writing the definitions with raw `Nat.add/mul/sub/div/mod/pow`
  and `cond (Nat.ble ..)` gave a 4.3× kernel speedup over the instance/operator version (≈0.34 s/n at n = 4000 vs 1.5 s/n),
  `maxHeartbeats 0` needed in generated modules (default 200000 hits an `isDefEq` timeout while the kernel check runs).
* Python replica (same arithmetic): no guard-search failure for n ∈ [0, 10000]; max `g` = 8; cap 68 never needed.
* Generators: `lean_tools/gen_fast_guard.py`, `gen_fast_guard_all.py` (cached g-list, 101 parts of 100 `n` each, aggregator).

Build status of the 0..10000 certificates and of the aggregator: see §5 (filled in at the end of this run).

## 4. Path 4: inductive / closed form

* The residue structure gives a *per-n* closed form of the agreement condition (`E ≤ s < 16^g − E`), which is what the
  kernel check evaluates. It is not inductive in `n`: `s_n = 16^n·Σ…` mod `16^g` shifts the base with `n`, the terms change denominators
  `8k+j`, and there is no recurrence relating `s_{n+1}` mod `16^g` to `s_n` mod `16^g` except by recomputing the sum
  (the usual BBP spigot reasoning: it is `16·(S_n) mod 1`, which needs the full fractional part, i.e. the
  infinite tail to depth `g` — exactly the content of the guard).
  Dead end, reason: any recurrence loses the information `g` digits deep, and that is the open part.
* PR 8's explicit guard (`bbp_guard_mu570`) is the only all-`n` tool; it is linear in `n` and cannot be capped.
* Chunk extension in general (path 1) yields only finite ranges; it cannot reach `2^270` (that is ≈ 10^81 values).

## 5. Measured cost and verified bound

**Update (final): literal capped form verified for every `n ≤ 10000`** (kernel, no sorry, no native_decide, axioms
propext/Classical.choice/Quot.sound): `BBPSpigotDigitCorrect_of_le_10000_unconditional`
(`Thoughts/Proved/BBPDigitsUnconditionalExt10000.lean`, combiner `BBPFastCertsAll10000` = `BBPFastCerts8299` for `n < 8300`
plus `BBPFastCertsT8300to10000` for `8300 ≤ n ≤ 10000`; 43 modules of 40 `n`, built one at a time, 32–59 s each, no OOM at CH=40).
The unbuildable CH=100 `Part83..100` were deleted. This is the literal capped form only up to 10000, NOT `PBBP01General`.

Earlier milestone: `BBPSpigotDigitCorrect_of_le_8299_unconditional` (every `n ≤ 8299`; `Thoughts/Proved/BBPDigitsUnconditionalExt8299.lean`,
aggregator `BBPFastCerts8299`, parts `BBPFastCerts10000Part0..82`, each 100 `n`). Prefix milestones also built and pushed:
`≤ 3099` (`Ext3099`), `≤ 5899` (`Ext5899`). Previous best on `main`: `n ≤ 2000`. The `n ≤ 2000` modules are untouched.

Cost (one `lake build` of one part at a time, `nice`, shared 8-core/16 GB box; wall times vary 2–3× with other tenants' load):

| n range of a 100-n part | wall (unloaded) | notes |
|---|---|---|
| ≈ 0–1000 | 25–40 s | |
| ≈ 3000–4000 | 45–55 s | |
| ≈ 5000–6000 | 60–75 s | |
| ≈ 7000–8200 | 85–130 s | |
| ≈ 8400 (Part84, CH=100) | killed at ~13 GB RSS | OOM; exit 137; one lean process |

Correction of an earlier claim in this work ("memory per module small"): that holds only at small `n`. One 100-n module near
`n ≈ 8400` needs > 13 GB resident in the kernel, so the module size had to be cut (CH=40 for `[8300, 10000]`, modules
`BBPFastCertsT8300to10000Part0..42`). Old big-number method for comparison: ≈ 1 s/n average, 8–11 GB, 17 min for `n ≤ 2000`.
New method: ≈ 0.3–1.3 s/n, one module at a time, a few GB below `n ≈ 5000`.
Failures seen along the way, all exit 137 (OOM kill) from running 3–4 lake jobs concurrently on the shared box, never a proof failure.
The box also rebooted once mid-run and lost the local build cache (Mathlib rebuilt, ~65 min); proofs unaffected.

Heuristic and Python replica (same arithmetic): no guard-search failure for `n ∈ [0, 10000]`, max `g = 8`.
CI note: the first PR run failed on an infrastructure error (elan could not download the toolchain, SSL error), not on Lean.
