# Review of the MacBook Air July 2026 Lean work (BBP/π scope only)

Date: 2026-11-01 (ET). Source: `/workspace/mac-import/mac-math-20261101/` (read only, nothing in it was changed).
Compared against: `metasecdev/math-proofs` main @ `9520112` (`/workspace/mp-release`).
Out of scope: P vs NP, Möbius, SATWitness, PeqNPBridge and Lean/PNP. These belong to Geometric Related Proofs (GRP). Where they overlap with this work, the overlap is noted only.

## Method and load
- Static scan for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `@[implemented_by]`, `opaque` and `partial def`.
- Compile checks used Lean v4.29.0-rc8 with the existing pre-built Mathlib `816ff45` from `/workspace/igm`. That is the same toolchain and Mathlib commit as math-proofs.
- Compiles were single files, run one at a time under `nice -n 19 ionice -c3`. Each took a few seconds.
- No Mathlib download and no Mathlib build.
- The scratch copies are in `/workspace/mac-check/` (imports renamed to `MacCheck.*`).
- I ran `#print axioms` and `#eval` checks in `/workspace/mac-check/src/Audit.lean` and `Legacy.lean`. True π hex digits came from mpmath at 150 digits.
- Toolchains differ: Lean/PNP is on v4.33.0-rc1 (the GRP side). `igm-compare` has no `lean-toolchain` file; PROJECTS_SUMMARY says it is v4.29.0-rc8.

## Per-file verdicts

| File | What it claims | Honesty scan | Compiles (v4.29.0-rc8) | Verdict |
|---|---|---|---|---|
| `Thoughts__Proved__BBPAlgebra.lean` (44 lines) | Algebraic BBP term identities | clean | Yes | **Covered**: byte-identical to main |
| `Thoughts__Proved__BBPSeries.lean` (164 lines) | Defines `bbpSeries`; head/tail split; scaled tail < 1; `BBPPiEqualsSeries` as a Prop (not an axiom) | clean; axioms = propext, Classical.choice, Quot.sound | Yes | **Covered**: byte-identical to main. Main also *proves* `bbpSeries_eq_pi` (BBPPiIdentity.lean:219) |
| `Thoughts__Proved__BBPTail.lean` (516 lines) | Tail bounds; spigot-term lemmas; `bbp_term` | clean axioms, but `bbp_term` is the **legacy mis-scaled** term (no 1/16^k) | **No**: line 270 has an extra `contradiction` ("No goals to be solved"). OK once that line is deleted (scratch copy only) | **Covered / older**: main (595 lines) has the fix, renamed the term to `bbp_term_legacy` with a warning, and has nothing missing from the mac version |
| `Thoughts__Proved__BBPSpigot.lean` (503 lines) | "Tier-1" digit theorems (n=5,17,18,24,29,32,40,42); P-BBP-01 cluster candidates; gap/SAT links | **8 `native_decide`**; imports `BBPIntDigit` (not in the import) plus `Normality`, `SATWitness` and `GapSeqSpigot` (the P vs NP side). The one `sorry` hit is a comment | **No** (missing modules); also fails policy because of native_decide | **Overclaimed, superseded**: see below |
| `Thoughts__Proved__Normality.lean` (112 lines) | Normality / gap equidistribution (H-01, C-01) | `partial def` ×2, `@[implemented_by]`; `gapSeqSAT := syntheticGap := i % 3` | Yes | **Wrong / overclaimed; not importable** (normality is excluded by the finitist rules) |
| `Thoughts__Proved__GapSeqSpigot.lean` (254 lines) | Spigot-derived gap sequence | `implemented_by` ×3, `partial def` ×2; marker `n % 3 = 0` is synthetic, not π | Yes | **Overclaimed; not π content**; it feeds the SAT side (GRP overlap) |
| `Thoughts__FinitistConsolidated.lean` | `pi_is_normal_proved`, `pi_is_normal_spigot_proved` | `PiIsNormal := GapSeqMod3Equidistribution gapSeqSAT` | not compiled (P vs NP dependency chain) | **Major mislabel**: it proves that `i % 3` is periodic, **not** that π is normal |
| `FinitstUnified_all__FinitistUnified_cleaned.lean` | Spigot bridge to π digits | 6 axioms, including `bbp_pi_away_from_integer_boundaries` / `_hex_boundaries` for **all n** with ε = 1/64 | not compiled | **Inconsistent**: the axiom is **false at n=24** (frac(16²⁴π) = 0.01343… < 1/64) |
| `FinitstUnified_all__FinitistFramework_linarith_FINAL.lean` | "ZERO SORRY … BBP proved … P=NP closed" | 8 axioms, including `pi_is_normal` and `bbp_tail_bound` | not compiled | **Inconsistent**: `bbp_tail_bound` is false (legacy `bbp_tail 1 = 17,895,712`, not < 1), and `pi_is_normal` is refutable at N=0. With either one you can prove `False`, so "zero sorry" means nothing here |
| `FinitistUnitifed_4_12_2026.lean`, `fixed_compile_scaffold` | BBP digit correctness | `axiom BBPDigitCorrect : Nat → Prop` plus `axiom … : BBPDigitCorrect n` (the scaffold also has `axiom bbp_tail_bound`) | not compiled | **Vacuous**: the axiom says nothing about π |
| `FinitstUnified_all__P_NP_almost.lean` | hex digit of π correct for all n | `axiom bbp_pi_hex_digit_correct` (5 axioms) | not compiled | **Unproven assumption** (not known to be false). Main's explicit guard (`bbp_explicit_guard_all_n'`) is the honest, proved version |
| `no_sorry.lean`, `FinitistFramework_final.lean` | normality of π | `axiom pi_is_normal`; `_final` also has 20 `sorry` | not compiled | **Overclaimed** (normality is assumed, not proved) |
| `FinitistUnified_all.lean` (37 axioms) | unified P=NP scaffold | – | does not compile (its own summary says so: undefined symbols) | Out of scope apart from the BBP axioms noted above |
| `PROVEN_RECORD.md` (2026-06-08) | P-01..P-22 "proved" | partly honest: it itself flags the mis-scaled `bbp_tail` and the dependence on H-01..H-03 | – | **Overclaims**: P-10, P-14, P-16 and C-02 ("PiIsNormal proved", "H-01 proved") |
| `PROJECTS_SUMMARY.md` (2026-06-03) | Status overview | – | – | Mostly honest ("No file establishes P = NP … without heavy axioms or sorry") |
| `ARA_NOTE.md` | "8 Tier-1 stable, 0 sorries, builds green"; asks for GPU-cluster runs | – | – | **Overclaimed**: Tier-1 is conditional and uses native_decide; GPU runs are not needed (see below) |

## The "Tier-1" BBP digit results (BBPSpigot.lean / ARA_NOTE)
- **Conditional.** Each `BBPSpigotDigitSpigotCertGapCorrect_*_of_hz` takes `hz` as a hypothesis. `hz` is exactly the gap/floor fact that needs proving. The chain also assumes `BBPPiEqualsSeries` and `BBPIntSeriesBracketUpper`.
- **native_decide.** The certificate evaluations (`bbpHexDigitSpigotCert_{five,eighteen,twenty_four,forty_two}`, `bbpHexDigitOfGapFloorZ_spigot_*`) use `native_decide`. That trusts the compiler, not the kernel.
- **Cherry-picked coincidences.** The legacy certificate `bbp_hex_digit` / `bbpHexDigitCert` is mis-scaled. For n = 0..46 it matches π's true hex digit **only at n = 17, 29, 32, 40**: 4 of 47 places, about what chance gives (1/16). Those are exactly the n used by the "cert-gap" Tier-1 theorems. `BBPSpigotDigitCorrect n` (defined against that legacy cert) is **false for most n**; for example n=0 gives 4, but the true digit is 2.
- The digit values quoted for n=5, 18, 24, 42 (A, 1, 0, 9) are correct π digits. Main already proves every digit up to n = 10000 with kernel `decide` and no hypotheses (`BBPDigitsUnconditional*`). It also has an all-n explicit-guard theorem (`bbp_explicit_guard_all_n'`, `PBBP01ExplicitGuard_proved`) and the identity `bbpSeries_eq_pi`. Note that main uses `⌊16ⁿπ⌋ mod 16` (digit n counted from 1), while the mac files use `⌊16·frac(16ⁿπ)⌋` (counted from 0), so digit numbers are offset by one between them.
- `PBBP01Cluster*Candidate` are only Props about which n are in a set (labelled "Not proved in Lean").

## Normality items
- `GapSeqEquidistribution` (the ℝ statement with a 20·log N / N bound, which is also the `PiIsNormal` axiom in linarith_FINAL) is **refutable**. At N = 0 the right side is 0 and the left side is 1/m > 0. I proved `¬GapSeqEquidistribution` in scratch with only the standard axioms. So C-01 `gap_density_mod_m` rests on a false premise.
- `syntheticGap_mod3_equidistribution` (labelled "proved H-01") is a true but trivial fact about `i % 3`. It says nothing about π.

## Axiom audit (scratch `#print axioms`)
- All proved BBPAlgebra, BBPSeries and BBPTail theorems use only `[propext, Classical.choice, Quot.sound]`.
- The `syntheticGap` theorems use `[propext]`.

## Import decision
**No PR.**
- Every correct BBP piece is either byte-identical to main (Algebra, Series) or an older version of main's file (Tail).
- The mac-only BBPSpigot content is one of three things: conditional and native_decide based (and weaker than main's unconditional proofs), built on the wrong legacy certificate, or SAT/gap material for P vs NP.
- Normality.lean and GapSeqSpigot are excluded by the finitist rules (and Normality.lean by name) and are not about π anyway.

Nothing is both new and correct, so math-proofs was not touched.

## Overlap notes for GRP
- `BBPSpigot.lean` carries SAT content: `GapSeqMod3Correct`, `ClauseSumWitnessedBBP`, and imports of `SATWitness` / `GapSeqSpigot`.
- `Normality.lean` and `GapSeqSpigot.lean` define `gapSeqSAT = i % 3`, which the P vs NP files use.
- `FinitistConsolidated`'s `PiIsNormal` mislabel and the inconsistent axioms in `linarith_FINAL` / `FinitistUnified_cleaned` show up in the "P=NP closed" headers.
- Lean/PNP uses Lean v4.33.0-rc1.
These were not analyzed further or imported.

## Plain-language verdict for Brian
Your July BBP work is on track wherever it was correct. The algebra, series and tail-bound files are the same as, or earlier versions of, what is already in math-proofs, and they check cleanly. The mac copy of BBPTail fails one line on the current Lean, which main already fixed. The "Tier-1" digit theorems are not real wins: they assume the hard step, use the compiler shortcut native_decide, and their n values are just the 4 places where the old wrong formula happens to match π. math-proofs already proves every digit up to 10,000 and the BBP-equals-π identity with no assumptions, so the GPU-cluster plan in ARA_NOTE isn't needed. The "π is normal, proved" labels are wrong: they prove a fact about the repeating pattern 0,1,2 of i mod 3, and two of the "zero sorry" files rest on axioms I can show are false, which makes those files prove anything. Nothing new needed importing, so I opened no pull request.
