# math-proofs

Lean 4 formalization of the Bailey–Borwein–Plouffe (BBP) formula for π and of
guarded, finitely checkable certificates for the hexadecimal digits of π.

**Author:** Brian Bernard Taylor (sole author).

## Scope

This repository contains only the BBP / π work. In particular:

1. **The BBP identity.** π = Σₖ 16⁻ᵏ (4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)),
   proved in Lean against Mathlib's `Real.pi` (`bbpSeries_eq_pi`).
2. **Guarded digit certificates.** A natural-number interval `[lo, hi]` computed from the
   BBP series with an explicit tail guard `g`. Whenever `lo = hi` (a decidable check), the
   common value is provably `⌊16ⁿ·π⌋`, so its residue mod 16 is the `n`-th hex digit of π.
   Concrete instances are checked by the Lean kernel (`decide +kernel`).
3. **An effective irrationality-measure bound for π in base 16.** A Mahler-style
   argument giving an explicit lower bound on `|16ᵏ·π − p|` for all integers `p` and all
   `k ≥ 1`. It yields an explicit linear guard `g(n)` that certifies the `n`-th hex
   digit of π for every `n`.

Not claimed here: anything about the normality of π, digit statistics beyond what is
stated in the Lean files, or results outside the BBP / π programme.

## Finitist framing

Every digit statement reduces to a computation on natural numbers: finite sums of integer
BBP terms, a finite guard, and an equality check `lo = hi`. Real analysis enters only to
connect that finite check to `Real.pi`, through the BBP identity and an explicit tail
bound. The kernel checks all certificates; no external oracle or compiled evaluation is
trusted.

## Trust base

* No `sorry`, and no `native_decide` (so `Lean.ofReduceBool` never appears).
* `#print axioms` on the key theorems may list only Lean's three standard axioms:
  `propext`, `Classical.choice`, `Quot.sound`. CI fails on anything else.

## Building

```
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

The toolchain is pinned in `lean-toolchain`. The Mathlib revision is pinned in
`lakefile.lean` and `lake-manifest.json`.

## Provenance

The code was imported from the author's development repository; each import commit
records the source repository and commit SHA.
