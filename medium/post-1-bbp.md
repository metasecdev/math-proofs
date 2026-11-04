# You Can Compute a Hex Digit of π Without the Ones Before It. How Do You Know It's Right?

## A Lean 4 proof that gives an explicit, checked precision budget for every position

---

You can compute, say, the millionth hexadecimal digit of π without computing any of the 999,999 digits before it. All it takes is a finite sum and some modular arithmetic.

The trick comes from a 1997 paper by David Bailey, Peter Borwein and Simon Plouffe, and the formula carries their initials: **BBP**.

Anyone who has shipped numerical code will have the next question ready. The algorithm works with finite precision. Rounding error is real. So when it hands you a digit, **how do you know it's the right one?**

That question is what my project is about. I wrote a set of proofs in the Lean 4 proof assistant that answer it with an explicit formula, for every position n.

## The BBP trick in plain words

The BBP formula writes π as an infinite sum:

`π = Σ (k ≥ 0) 1/16ᵏ · ( 4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6) )`

The key thing is the `1/16ᵏ`. Multiplying π by 16ⁿ shifts its hexadecimal expansion n places to the left, the same way multiplying by 10ⁿ shifts a decimal. After the shift, the early terms of the sum turn into ordinary integer arithmetic that you can reduce modulo small numbers, and the later terms shrink fast. Add up a finite number of terms, look at the result, and the digit you want falls out. You never need the earlier digits.

For reference, π in hex starts `3.243F6A88…`. In the notation I use, `dₙ = ⌊16ⁿ·π⌋ mod 16`, so `d₀ = 3`, `d₁ = 2`, `d₂ = 4`, and so on.

## The precision problem

Every real implementation stops the sum somewhere and rounds somewhere, so it needs a **guard**: some extra hex digits of working precision beyond the one you want, so that accumulated error can't flip the answer.

How many extra digits are enough? That depends on something you don't know ahead of time: how close `16ⁿ·π` happens to be to a whole number. If the digits right after position n are a long run of `0`s or `F`s, then `16ⁿ·π` sits just above or just below an integer. A tiny error can then push the computed value across that integer and change the digit. To be safe there, you need more guard digits.

So "how much precision is enough?" turns into a classical question in number theory: **how close can `16ⁿ·π` get to an integer?**

## What I proved

The whole development is in Lean 4, on top of the Mathlib library. Everything below is a theorem checked by Lean's kernel.

**1. The BBP formula equals π.** The proof writes each term as an integral, sums a geometric series under the integral sign, and evaluates the result in closed form. This isn't new as a fact, and it isn't new as a formal proof either. Bertot, Rideau and Théry formalized the formula and a digit-extraction routine in Coq (Journal of Automated Reasoning, 2018) and used it to compute the billionth hex digit of π inside Coq. HOL Light's library contains the formula too. In Lean, Bastiaan Braams's lean-DLMF project has the identity as `hasSum_bbp_pi`. My proof was developed independently by a different route, and I don't claim priority for the identity.

**2. An integer-only certificate, with a soundness theorem.** For a position n and a guard depth g, the certificate computes two natural numbers, `lo` and `hi`, using only integer floors and sums. If `lo = hi`, then `lo` is exactly `⌊16ⁿ·π⌋`, so `lo mod 16` is the true digit `dₙ`. Checking `lo = hi` is a finite computation, so for any particular n and g the kernel can just run it.

That on its own is a "when it answers, it's right" guarantee. The Coq work proves the same kind of partial-correctness statement for its routine. As those authors point out, a routine that never answers would satisfy such a statement too. What's missing is a promise that the check will actually pass.

**3. An explicit irrationality-measure bound at powers of 16.** For every `k ≥ 1` and every integer p:

`|16ᵏ·π − p| · 16^(570k) > 2^(−7182802) · 16ᵏ`

In words: `16ᵏ·π` can't get closer to an integer than an explicit, if very small, amount. The proof follows Mahler's method (1953), in the form Mignotte used (1974), with every constant written out and checked. The exponent 570 is a long way from the best published bound in a journal that I know of, about 7.10 (Zeilberger and Zudilin, 2020). But the application doesn't need a small exponent. It needs a constant that is fully explicit and valid for every k, and that's what this bound provides.

**4. The main theorem: an explicit guard for every position.** Putting 2 and 3 together: for every `n ≥ 0`, the certificate returns the correct digit `dₙ` at every guard depth

`g ≥ 569n + ⌊log₁₆(n+1)⌋ + 1 + 1795710`

I also proved a simpler form: any `g ≥ 570n + 1795711` works. These are statements about every n, not a test over some range.

**5. Runs, distance and need.** A short chain of exact statements ties the precision question back to the digits themselves. Let ρ(n) be the length of the run of `0`s or `F`s starting right after position n, and let δₙ be the distance from `16ⁿ·π` to the nearest integer. For every n:

`16^(−(ρ(n)+1)) < δₙ < 16^(−ρ(n))`

Let `need(n)` be the smallest guard depth that the distance criterion certifies. It is pinned down to within one: it equals the run length ρ(n) plus a small logarithmic term, or one more than that. That makes the intuition above precise: each extra `0` or `F` in the run pushes the needed guard up by about one digit.

## What the guard means in practice

The numbers are big. At n = 0, the proved guard is 1,795,711 hex digits. The paper also lists least sufficient depths, computed numerically and not used in any proof: 2 at n = 0 and n = 1, 3 at n = 10, 4 at n = 100 and n = 1,000, and 7 at n = 1,000,000.

So the theorem isn't telling you to compute with millions of guard digits. Here's how it's meant to be used:

1. Run the cheap `lo = hi` check at a small guard depth.
2. If it passes, the soundness theorem says the digit is correct. Done.
3. If it doesn't pass, increase g and try again. The main theorem guarantees this stops, at a depth no larger than the formula above.

The formula is a ceiling on the search, not a recipe. The check can never come back inconclusive forever.

**A small worked example**, computed directly from the certificate's definition. Take position n = 1, the first hex digit after the point. The true value is `16·π = 50.265…`, so `⌊16π⌋ = 50` and `50 mod 16 = 2`, which is `d₁`.

- At guard depth g = 1, the certificate gives `lo = 49` and `hi = 51`. They disagree, so the certificate makes no claim. It doesn't guess.
- At g = 2, it gives `lo = hi = 50`. They agree, so by the soundness theorem `⌊16π⌋ = 50` and the digit is `50 mod 16 = 2`. Correct.

That matches the numerical table's least sufficient depth of 2 at n = 1.

## Why a proof assistant?

Because the claims are "for every n" and the constants are enormous: an exponent of 570, a constant of `2^(−7182802)`, an offset of 1,795,710. That's exactly the kind of argument where a hand proof can quietly drop a factor of 2. In Lean, every inequality, every constant and every case split is checked by a small trusted kernel.

The trust base is deliberately narrow:

- **No `sorry`.** That's Lean's "trust me" placeholder, and none remain.
- **Only Lean's three standard axioms:** `propext`, `Classical.choice` and `Quot.sound`. Running `#print axioms` on the key theorems lists nothing else, and CI fails if anything else ever appears.
- **`decide +kernel`, never `native_decide`.** Finite computations such as digit checks are evaluated by the kernel itself. `native_decide` would add the compiler to what you have to trust, so it isn't used anywhere.

**About the older "capped" certificate.** The repo also has an earlier certificate that only tries guard depths up to 64. It's proved correct for every n ≤ 10,000; the top part of that range was checked by a local build, because it needs more memory than CI runners have. It's also proved to return a wrong digit in an explicit, astronomically far-off window around n ≈ 2²⁷². The positions in between are **unchecked**: nothing is proved about them either way. That certificate lives in an appendix and isn't part of the main theorem, which uses the explicit guard instead.

## Check it yourself

The code is Apache-2.0 and the paper text is CC BY 4.0.

```
git clone https://github.com/metasecdev/math-proofs
cd math-proofs
lake exe cache get      # prebuilt Mathlib
lake build
lake env lean Thoughts/Axioms.lean   # prints the axioms each key theorem uses
```

The toolchain and Mathlib version are pinned. `Thoughts/Axioms.lean` runs `#print axioms` on each headline theorem, and `scripts/check_axioms.py` is the gate CI uses. The main theorem is `BBPPi.floor_digit_eq_guard570`, in `Thoughts/Research/BBPMu570b.lean`.

## What this is and isn't

This is a fully explicit, machine-checked answer to one engineering question: how much precision guarantees a correct hex digit of π at position n? The answer holds for every n.

It says nothing about whether π's digits are "random" or normal, and makes no statistical claims. The proved guard is far larger than what's needed in practice, and sharper explicit bounds would bring it down. That's open future work.

- **Code and paper:** https://github.com/metasecdev/math-proofs
- **Archived release (v1.0.1):** https://doi.org/10.5281/zenodo.23867088
- **All versions (concept DOI):** https://doi.org/10.5281/zenodo.23867087
- **The original BBP paper:** D. H. Bailey, P. B. Borwein, S. Plouffe, "On the rapid computation of various polylogarithmic constants," *Math. Comp.* 66 (1997). https://doi.org/10.1090/S0025-5718-97-00856-9

---

*[Author bio placeholder: Brian Bernard Taylor is an independent researcher working on cybersecurity, AI security and formally verified mathematics.]*

**Suggested Medium tags:** Mathematics · Pi · Formal Verification · Lean · Programming
