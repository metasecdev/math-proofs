# arXiv submission — copy-paste fields

Prepared 1 Nov 2026 (ET) from metasecdev/math-proofs main @ ff1918c (paper/main.tex, paper/refs.bib).
Submit at: https://arxiv.org/submit  (log in / register at https://arxiv.org/user/register first)
Upload file: `math-proofs-arxiv.tar.gz` (main.tex, main.bbl, refs.bib). sha256 d3a351558c650b5b7a506285eb4c6684a99acd948b1ff493000bdbda6d30a344

## License (Step 1)
CC BY 4.0 — "Creative Commons Attribution 4.0 International" (matches paper/LICENSE-CC-BY-4.0). Note: arXiv licenses are irrevocable once the paper is announced.

## Archive / category
- Primary: **math.NT** (Mathematics — Number Theory)
- Cross-list: **cs.LO** (Computer Science — Logic in Computer Science)

## Title
A formally verified hexadecimal digit extraction for $\pi$ with an explicit guard for every position

## Authors
Brian Bernard Taylor

## Abstract
We describe a Lean 4 development, built on Mathlib, about the Bailey-Borwein-Plouffe (BBP) formula for $\pi$. It contains an independent proof that the BBP series equals $\pi$, an integer-only certificate for the hexadecimal digit $d_n = \lfloor 16^n \pi \rfloor \bmod 16$, and a soundness theorem: when the two ends of the certificate's bracket agree, the certified digit is the true digit. To remove the dependence on that check, we formalize an explicit irrationality-measure bound at the denominators $16^k$: for every $k \ge 1$ and every integer $p$, $|16^k \pi - p| \cdot 16^{570k} > 2^{-7182802} \cdot 16^k$. Our main theorem shows that for every $n \ge 0$ the certificate returns $d_n$ at every guard depth $g \ge 569n + \lfloor \log_{16}(n+1) \rfloor + 1 + B$ with $B = 1795710$; a simplified linear form of the guard is also proved. We also prove a short chain of exact statements relating the run of 0s or Fs after position $n$, the distance from $16^n \pi$ to the nearest integer, and the least sufficient guard depth. All statements are for every $n$ or for explicit finite ranges; no asymptotic, probabilistic or normality claim is made. The proofs use only the axioms propext, Classical.choice and Quot.sound, and no native_decide.

(1246 characters; limit is 1920.)

## Comments
10 pages, 2 tables. Lean 4 formalization: https://github.com/metasecdev/math-proofs, archived at doi:10.5281/zenodo.23867088

## Report number
(blank)

## Journal reference
(blank — only fill after journal publication)

## DOI
(blank — the Zenodo DOI is for the software, not this paper; it is already in Comments)

## MSC class
11Y60, 11J82, 68V20

- 11Y60 — Evaluation of number-theoretic constants (π digit extraction)
- 11J82 — Measures of irrationality and of transcendence (the explicit bound at 16^k)
- 68V20 — Formalization of mathematics in connection with theorem provers (the Lean 4 development)
These match the paper's own \subjclass[2020] line.

## ACM class (optional)
F.4.1

(F.4.1 = Mathematical Logic, which includes mechanical theorem proving; arXiv uses the 1998 ACM scheme. Can be left blank.)

## Endorsement
arXiv requires endorsement before a first submission to a category (https://info.arxiv.org/help/endorsement.html).
Automatic endorsement mainly comes from an institutional email and/or claimed prior papers. With a gmail account
and no prior arXiv papers, expect to be asked for a personal endorsement for math: arXiv emails a 6-character
endorsement code/link after you start the submission and pick math.NT; send it to an established arXiv author
in the field (one who knows you or will look at the paper). Use "Which authors of this paper are endorsers?" on
related arXiv abstract pages (e.g. arXiv:1709.01743, cited in refs) to find eligible endorsers; don't mass-email.
