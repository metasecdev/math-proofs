# arXiv endorsement for math.NT: candidates, draft request, process notes

Prepared Sun 1 Nov 2026, about 4:30 PM ET. **No one has been contacted.**

Paper: "A formally verified hexadecimal digit extraction for π with an explicit guard for every position" by Brian Bernard Taylor (Independent Researcher).
Code: https://github.com/metasecdev/math-proofs, Zenodo doi:10.5281/zenodo.23867088

## How the checks were done
- Every arXiv ID below was checked against the arXiv API and its abs page (title and authors match, HTTP 200).
- **"Which authors are endorsers?" page** (`https://arxiv.org/auth/show-endorsers/<id>`): every ID returned **HTTP 401, login required**, so endorser status is **not verified** for anyone. Brian can open these links himself while logged in to arXiv.
- **The eligibility rule I applied** (arXiv help page): an endorser needs enough papers in the endorsement domain, here math, submitted between **3 months and 5 years ago**. Below, "likely eligible" means they have math papers in that window. It is an inference only.
- Emails are listed only where they are printed on the person's own public page.

## Candidates, best fit first

| # | Name | Affiliation | Relevant arXiv paper | Why relevant | Contact page | Endorser likely? |
|---|------|-------------|----------------------|--------------|--------------|------------------|
| 1 | **Wadim Zudilin** | Radboud University Nijmegen (Professor of Pure Mathematics) | [arXiv:2510.00215](https://arxiv.org/abs/2510.00215), Cohen & Zudilin, *Continued Fractions and Irrationality Measures for Chowla–Selberg Gamma Quotients* (math.NT, 2025). Also co-author of the paper's cited [arXiv:1912.06345](https://arxiv.org/abs/1912.06345) (irrationality measure of π ≤ 7.103…) | Leading expert on irrationality measures; cited in the paper | https://www.math.ru.nl/~wzudilin/ and https://www.ru.nl/en/people/zudilin-v (email printed there: w.zudilin@math.ru.nl) | Yes (many math.NT papers 2025–26) |
| 2 | **David H. Bailey** | Senior Scientist (retired), Lawrence Berkeley National Laboratory; Research Associate, UC Davis CS | [arXiv:2604.02384](https://arxiv.org/abs/2604.02384), Bailey, McPhedran & Salvy, *General formulas for a class of Euler sums* (math.NT, Apr 2026). Also [arXiv:2311.06294](https://arxiv.org/abs/2311.06294) (math.NT, 2023) | Co-author of the BBP formula (cited as BBP 1997) | https://www.davidhbailey.com/ (his CV PDF prints dhbailey@lbl.gov) | Yes (2311.06294 is inside the window; 2604.02384 just reaches it) |
| 3 | **David Loeffler** | UniDistance Suisse (Full Professor; formerly Warwick) | [arXiv:2503.00959](https://arxiv.org/abs/2503.00959), Loeffler & Stoll, *Formalizing zeta and L-functions in Lean* (math.NT, 2025) | Number theorist who formalizes in Lean/Mathlib; an exact match for a math.NT Lean paper | https://unidistance.ch/en/profile/david-loeffler (his Warwick page prints "David dot Loeffler at unidistance dot ch") | Yes (several math.NT papers 2024–25) |
| 4 | **Michael Stoll** | Universität Bayreuth (Chair of Computer Algebra) | [arXiv:2503.00959](https://arxiv.org/abs/2503.00959), same paper as #3 | Computational number theory plus Lean formalization | https://www.mathe2.uni-bayreuth.de/stoll/ | Likely (co-author of 2503.00959) |
| 5 | **Alex Kontorovich** | Rutgers University (Distinguished Professor, Chair of Mathematics) | [arXiv:2409.17248](https://arxiv.org/abs/2409.17248), *Sign changes along geodesics of modular forms* (math.NT, 2024). Lean work: [arXiv:2610.17331](https://arxiv.org/abs/2610.17331) (mini-Lean-agent, cs.AI, 2026) | Analytic number theorist who is active in Lean formalization | https://sites.math.rutgers.edu/~alexk/ | Yes (math.NT 2024) |
| 6 | **Doron Zeilberger** | Rutgers University (Board of Governors Professor) | Co-author of the cited [arXiv:1912.06345](https://arxiv.org/abs/1912.06345) (math.NT). Recent: [arXiv:2609.25098](https://arxiv.org/abs/2609.25098), *Approximating Pi (and other constants) by Radicals…* (math.HO, Sep 2026) | Cited in the paper; experimental/computer-assisted math, including π | https://sites.math.rutgers.edu/~zeilberg/ | Yes (many math papers, though mostly math.CO/HO) |
| 7 | **Simon Plouffe** | Affiliation not verified as current; personal homepage | [arXiv:2201.12601](https://arxiv.org/abs/2201.12601), *A formula for the nth decimal digit or binary of π and powers of π* (math.NT, 2022). Also [arXiv:2510.06688](https://arxiv.org/abs/2510.06688) (math.NT, 2025) | Co-author of BBP (cited); digit-extraction formulas for π | https://www.plouffe.fr/ | Likely (math.NT 2022, 2023, 2025) |
| 8 | **Timothy Trudgian** | UNSW Canberra (Professor) | [arXiv:2303.13785](https://arxiv.org/abs/2303.13785), Johnston, Ramaré & Trudgian, *An explicit upper bound for L(1,χ) when χ is quadratic* (math.NT, 2023) | Explicit-constant number theory, which matches the paper's explicit guard B | https://www.unsw.edu.au/staff/timothy-trudgian | Likely (math.NT 2023) |

### Highly relevant, but probably not able to endorse for math right now
- **Gregory V. Chudnovsky** (NYU Tandon, Distinguished Industry Professor, https://engineering.nyu.edu/faculty/gregory-chudnovsky): [arXiv:2610.26539](https://arxiv.org/abs/2610.26539), *The irrationality exponent of the lemniscate period: A determinant proof with a Lean 4 formalization* (math.NT, 19 Oct 2026). This is the closest topical match: irrationality exponents plus Lean 4. But all three of his arXiv papers under this name date from Oct 2026, under the 3-month minimum, so he is probably **not yet eligible**. Better kept as a later contact than as an endorser.
- **Laurent Théry and Yves Bertot** (Inria Sophia Antipolis; https://www-sop.inria.fr/marelle/Laurent.Thery/ and https://www.inria.fr/en/yves-bertot): [arXiv:1709.01743](https://arxiv.org/abs/1709.01743), *Distant decimals of π* (cs.LO, 2017; cited in the paper). Their arXiv papers are cs.LO and mostly older than 5 years, so they are **probably not math endorsers**. Note that cross-listing to cs.LO does not need a separate endorsement; only the primary category does.

**Suggested order:** Zudilin, then Bailey, then Loeffler, then Kontorovich. Write to **one person at a time** and wait about a week before trying the next. arXiv says emailing many potential endorsers at once is inappropriate.

## Draft endorsement request (plain text, from Brian, about 160 words)

Subject: arXiv endorsement request (math.NT): formally verified BBP digit extraction for pi

Dear Professor [NAME],

I am an independent researcher preparing my first arXiv submission, to math.NT, and I am writing to ask whether you would consider endorsing me.

The paper, "A formally verified hexadecimal digit extraction for pi with an explicit guard for every position," gives a Lean 4 proof that pi equals the Bailey–Borwein–Plouffe series. It then proves an explicit number of guard digits that is sufficient for correct hexadecimal digit extraction at every position n, using an irrationality-measure bound for pi at powers of 16. Ranges beyond what is proved are reported as unchecked.

The Lean code is public and depends only on Lean's standard axioms (propext, Classical.choice, Quot.sound), with no sorry:
https://github.com/metasecdev/math-proofs
doi:10.5281/zenodo.23867088

I would be glad to send the PDF. If you are willing, my endorsement code is [ENDORSEMENT CODE], or you can use this link: [ENDORSEMENT LINK].

Thank you for your time.

Brian Bernard Taylor
Independent Researcher
admin@metasecdev.com

(Before sending: replace [NAME]; optionally add one sentence on why you chose them, e.g. "your work on irrationality measures of pi"; attach the PDF or offer it.)

## arXiv endorsement process (from https://info.arxiv.org/help/endorsement.html)
- **Who needs it:** first submissions, and first submissions to a new category. Most top-level areas, including **math**, are a single endorsement domain. At least one positive endorsement is needed. Cross-lists such as cs.LO do not need their own endorsement.
- **Automatic route:** an account can be endorsed automatically if it has claimed papers **and** uses an email that meets arXiv's institutional-email criteria. admin@metasecdev.com is a custom domain and probably does not meet those criteria, so Brian should expect to need a personal endorsement.
- **The code:** once you start a submission and choose the category, arXiv emails a request with a **six-character alphanumeric endorsement code** and a link. You forward that to the potential endorser, who enters the code on the endorsement form at https://arxiv.org/auth/endorse (login required) and records yes or no. The endorser's decision is private.
- **If the email is missing:** log in at https://arxiv.org/user/ and look for the endorsement-request link for the category on the user page or in the paused submission. Opening https://arxiv.org/auth/need-endorsement while logged in also shows it; I checked that this URL exists and redirects to the login page. Also check the spam folder of admin@metasecdev.com.
- **Finding endorsers:** at the bottom of each abstract page, the link "Which of these authors are endorsers?" lists eligible authors. It requires login, which is why it is unchecked above.
- **Eligibility:** endorsers need a set number of papers in the domain, submitted between 3 months and 5 years ago, and must themselves be endorsed in that domain.
- **What endorsers check:** it is not peer review. They check that the paper is appropriate for the subject area, and they should have seen the paper or know the author, so offering the PDF helps.
- **Etiquette:** no mass emails, and no repeated emails to the same person. Only the author's own work may be submitted.
