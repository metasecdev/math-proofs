import Thoughts.Proved.BBPDigitsUnconditionalExt10000

/-!
# Axiom audit for the heavy certificates (library `BBPHeavyCerts`)

NOT run by CI: CI does not build `BBPHeavyCerts` (more than 10 GB of RAM per Lean process).
Run on a large machine:

    lake build BBPHeavyCerts
    lake env lean Thoughts/AxiomsHeavy.lean 2>&1 | tee axioms-heavy.log
    python3 scripts/check_axioms.py axioms-heavy.log

Paper, Table 2, Appendix A (capped certificate correct for every `n ≤ 10000`).
-/

#print axioms FinitistProved.bbpGuardAgrees_of_lt_10001
#print axioms FinitistProved.BBPSpigotDigitCorrect_of_le_10000_unconditional
