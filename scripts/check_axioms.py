#!/usr/bin/env python3
"""Axiom / trust-base gate for math-proofs CI.

Usage: check_axioms.py LOG [LOG ...]

* Parses every `#print axioms` result found in the given Lean/Lake logs.
  Fails if any reported axiom is outside {propext, Classical.choice, Quot.sound}
  (this catches `sorryAx` and `Lean.ofReduceBool`, i.e. `sorry` and `native_decide`).
* Fails if a log reports a declaration using `sorry`, or any Lean error.
* Scans the Lean sources of the repository (comments and strings stripped) and fails on
  `sorry`, `admit`, `native_decide`, `axiom` declarations, `implemented_by`, `extern`.
* Fails if no `#print axioms` result was found at all (guard against a silent no-op).
"""
import os
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DEP_RE = re.compile(r"'(.+?)' depends on axioms: \[(.*?)\]", re.S)
NODEP_RE = re.compile(r"'(.+?)' does not depend on any axioms")
FORBIDDEN_TOKENS = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*axiom\s", re.M), "axiom declaration"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by"),
    (re.compile(r"@\[\s*extern\b"), "extern"),
    (re.compile(r"\bdecide\s*\+native\b|\bDecidable\.decide_eq_true_native\b"), "native decide"),
]


def strip_lean(src: str) -> str:
    """Remove nested block comments, line comments and string literals."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth:
            if src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = j + 1
            out.append('""')
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def main() -> int:
    failures = []
    results = {}
    text = ""
    for log in sys.argv[1:]:
        text += Path(log).read_text(errors="replace") + "\n"
    for name, axs in DEP_RE.findall(text):
        results[name] = sorted(a.strip() for a in axs.replace("\n", " ").split(",") if a.strip())
    for name in NODEP_RE.findall(text):
        results[name] = []
    if not results:
        failures.append("no `#print axioms` output found in the logs")
    for name, axs in sorted(results.items()):
        bad = [a for a in axs if a not in ALLOWED]
        if bad:
            failures.append(f"{name}: non-standard axioms {bad}")
    if re.search(r"declaration uses 'sorry'", text):
        failures.append("a declaration uses 'sorry' (see logs)")
    for line in text.splitlines():
        if re.match(r"\s*(error|✖)", line) or re.search(r"\berror:", line):
            failures.append(f"log error: {line.strip()[:200]}")
    root = Path(__file__).resolve().parent.parent
    scanned = 0
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        scanned += 1
        body = strip_lean(p.read_text(errors="replace"))
        for rx, what in FORBIDDEN_TOKENS:
            for m in rx.finditer(body):
                line = body.count("\n", 0, m.start()) + 1
                failures.append(f"{p.relative_to(root)}:{line}: forbidden `{what}`")

    # Summary
    sets = {}
    for name, axs in results.items():
        sets.setdefault(", ".join(axs) or "(none)", []).append(name)
    lines = ["## Axiom report", "",
             f"`#print axioms` results parsed: **{len(results)}**; Lean files scanned: **{scanned}**", "",
             "| axioms | # declarations |", "|---|---|"]
    for k, v in sorted(sets.items()):
        lines.append(f"| {k} | {len(v)} |")
    lines += ["", "<details><summary>All declarations</summary>", "", "```"]
    lines += [f"{n}: [{', '.join(a)}]" for n, a in sorted(results.items())]
    lines += ["```", "</details>", ""]
    if failures:
        lines += ["### FAILURES", ""] + [f"- {f}" for f in failures]
    else:
        lines += ["**OK**: only propext / Classical.choice / Quot.sound; no sorry, no native_decide."]
    report = "\n".join(lines)
    print(report)
    summ = os.environ.get("GITHUB_STEP_SUMMARY")
    if summ:
        with open(summ, "a") as fh:
            fh.write(report + "\n")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
