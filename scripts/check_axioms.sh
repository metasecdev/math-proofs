#!/usr/bin/env bash
# Print the axioms of every headline theorem and fail on anything beyond
# propext, Classical.choice and Quot.sound (in particular sorryAx or Lean.ofReduceBool).
set -euo pipefail
file="${1:-BBPPi/Axioms.lean}"
out="$(lake env lean "$file" 2>&1)"
printf '%s\n' "$out" | tee axioms-report.txt
if printf '%s\n' "$out" | grep -q "error"; then echo "FAIL: errors while checking axioms"; exit 1; fi
bad="$(printf '%s\n' "$out" | grep -o "depends on axioms: \[[^]]*\]" | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/ //g' | grep -v -x -e propext -e Classical.choice -e Quot.sound -e '' || true)"
if [ -n "$bad" ]; then echo "FAIL: unexpected axioms:"; printf '%s\n' "$bad" | sort -u; exit 1; fi
n="$(printf '%s\n' "$out" | grep -c "depends on axioms" || true)"
total="$(grep -c '^#print axioms' "$file")"
if [ "$n" != "$total" ]; then echo "FAIL: $n of $total theorems reported axioms (a theorem with no axioms or an error?)"; exit 1; fi
echo "OK: $n theorems use only propext, Classical.choice, Quot.sound"
