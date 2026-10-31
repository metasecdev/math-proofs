#!/usr/bin/env bash
# Source hygiene: no sorry, no native_decide, and no unrelated (SAT / P vs NP) modules.
set -euo pipefail
fail=0
if grep -rnwE "sorry|admit" --include='*.lean' BBPPi BBPPiCerts | grep -v -- '--' | grep -v '`sorry`'; then echo "FAIL: sorry/admit"; fail=1; fi
if grep -rn "native_decide" --include='*.lean' BBPPi BBPPiCerts | grep -v '`native_decide`' | grep -v 'no native_decide'; then echo "FAIL: native_decide"; fail=1; fi
if grep -rnE "^import .*(SAT|Twist|PeqNP|PvsNP|GapSeq|Thoughts)" --include='*.lean' BBPPi BBPPiCerts BBPPi.lean BBPPiCerts.lean ; then echo "FAIL: unrelated import"; fail=1; fi
[ "$fail" = 0 ] && echo "OK: hygiene"
exit $fail
