#!/bin/bash
# usage: s2s_mk.sh ORIGMODULE NEWNAME [EXTRA_IMPORT...]  (ORIGMODULE without Tools. prefix)
set -e
cd "$(dirname "$0")/.."
orig=$1; new=$2; shift 2
imps="Tools.$orig Tools.ShippingFGCircuitS2sAdmLawsX Tools.ShippingFGCircuitS2sAdmS2hHist Tools.ShippingFGCircuitS2sAdmS2hHist2"
for f in Tools/ShippingFGCircuitS2sAdmChild*.lean Tools/ShippingFGCircuitS2sAdmKWalk.lean; do b=$(basename $f .lean); imps="$imps Tools.$b"; done
for f in Tools.ShippingChildRunAKids Tools.ShippingChildComposeC; do imps="$imps $f"; done
for e in "$@"; do imps="$imps $e"; done
python3 scripts/s2s_port2.py Tools/$orig.lean Tools/$new.lean $imps
grep -q "lean_lib «Tools.$new»" lakefile.lean || printf '\nlean_lib «Tools.%s» where\n  roots := #[`Tools.%s]\n' $new $new >> lakefile.lean
