#!/bin/bash
# usage: s2s_step.sh ORIG NEW   (ORIG module without Tools.; NEW suffix after ShippingFGCircuitS2sAdm). Imports all previously ported 'late' modules listed in scripts/s2s_late.txt.
cd "$(dirname "$0")/.."
late=$(cat scripts/s2s_late.txt | sed 's/^/Tools.ShippingFGCircuitS2sAdm/' | tr '\n' ' ')
bash scripts/s2s_mk.sh "$1" "ShippingFGCircuitS2sAdm$2" $late | tail -1
bash scripts/s2s_b.sh "Tools.ShippingFGCircuitS2sAdm$2" ${3:-20}
