#!/bin/sh
# FG circuit pilot S1q: print only the output of Tests.Gen5.FGCircuitPilotCompare15 (IR + SV text of the 5 roots) from a `kjob lake build` log on stdin.
# usage: kjob lake build Tests.Gen5.FGCircuitPilotCompare15 2>&1 | scripts/gen5/fgc_s1q/extract.sh > out.txt
awk '/Built Tests.Gen5.FGCircuitPilotCompare15/{p=1; next} p' | grep -v '^{"event_id"' | grep -v '^Build completed' | grep -v '^real\|^user\|^sys'
