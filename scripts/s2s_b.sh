#!/bin/bash
# build one target, log to $S4LOG, print errors and the end of the log
cd "$(dirname "$0")/.."
L=${S4LOG:-/tmp/s4build.log}
kjob lake build "$1" > $L 2>&1
grep -n "error:" $L | cut -c1-300 | head -${2:-12}
grep -E "Build completed|build failed" $L
grep -c "sorryAx" $L | sed "s/^/sorryAx lines: /"
