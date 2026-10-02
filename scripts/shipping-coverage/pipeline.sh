#!/usr/bin/env bash
# For every machine-route declaration of a measurement, evaluate the gates of
# the shipping theorem (`Tools.ShippingMachineShipping.machine_ships_full`)
# on the modules of a real run: the duplicate merge and the optimizer accepted
# by `refineCheck`, the reset port and the output ports present, the
# emitted-Verilog check and its width agreement.  Where they hold, the
# generated `f.machine_ships` says the optimized module and its emitted
# Verilog show the source declaration.
#
#   scripts/shipping-coverage/pipeline.sh WORKDIR [FILES.txt]
#
# WORKDIR is the directory of a completed `run.sh` pass 1.  Requires a
# completed `lake build Tests.AllTests`; must NOT run next to a `lake build`.
set -u
cd "$(dirname "$0")/../.."
WORK="$1"
HERE="scripts/shipping-coverage"
mkdir -p "$WORK/pipeline_jobs"
sed "s#@WORK@#$WORK#g" "$HERE/pipeline_tail.lean.in" > "$WORK/pipeline_tail.lean"
: > "$WORK/pipeline_reasons.txt"
if [ $# -ge 2 ]; then cat "$2"; else grep " 0$" "$WORK/status.txt" | awk '{print $1}'; fi \
  | grep -v "^Tests/AllTests.lean$" | nl -w1 -s' ' > "$WORK/pipeline_jobs/list.txt"
run_one() {
  i="$1"; f="$2"; job="$WORK/pipeline_jobs/p$i.lean"
  { echo "import Tools.ShippingMachineShipping"; cat "$f" "$WORK/pipeline_tail.lean"; } > "$job"
  timeout -k 5 1500 lake env lean --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so "$job" \
    > /dev/null 2>&1
  rm -f "$job"
}
export -f run_one; export WORK
xargs -P 3 -L 1 bash -c 'run_one "$0" "$1"' < "$WORK/pipeline_jobs/list.txt"
python3 "$HERE/report.py" pipeline "$WORK"
