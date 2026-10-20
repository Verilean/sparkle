#!/usr/bin/env bash
# Cross-check every machine-route module of a measurement against its SOURCE
# by simulation: the emitted module is run with the IR semantics
# (`Sparkle.IR.Semantics.runModule`) for 60 cycles on fixed input streams,
# the source declaration is evaluated by Lean on the same streams
# (`Signal.val`), and every output port is compared at every cycle.
#
#   scripts/shipping-coverage/simulate.sh WORKDIR [FILES.txt]
#
# WORKDIR is the directory of a completed `run.sh` pass 1.  This is evidence,
# not proof — the proof is the generated endpoint (`endpoints.sh`) — but it
# exercises what the theorems do not: the module the entry actually returns
# in this environment, including the runtime-gated `closeLets`.
#
# Requires a completed `lake build Tests.AllTests`; must NOT run next to a
# `lake build`.
set -u
cd "$(dirname "$0")/../.."
WORK="$1"
HERE="scripts/shipping-coverage"
mkdir -p "$WORK/simulate_jobs"
sed "s#@WORK@#$WORK#g" "$HERE/simulate_tail.lean.in" > "$WORK/simulate_tail.lean"
: > "$WORK/simulate_reasons.txt"
if [ $# -ge 2 ]; then cat "$2"; else grep " 0$" "$WORK/status.txt" | awk '{print $1}'; fi \
  | nl -w1 -s' ' > "$WORK/simulate_jobs/list.txt"
run_one() {
  i="$1"; f="$2"; job="$WORK/simulate_jobs/s$i.lean"
  cat "$f" "$WORK/simulate_tail.lean" > "$job"
  timeout -k 5 1500 lake env lean --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so "$job" \
    > /dev/null 2>&1
  rm -f "$job"
}
export -f run_one; export WORK
xargs -P 3 -L 1 bash -c 'run_one "$0" "$1"' < "$WORK/simulate_jobs/list.txt"
echo "machine-route declarations: $(grep -c . "$WORK/machine_decls.txt")"
echo "simulated: $(sort -u "$WORK/simulate_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
echo "by result:"; sort -u "$WORK/simulate_reasons.txt" | cut -d'|' -f2 | sort | uniq -c
grep -v "|OK|" "$WORK/simulate_reasons.txt" | sort -u | cut -c1-200
