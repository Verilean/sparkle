#!/usr/bin/env bash
# For every machine-route declaration of a measurement, generate its machine
# endpoint — the kernel-checked theorem `f.machine_sound` of
# Tools/ShippingMachineCommand.lean — and count the ones the kernel accepts.
#
#   scripts/shipping-coverage/endpoints.sh WORKDIR [FILES.txt]
#
# WORKDIR is the directory of a completed `run.sh` pass 1 (it has
# `status.txt` and `machine_decls.txt`).  Each corpus file is elaborated once
# more with the command's import in front and the generator behind; a
# declaration several files see is generated in each (one success counts).
# FILES.txt limits the
# run to the files it lists (default: every file pass 1 ran successfully).
#
# ENDPOINT_JOBS sets how many files run at once (default 3; one elaboration
# of a large file can take 3 GB, so a small machine wants fewer).
#
# Requires a completed `lake build Tests.AllTests` and must NOT run next to a
# `lake build`.  A kernel check has no time limit of its own; the per-file
# limit below is what stops a check that does not end, and such a file is
# listed at the end.
set -u
cd "$(dirname "$0")/../.."
WORK="$1"
HERE="scripts/shipping-coverage"
mkdir -p "$WORK/endpoint_jobs"
sed "s#@WORK@#$WORK#g" "$HERE/endpoint_tail.lean.in" > "$WORK/endpoint_tail.lean"
: > "$WORK/endpoint_reasons.txt"
: > "$WORK/endpoint_status.txt"
: > "$WORK/linked_reasons.txt"
if [ $# -ge 2 ]; then cat "$2"; else grep " 0$" "$WORK/status.txt" | awk '{print $1}'; fi \
  | nl -w1 -s' ' > "$WORK/endpoint_jobs/list.txt"
run_one() {
  i="$1"; f="$2"; job="$WORK/endpoint_jobs/e$i.lean"
  { echo "import Tools.ShippingMachineLinkedCommand"; cat "$f" "$WORK/endpoint_tail.lean"; } > "$job"
  timeout -k 5 900 lake env lean --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so "$job" \
    > /dev/null 2>&1
  echo "$f $?" >> "$WORK/endpoint_status.txt"
  rm -f "$job"
}
export -f run_one; export WORK
xargs -P "${ENDPOINT_JOBS:-3}" -L 1 bash -c 'run_one "$0" "$1"' < "$WORK/endpoint_jobs/list.txt"
python3 "$HERE/report.py" endpoints "$WORK"
# the linked composition (one success per declaration counts)
echo "combinational children with machine_child: $(grep '|CHILD|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
echo "declarations with calls and machine_linked: $(grep '|LINKED|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l) of $(grep '|LINKED|' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
grep '|LINKED|FAIL' "$WORK/linked_reasons.txt" | sort -u | cut -c1-250 | head -20
