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
  { echo "import Tools.ShippingGateChildCommand"; echo "import Tools.ShippingMachineSeqCommand"; echo "import Tools.ShippingMachineShipsHierCommand"; echo "import Tools.ShippingMachineShipsHierHCommand"; echo "import Tools.ShippingHierSVRunH"; echo "import Tools.ShippingMachineDepthCommand"; echo "import Tools.ShippingPremiseEval"; cat "$f" "$WORK/endpoint_tail.lean"; } > "$job"
  timeout -k 5 1500 lake env lean --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so "$job" \
    > /dev/null 2>&1
  echo "$f $?" >> "$WORK/endpoint_status.txt"
  rm -f "$job"
}
export -f run_one; export WORK
xargs -P "${ENDPOINT_JOBS:-3}" -L 1 bash -c 'run_one "$0" "$1"' < "$WORK/endpoint_jobs/list.txt"
python3 "$HERE/report.py" endpoints "$WORK"
# the shipping theorems of machines with instances: generated (GEN:OK), the
# premises holding on the real compile (PREM), the parent's emitted Verilog
# (SV:parent) — generation alone is never counted as applying
for tag in SHIPSHIER SHIPSHIERH SHIPSHIERN1; do
  all=$(grep "|$tag|" "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)
  gen=$(grep "|$tag|GEN:OK" "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)
  prem=$(grep "|$tag|GEN:OK|PREM|" "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)
  sv=$(grep "|$tag|GEN:OK|PREM|SV:parent" "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)
  echo "$tag: attempted $all, generated $gen, premises hold on the run $prem, parent's emitted Verilog $sv"
  grep "|$tag|" "$WORK/linked_reasons.txt" | grep -v "|PREM|SV:parent" | sort -u | cut -c1-250 | head -10
done
# files that did not finish: their declarations are UNMEASURED (not failed)
awk '$2 != 0 { r = ($2 == 124 ? "timeout" : ($2 == 137 ? "killed (OOM?)" : "exit " $2)); print "unmeasured file: " $1 " (" r ")" }' "$WORK/endpoint_status.txt"
# the linked composition (one success per declaration counts)
echo "combinational children with machine_child: $(grep '|CHILD|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
echo "gate-route children with gate_child: $(grep '|GATECHILD|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l) of $(grep '|GATECHILD|' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
grep '|GATECHILD|FAIL' "$WORK/linked_reasons.txt" | sort -u | cut -c1-250 | head -10
echo "declarations with machine_composed: $(grep '|COMPOSED|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l) of $(grep '|COMPOSED|' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
grep '|COMPOSED|FAIL' "$WORK/linked_reasons.txt" | sort -u | cut -c1-250 | head -10
echo "memory/sequential-call parents with machine_composedT: $(grep '|COMPOSEDT|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l) of $(grep '|COMPOSEDT|' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
grep '|COMPOSEDT|FAIL' "$WORK/linked_reasons.txt" | sort -u | cut -c1-250 | head -10
echo "declarations with calls and machine_linked: $(grep '|LINKED|OK' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l) of $(grep '|LINKED|' "$WORK/linked_reasons.txt" | cut -d'|' -f1 | sort -u | wc -l)"
grep '|LINKED|FAIL' "$WORK/linked_reasons.txt" | sort -u | cut -c1-250 | head -20
