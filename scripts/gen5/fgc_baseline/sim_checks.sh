#!/usr/bin/env bash
# S0: existing simulation / vector checks, recorded as pass/fail per check.
#
#   scripts/gen5/fgc_baseline/sim_checks.sh OUT [EXES.txt]
#
# Checks: (1) `lake build Tests.AllTests` (elaboration-time #guard/#eval checks
# and every synthesis command of the AllTests closure), (2) `lake exe test`
# (the lakefile test_driver), (3) each lean_exe named in EXES.txt (default: the
# lakefile exes whose name ends in `-test`, `sim-runner-test`, `-cosim`,
# `iverilog-roundtrip-test`, minus names containing `jit`, `linux`, `warp`,
# `oracle`, `repro`, which run for minutes-hours; list them explicitly to
# include them), (4) scripts/verify_parameterized_csim.sh (symbolic-parameter
# C sim vs. fixture).  Raw logs -> OUT/sim/<name>.log ; one line per check ->
# OUT/sim_results.tsv (name, exit, seconds).  Heavy: run via kjob run, one
# group of exes per job (EXES.txt chunks).  Resumable (REDO=1 reruns).
set -u
cd "$(dirname "$0")/../../.."
OUT="$1"; mkdir -p "$OUT/sim"
TMO="${SIM_TMO:-900}"
if [ $# -ge 2 ]; then cp "$2" "$OUT/sim_exes.txt"
else grep -oE '^lean_exe «[^»]+»' lakefile.lean | sed 's/lean_exe «//;s/»//' \
  | grep -E -- '(-test|-cosim|-sim-runner|test)$' | grep -vE 'jit|linux|warp|oracle|repro' > "$OUT/sim_exes.txt"; fi
run() {  # name, command...
  n="$1"; shift
  [ -f "$OUT/sim/$n.done" ] && [ "${REDO:-0}" != 1 ] && return
  t0=$(date +%s)
  timeout -k 5 "$TMO" "$@" > "$OUT/sim/$n.log" 2>&1; rc=$?
  t1=$(date +%s)
  echo -e "$n\t$rc\t$((t1 - t0))" > "$OUT/sim/$n.done"
}
if [ "${SKIP_BUILD:-0}" != 1 ]; then run build-AllTests lake build Tests.AllTests; fi
while read -r e; do [ -n "$e" ] && run "exe-$e" lake exe "$e"; done < "$OUT/sim_exes.txt"
run verify-parameterized-csim bash scripts/verify_parameterized_csim.sh
cat "$OUT"/sim/*.done > "$OUT/sim_results.tsv"
echo "sim checks: $(wc -l < "$OUT/sim_results.tsv") run, $(awk -F'\t' '$2==0' "$OUT/sim_results.tsv" | wc -l) exit 0"
