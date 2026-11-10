#!/usr/bin/env bash
# U1 measurement driver (MEASUREMENT ONLY, never for main).  Wraps u1_run.py.
#
# Usage (inside a kjob Pod, repo root of the tree being measured, after
# `kjob lake build Tools.VedU1Entry Tools.VedU1Deep Tools.VedStrictAudit`):
#   scripts/ved/u1_full.sh smoke [OUT]          # the smoke rows below, both routes
#   scripts/ved/u1_full.sh full  [OUT]          # 327 rows x {u1,u1_deep} = 654 records
#   scripts/ved/u1_full.sh rows ROWS.txt [OUT]  # lines "ROW ROUTE" (route u1|u1_deep|u1_deep_ns|u1_hier)
#   scripts/ved/u1_full.sh merge OUT SHARD_OUT...
#   scripts/ved/u1_full.sh size smoke|full|ROWS.txt [OUT]   # circuit SIZE (size_run.py), not a U1 route:
#       one record per row (SV sha256, IR counts, yosys generic + gowin); ROWS.txt lines "ROW";
#       OUT defaults to <report dir>/size-run; env SIZE_YOSYS, SIZE_YOSYS_TMO, SIZE_TMO, SHARD=k/n, SIZE_BUILD=0
# OUT defaults to $KJOB_REPORT_PATH's directory + /u1-run (never the source tree).
# Environment: U1_LEAN (default "kjob lake env lean"), U1_TMO (1800 s), U1_GRACE,
#   U1_RLIMIT_AS_KB, U1_INV_COMMIT/U1_INV_BLOB (default: the U0 pin), REDO=1,
#   ROUTES="u1 u1_deep" (restrict routes; u1_hier is run only when named, e.g. ROUTES="u1_hier"), SHARD=k/n (take every n-th list line,
#   k=0..n-1; give each shard its own OUT and merge afterwards).
# Exit status: 0 COMPLETE, 3 INCOMPLETE (harness errors / missing records).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git rev-parse --show-toplevel)
mode=${1:?smoke|full|rows|merge}; shift
# smoke coverage (inventory rows of the pinned inventory; row = data line number):
#  56 counterCdo (one register, expected U1 accepted), 57 resetCounterCdo, 59 heldRegCdo
#   3 adder16 (register-free)         63 pairCounterCdo, 64 pairRecordCdo (multi-output)
#   4 registerFile2 (memory)          25 rv32iSoCSynth (#writeDesign args: unsupported-invocation)
#  12 clintSignal, 13 csrFileSignal, 17 hazardSignal (wide inputs: Missing-cases / runCircuitH candidates; unconfirmed)
SMOKE_ROWS="56 57 59 3 63 64 4 25 12 13 17"
SIZE_SMOKE_ROWS="274 56 7 164 10"
default_out() { echo "$(dirname "${KJOB_REPORT_PATH:-$PWD/report.md}")/u1-run"; }
if [ "$mode" = merge ]; then
  OUT=${1:?OUT}; shift
  exec python3 -I "$HERE/u1_run.py" --out "$OUT" merge "$@"
fi
if [ "$mode" = size ]; then
  what=${1:?smoke|full|ROWS.txt}; shift
  OUT=${1:-$(dirname "${KJOB_REPORT_PATH:-$PWD/report.md}")/size-run}
  LIST=$(mktemp); trap 'rm -f "$LIST" "$LIST.s"' EXIT
  case "$what" in
    smoke) for r in $SIZE_SMOKE_ROWS; do echo "$r"; done > "$LIST" ;;
    full)  python3 -I "$HERE/u1_gen.py" --repo "$REPO" ${U1_INV_COMMIT:+--commit "$U1_INV_COMMIT"} \
             ${U1_INV_BLOB:+--blob "$U1_INV_BLOB"} rows | cut -f1 > "$LIST" ;;
    *)     cp "$what" "$LIST" ;;
  esac
  if [ -n "${SHARD:-}" ]; then
    k=${SHARD%/*}; n=${SHARD#*/}
    awk -v k="$k" -v n="$n" '(NR-1) % n == k' "$LIST" > "$LIST.s" && mv "$LIST.s" "$LIST"
  fi
  echo "u1_full: mode=size records=$(wc -l < "$LIST") out=$OUT"
  if [ "${SIZE_BUILD:-1}" != 0 ]; then
    mods=$(python3 -I "$HERE/u1_imports.py" --repo "$REPO" --list "$LIST" --tools Sparkle.Compiler.Elab) || exit 2
    (cd "$REPO" && kjob lake build $mods) || { echo "u1_full: import build FAILED" >&2; exit 2; }
  fi
  cd "$REPO" && exec python3 -I "$HERE/size_run.py" --repo "$REPO" --out "$OUT" list "$LIST"
fi
LIST=$(mktemp)
trap 'rm -f "$LIST"' EXIT
case "$mode" in
  rows)  src=${1:?ROWS.txt}; shift; cp "$src" "$LIST" ;;
  smoke) for r in $SMOKE_ROWS; do for rt in ${ROUTES:-u1 u1_deep u1_deep_ns}; do echo "$r $rt"; done; done > "$LIST" ;;
  full)  python3 -I "$HERE/u1_gen.py" --repo "$REPO" ${U1_INV_COMMIT:+--commit "$U1_INV_COMMIT"} \
           ${U1_INV_BLOB:+--blob "$U1_INV_BLOB"} rows | cut -f1 | while read -r r; do
           for rt in ${ROUTES:-u1 u1_deep u1_deep_ns}; do echo "$r $rt"; done; done > "$LIST" ;;
  *) echo "unknown mode $mode" >&2; exit 2 ;;
esac
OUT=${1:-$(default_out)}
if [ -n "${SHARD:-}" ]; then
  k=${SHARD%/*}; n=${SHARD#*/}
  awk -v k="$k" -v n="$n" '(NR-1) % n == k' "$LIST" > "$LIST.s" && mv "$LIST.s" "$LIST"
fi
echo "u1_full: mode=$mode records=$(wc -l < "$LIST") out=$OUT"
# build the modules the cases import (row files' direct imports + U1 tools),
# unless U1_BUILD=0; a failed build stops the run (no record is produced)
if [ "${U1_BUILD:-1}" != 0 ]; then
  mods=$(python3 -I "$HERE/u1_imports.py" --repo "$REPO" --list "$LIST") || exit 2
  t0=$(date +%s)
  (cd "$REPO" && kjob lake build $mods) || { echo "u1_full: import build FAILED" >&2; exit 2; }
  echo "u1_full: import build ok wall=$(( $(date +%s) - t0 ))s modules=$(echo $mods | wc -w)"
fi
cd "$REPO" && exec python3 -I "$HERE/u1_run.py" --repo "$REPO" --out "$OUT" list "$LIST"
