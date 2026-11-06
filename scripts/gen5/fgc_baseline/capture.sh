#!/usr/bin/env bash
# S0 capture: elaborate each inventory file once, keep raw stdout (generated
# Verilog + Lean messages), the profile log lines (route per declaration),
# exit code and wall time.  Raw output goes to OUT (use $KJOB_REPORT_PATH's
# directory), never into the source tree.
#
#   scripts/gen5/fgc_baseline/capture.sh OUT [FILES.txt]
#
# FILES.txt: one repo-relative path per line (default: files with >= 1 synthesis
# command in OUT/inventory.tsv, produced by extract_inventory.py).  Resumable:
# a file with OUT/status/<key>.txt is skipped (REDO=1 to rerun).
# Serial on purpose (the compiler's profile log path /tmp/sparkle-profile.log is
# global).  Requires `lake build Tests.AllTests` (and the IP libs for IP/ files)
# to have completed; do not run next to a `lake build`.
set -u
cd "$(dirname "$0")/../../.."
OUT="$1"; mkdir -p "$OUT/out" "$OUT/prof" "$OUT/status"
TMO="${CAP_TMO:-900}"
if [ $# -ge 2 ]; then cp "$2" "$OUT/files_run.txt"
else tail -n +2 "$OUT/inventory.tsv" | cut -f1 | sort -u > "$OUT/files_run.txt"; fi
# `lean` must be the toolchain's own binary: inside `kjob lake env` only `lake` is on PATH
# (first run: every file failed with "could not execute external process 'lean'").
if ! command -v lean >/dev/null 2>&1; then
  LB="$( (elan which lean 2>/dev/null) || true)"
  [ -z "$LB" ] && LB="$(dirname "$(readlink -f "$(command -v lake)")")/lean"
  [ -x "$LB" ] && export PATH="$(dirname "$LB"):$PATH"
fi
command -v lean >/dev/null 2>&1 || { echo "capture.sh: lean not found on PATH" >&2; exit 2; }
lean --version > /dev/null || { echo "capture.sh: lean does not run" >&2; exit 2; }
{ echo "sha=${FGC_SHA:-$(git rev-parse HEAD 2>/dev/null)}"; echo "lean=$(command -v lean)"; echo "toolchain=$(cat lean-toolchain)"; echo "date=$(date -u +%FT%TZ)"; } > "$OUT/env.txt"
while read -r f; do
  [ -z "$f" ] && continue
  key="$(echo "$f" | tr '/' '_')"
  [ -f "$OUT/status/$key.txt" ] && [ "${REDO:-0}" != 1 ] && continue
  rm -f /tmp/sparkle-profile.log
  t0=$(date +%s)
  SPARKLE_PROFILE=1 timeout -k 5 "$TMO" lake env lean --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so "$f" \
    > "$OUT/out/$key.txt" 2> "$OUT/out/$key.err"
  rc=$?
  t1=$(date +%s)
  cp /tmp/sparkle-profile.log "$OUT/prof/$key.log" 2>/dev/null || : > "$OUT/prof/$key.log"
  echo "$f $rc $((t1 - t0))" > "$OUT/status/$key.txt"
done < "$OUT/files_run.txt"
echo "capture done: $(cat "$OUT"/status/*.txt | wc -l) files"
