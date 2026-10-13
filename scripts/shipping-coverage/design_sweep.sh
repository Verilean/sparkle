#!/usr/bin/env bash
# The design-level generators on a CHOSEN list of files, one file at a time.
# WRITTEN, NOT RUN (round par/b-36).  Plan: docs/parallel/B-corpus-plan.md.
#
#   scripts/shipping-coverage/design_sweep.sh WORKDIR FILES.txt
#
# FILES.txt is REQUIRED (one path per line, relative to the repository root;
# blank lines and lines starting with # are skipped).  There is no default
# list: this script never enumerates the corpus.
#
# For each file, in the order given, ONE job:
#   import Tools.ShippingCorpusSweep  +  the file  +  design_tail.lean.in
# run as ONE cgroup-protected job (cgrun.sh: MemoryMax, swap 0, timeout, one
# job at a time).  Serial by construction: the next job starts when the
# previous one has ended.
#
# Resumable.  WORKDIR/done/<key>.status is written when a job has ended; a
# file with a status is skipped (REDO=1 runs it again and replaces its rows).
# Results are per file (WORKDIR/rows/<key>.txt), never truncated by another
# file's run.
#
# A file whose job did not reach its FILE-DONE row (timeout, OOM, crash) is
# UNMEASURED: its missing candidates are not failures.
#
# Environment:
#   DS_MEM   MemoryMax of a job            (default 3G)
#   DS_TMO   time limit of a job, seconds  (default 1500)
#   DS_MODE  candidates: marked | all      (default marked)
#   DS_WAIT  seconds to wait for another protected job to end before giving
#            up on a file (default 3600); such a file gets NO status
#   REDO=1   run files that already have a status
#
# Requires a completed `lake build Tools.ShippingCorpusSweep` and the built
# oleans of the imports of each file; must NOT run next to a `lake build`
# (cgrun refuses while another protected job is alive).
set -u
cd "$(dirname "$0")/../.."
if [ $# -lt 2 ] || [ ! -f "$2" ]; then
  echo "usage: design_sweep.sh WORKDIR FILES.txt   (FILES.txt is required: a chosen list, never the corpus)" >&2
  exit 2
fi
WORK="$1"; LIST="$2"
HERE="scripts/shipping-coverage"
MEM="${DS_MEM:-3G}"; TMO="${DS_TMO:-1500}"; MODE="${DS_MODE:-marked}"; WAIT="${DS_WAIT:-3600}"
case "$MODE" in marked|all) ;; *) echo "DS_MODE must be marked or all" >&2; exit 2;; esac
mkdir -p "$WORK/jobs" "$WORK/rows" "$WORK/done" "$WORK/logs"
WORKABS="$(cd "$WORK" && pwd)"
grep -v '^[[:space:]]*#' "$LIST" | grep -v '^[[:space:]]*$' > "$WORKABS/files_given.txt"
TOTAL=$(wc -l < "$WORKABS/files_given.txt")
echo "design_sweep: $TOTAL files given; MemoryMax $MEM, swap 0, $TMO s per file, mode $MODE"

# (the list is read on descriptor 3: the jobs must not consume it)
while read -r f <&3; do
  key="$(echo "$f" | tr '/' '_')"
  st="$WORKABS/done/$key.status"
  if [ -f "$st" ] && [ "${REDO:-0}" != 1 ]; then
    echo "skip (has a status): $f"
    continue
  fi
  if [ ! -f "$f" ]; then
    echo "file=$f result=missing exit=- seconds=0 peak=-" > "$st"
    echo "missing: $f"
    continue
  fi
  rows="$WORKABS/rows/$key.txt"; tops="$WORKABS/jobs/$key.tops"; job="$WORKABS/jobs/$key.lean"
  : > "$rows"
  # the identifiers after the synthesis commands of this file (marks only)
  grep -oE "^#(synthesizeVerilog|writeDesign|writeVerilogDesign|synthesizeVerilogDesign|synthesize)[[:space:]]+[A-Za-z_][A-Za-z0-9_.']*" "$f" \
    | awk '{print $2}' | sort -u > "$tops"
  {
    echo "import Tools.ShippingCorpusSweep"
    cat "$f"
    sed -e "s#@ROWS@#$rows#g" -e "s#@TOPS@#$tops#g" -e "s#@LABEL@#$f#g" -e "s#@MODE@#$MODE#g" \
      "$HERE/design_tail.lean.in"
  } > "$job"
  name="ds-$(echo "$key" | tr -c 'A-Za-z0-9\n' '-' | cut -c1-40)"
  t0=$(date +%s)
  waited=0
  while :; do
    "$HERE/cgrun.sh" -n "$name" -m "$MEM" -s 0 -t "$TMO" -j 2 -- \
      lake env lean --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so "$job" \
      > "$WORKABS/logs/$key.cgrun.txt" 2>&1 < /dev/null
    rc=$?
    # 75: another protected job is alive — wait, do not skip
    if [ "$rc" = 75 ] && [ "$waited" -lt "$WAIT" ]; then
      sleep 30; waited=$((waited + 30)); continue
    fi
    break
  done
  t1=$(date +%s)
  if [ "$rc" = 75 ]; then
    echo "not started (another protected job was alive for $WAIT s): $f — no status written"
    continue
  fi
  rec="$(grep -m1 '^== ' "$WORKABS/logs/$key.cgrun.txt" | cut -c4-)"
  if [ -n "$rec" ] && [ -f "$rec/log.txt" ]; then cp "$rec/log.txt" "$WORKABS/logs/$key.lean.txt"; fi
  peak="$(grep -m1 '^memory_peak_file=' "$WORKABS/logs/$key.cgrun.txt" | cut -d= -f2)"
  if grep -q '|FILE-DONE|' "$rows"; then res=measured
  elif [ "$rc" = 124 ]; then res=unmeasured-timeout
  elif [ "$rc" = 137 ]; then res=unmeasured-oom
  elif [ "$rc" = 76 ] || [ "$rc" = 77 ] || [ "$rc" = 78 ]; then res=unmeasured-not-protected
  else res="unmeasured-exit-$rc"
  fi
  echo "file=$f result=$res exit=$rc seconds=$((t1 - t0)) peak=${peak:--}" > "$st"
  echo "$res ($((t1 - t0)) s, peak ${peak:--}): $f"
  rm -f "$job"
done 3< "$WORKABS/files_given.txt"

python3 "$HERE/design_report.py" "$WORKABS"
