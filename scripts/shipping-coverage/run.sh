#!/usr/bin/env bash
# Measure which front end the shipping compiler takes on the repository's
# synthesis corpus, and why declarations miss the certified gate.
#
#   scripts/shipping-coverage/run.sh [WORKDIR]
#   PASSES=1 scripts/shipping-coverage/run.sh [WORKDIR]   # routes + outputs only
#
# Pass 1 also keeps every file's output under WORKDIR/out/ (the generated
# Verilog of each `#synthesizeVerilog` is in it).  Two runs of pass 1 on two
# compiler versions can be compared with `diff -r A/out B/out`: the dispatch
# arms are shared by the certified and the legacy front end, so this is the
# regression check that a new arm did not change what legacy-route designs
# compile to.
#
# Requires a completed `lake build Tests.AllTests` (the files are run with
# `lake env lean`, which only reads built oleans) and must NOT run next to a
# `lake build`. The compiler's profile log path is fixed by the compiler:
# /tmp/sparkle-profile.log (it is cleared here).
set -u
cd "$(dirname "$0")/../.."
WORK="${1:-$(mktemp -d)}"
mkdir -p "$WORK"
HERE="scripts/shipping-coverage"

grep -rlE "^#synthesizeVerilog|^#writeDesign|^#writeVerilogDesign|^#synthesizeVerilogDesign|^#synthesize |synthesizeCombinational|synthesizeHierarchical" \
  --include=*.lean Tests IP Examples | sort > "$WORK/files.txt"

# Pass 1: every synthesis, with the front end it took.  Three files in
# parallel: the profile log is appended one self-contained line at a time,
# and the report reads it line by line, so interleaving does not matter.
rm -f /tmp/sparkle-profile.log
: > "$WORK/status.txt"
mkdir -p "$WORK/out"
pass1_one() {
  f="$1"
  # stdout only: stderr carries the profile lines, whose timings vary.
  SPARKLE_PROFILE=1 timeout 300 lake env lean "$f" \
    > "$WORK/out/$(echo "$f" | tr '/' '_').txt" 2> /dev/null
  echo "$f $?" >> "$WORK/status.txt"
}
export -f pass1_one; export WORK
xargs -P 3 -L 1 bash -c 'pass1_one "$0"' < "$WORK/files.txt"
cp /tmp/sparkle-profile.log "$WORK/profile.log"
python3 "$HERE/report.py" routes "$WORK"
if [ "${PASSES:-3}" = "1" ]; then
  echo "work directory: $WORK"
  exit 0
fi

# Pass 2: why each legacy-only declaration misses the gate.
sed "s#@WORK@#$WORK#g" "$HERE/probe_tail.lean.in" > "$WORK/probe_tail.lean"
: > "$WORK/cov_reasons.txt"
grep " 0$" "$WORK/status.txt" | awk '{print $1}' | while read -r f; do
  cat "$f" "$WORK/probe_tail.lean" > "$WORK/tmp_cov.lean"
  timeout 300 lake env lean "$WORK/tmp_cov.lean" > /dev/null 2>&1
done
python3 "$HERE/report.py" reasons "$WORK"

# Pass 3: the same question AFTER the reductions the legacy translator performs
# on the fly (delta-beta of user definitions, projection of a constructor),
# and as blocker SETS: what must be certified together to unlock a declaration.
sed "s#@WORK@#$WORK#g" "$HERE/normalize_tail.lean.in" > "$WORK/normalize_tail.lean"
: > "$WORK/norm_reasons.txt"
grep " 0$" "$WORK/status.txt" | awk '{print $1}' | while read -r f; do
  cat "$f" "$WORK/normalize_tail.lean" > "$WORK/tmp_cov.lean"
  timeout 300 lake env lean "$WORK/tmp_cov.lean" > /dev/null 2>&1
done
echo "--- before normalisation ---"
python3 "$HERE/report.py" sets "$WORK" cov_reasons.txt
echo "--- after normalisation ---"
python3 "$HERE/report.py" sets "$WORK" norm_reasons.txt
echo "work directory: $WORK"
