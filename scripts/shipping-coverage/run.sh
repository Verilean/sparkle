#!/usr/bin/env bash
# Measure which front end the shipping compiler takes on the repository's
# synthesis corpus, and why declarations miss the certified gate.
#
#   scripts/shipping-coverage/run.sh [WORKDIR]
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

# Pass 1: every synthesis, with the front end it took.
rm -f /tmp/sparkle-profile.log
: > "$WORK/status.txt"
while read -r f; do
  SPARKLE_PROFILE=1 timeout 300 lake env lean "$f" > /dev/null 2>&1
  echo "$f $?" >> "$WORK/status.txt"
done < "$WORK/files.txt"
cp /tmp/sparkle-profile.log "$WORK/profile.log"
python3 "$HERE/report.py" routes "$WORK"

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
