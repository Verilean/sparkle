#!/usr/bin/env bash
# rt62: threshold method for the MachRecUnfold fuel limit (no counting instrumentation).
# For ONE candidate limit L: elaborate every corpus file with `lean` and collect the
# `MachRecUnfold.<def>: fuel exhausted (limit L ...)` compile errors, with file and declaration.
# Run it once per candidate limit (e.g. 1000, 10000, 100000); the smallest L with no exhausted
# file is a limit that is enough for the corpus.  (A file that still fails for another reason is
# listed in status.txt with a nonzero exit; only `fuel exhausted` lines are counted here.)
#
#   Per-limit procedure (a copy of the tree, never the shared checkout):
#     1. cp -r the worktree to a scratch dir outside the source tree (or use a fresh kjob run checkout)
#     2. sed -i 's/^def fuelLimit : Nat := .*/def fuelLimit : Nat := L/' Sparkle/Compiler/MachRecUnfold.lean
#     3. kjob lake build Sparkle        # rebuilds the compiler (+ everything depending on it) with L
#     4. kjob lake env bash scripts/shipping-coverage/rt_fuel_threshold.sh OUTDIR JOBS L [TIMEOUT_S] [SEL...]
#   `lake env` supplies LEAN_PATH; imports of corpus files that have no olean are NOT elaborated
#   and are listed in OUTDIR/unbuilt.txt (build those targets in step 3, or pass a narrower SEL).
#
#   Args: OUTDIR (outside the source tree)  JOBS (parallel files, default 3)
#         L (the limit the compiler was built with; recorded in the output, default: read from source)
#         TIMEOUT_S (per file, default 600)
#         SEL...  corpus selection as in run.sh: any of Tests IP Examples (default all three),
#                 or a path to a file listing one corpus file per line (relative to the repo root).
#   Output: OUTDIR/exhausted.txt   lines `EXHAUSTED <limit> <file> <decl> <def> <unit>`
#           OUTDIR/exhausted_files.txt  files with at least one exhaustion
#           OUTDIR/status.txt      `<file> <exit>` (124 = timed out)
#           OUTDIR/unbuilt.txt, OUTDIR/log/*.{out,err}, OUTDIR/summary.txt
set -u
OUT="${1:?OUTDIR}"; JOBS="${2:-3}"; LIM="${3:-}"; TMO="${4:-600}"
shift 4 2>/dev/null || shift $#
ROOT="$(pwd)"
[ -z "$LIM" ] && LIM="$(sed -n 's/^def fuelLimit : Nat := \([0-9]*\).*/\1/p' "$ROOT/Sparkle/Compiler/MachRecUnfold.lean")"
mkdir -p "$OUT"
case "$(cd "$OUT" && pwd)" in "$ROOT"/*) echo "OUTDIR is inside the source tree" >&2; exit 2;; esac
mkdir -p "$OUT/log"
: > "$OUT/exhausted.txt"; : > "$OUT/unbuilt.txt"; : > "$OUT/status.txt"; : > "$OUT/runlist.txt"; : > "$OUT/files.txt"
[ $# -eq 0 ] && set -- Tests IP Examples
DIRS=""
for s in "$@"; do
  if [ -f "$s" ]; then cat "$s" >> "$OUT/files.txt"; else DIRS="$DIRS $s"; fi
done
if [ -n "$DIRS" ]; then
  # shellcheck disable=SC2086
  grep -rlE "^#synthesizeVerilog|^#writeDesign|^#writeVerilogDesign|^#synthesizeVerilogDesign|^#synthesize |synthesizeCombinational|synthesizeHierarchical" \
    --include=*.lean $DIRS | sort >> "$OUT/files.txt"
fi
have() {
  p="$(echo "$1" | tr . /)"
  IFS=: read -ra D <<< "$LEAN_PATH"
  for d in "${D[@]}"; do [ -f "$d/$p.olean" ] && return 0; done
  return 1
}
while read -r f; do
  [ -z "$f" ] && continue
  miss=""
  for m in $(grep -E "^import " "$ROOT/$f" | sed 's/^import //'); do
    have "$m" || { miss="$m"; break; }
  done
  if [ -n "$miss" ]; then echo "$f $miss" >> "$OUT/unbuilt.txt"; else echo "$f" >> "$OUT/runlist.txt"; fi
done < "$OUT/files.txt"
one() {
  f="$1"; key="$(echo "$f" | tr '/' '_')"
  ( cd "$ROOT" && timeout "$TMO" lean "$f" > "$OUT/log/$key.out" 2> "$OUT/log/$key.err" )
  echo "$f $?" >> "$OUT/status.txt"
}
export -f one; export OUT ROOT TMO
xargs -P "$JOBS" -I{} bash -c 'one {}' < "$OUT/runlist.txt"
# The compiler error reads  <file>:<line>:<col>: error: ... MachRecUnfold.<def>: fuel exhausted (limit N <unit>)
# and the declaration is the one named in the compile-error context; record the position and the
# message text so the declaration can be looked up from file:line.
for f in "$OUT"/log/*.out "$OUT"/log/*.err; do
  [ -f "$f" ] || continue
  grep -h "fuel exhausted" "$f" | sed -E "s|^([^:]+:[0-9]+):[0-9]+:.*MachRecUnfold\.([A-Za-z?]+): fuel exhausted \(limit ([0-9]+) (.*)\).*|EXHAUSTED $LIM \1 \2 \3 \4|"
done | sort -u >> "$OUT/exhausted.txt"
cut -d' ' -f3 "$OUT/exhausted.txt" | cut -d: -f1 | sort -u > "$OUT/exhausted_files.txt"
{ echo "limit $LIM"
  echo "files: $(wc -l < "$OUT/files.txt") run: $(wc -l < "$OUT/runlist.txt") unbuilt: $(wc -l < "$OUT/unbuilt.txt")"
  echo "exhausted rows: $(wc -l < "$OUT/exhausted.txt") exhausted files: $(wc -l < "$OUT/exhausted_files.txt")"
  echo "nonzero exit: $(awk '$2!=0' "$OUT/status.txt" | wc -l) (timeouts: $(awk '$2==124' "$OUT/status.txt" | wc -l))"
} | tee "$OUT/summary.txt"
