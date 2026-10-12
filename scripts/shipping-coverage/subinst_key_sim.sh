#!/usr/bin/env bash
# Limited simulation of the declarations of candidate G (gTopWR, gTopRW,
# hTopWR, gW, gR of Tests/Compiler/SubInstanceKeyTest.lean; a copy of
# nested_let_sim.sh with the names replaced): the text of the REAL command of
# the tree and of the entry with the front end off, against the SOURCE (the
# Lean declaration evaluated cycle by cycle) on one stimulus. Uses no
# candidate declaration: run it on poc AND on fix/nested-let-cache-build.
# WRITTEN, NOT RUN. Predicted: gTopWR / hTopWR command==source F with numbers
# (no x); gTopRW no trace or F; gW, gR T (docs/parallel/B-cache-keys.md).
#
#   scripts/shipping-coverage/cgrun.sh -n subinstkeysim -m 3G -t 900 -- \
#     scripts/shipping-coverage/subinst_key_sim.sh
#
# One line per declaration:
#   SUBINSTKEYSIM <decl>: command==source <T/F/-> nofe==source <T/F/-> command==nofe <T/F/-> x-cycles command=<n> nofe=<n> cycles=<n>
# `-`: a trace is missing. X: an undriven or self-assigned wire simulates as
# x and is printed as the text `x`; the comparison is textual, so an x cycle
# DIFFERS from the source (F) and is counted in `x-cycles`.
#
# Evidence on one stimulus, not a proof. Exits 0 always (it reports).
# Requires a completed `lake build Tests.Compiler.SubInstanceKeyTest`; must
# NOT run next to a `lake build`. Files: .lake/build/gen/subinst-key-sim/.
set -u
cd "$(dirname "$0")/../.."
OUT=.lake/build/gen/subinst-key-sim
rm -rf "$OUT"
mkdir -p "$OUT"

DYN=.lake/build/lib/libsparkle_Sparkle.so
LOAD=()
[ -f "$DYN" ] && LOAD=("--load-dynlib=$DYN")
timeout -k 5 "${SPARKLE_SUBINSTKEYSIM_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/subinst_key_sim.lean > "$OUT/lean.log" 2>&1
echo "SUBINSTKEYSIM lean: exit=$? log=$OUT/lean.log"
grep -E "SUBINSTKEYSIM-GEN|error" "$OUT/lean.log" | cut -c1-400 | head -40

if [ ! -s "$OUT/rows.txt" ]; then
  echo "SUBINSTKEYSIM: NOT RUN — the Lean step wrote no rows (see $OUT/lean.log)"
  exit 0
fi
if ! command -v iverilog > /dev/null 2>&1 || ! command -v vvp > /dev/null 2>&1; then
  echo "SUBINSTKEYSIM: NOT RUN — iverilog / vvp not on PATH (the texts are in $OUT)"
  exit 0
fi

simulate() { # tag variant
  local sv="$OUT/$1_$2.sv" tr="$OUT/$1_$2.trace"
  : > "$tr"
  [ -s "$sv" ] || return 0
  if timeout -k 5 120 iverilog -g2012 -s wsim_tb -o "$OUT/$1_$2.vvp" "$OUT/$1_tb.sv" "$sv" \
      > "$OUT/$1_$2.iverilog.log" 2>&1; then
    timeout -k 5 120 vvp -n "$OUT/$1_$2.vvp" 2> "$OUT/$1_$2.vvp.log" \
      | grep -E '^(R1|A|R2|B) [0-9]+ ' > "$tr"
  fi
  return 0
}

compare() {
  if [ ! -s "$1" ] || [ ! -s "$2" ]; then echo "-|no trace"; return 0; fi
  paste -d'|' "$1" "$2" | awk -F'|' '
    { n2 = split($2, e, " ")
      if (n2 >= 3 && e[3] == "-") next
      n++
      if ($1 != $2 && !bad) { bad = 1; first = "got [" $1 "] want [" $2 "]" } }
    END { if (n == 0) print "F|nothing to compare"
          else if (bad) print "F|" first
          else print "T|" }'
}

xcount() { # lines of a trace whose value contains x or z
  [ -s "$1" ] || { echo "-"; return 0; }
  awk '{ if ($3 ~ /[xXzZ]/) n++ } END { print n + 0 }' "$1"
}

while read -r tag decl ncyc; do
  if [ "$ncyc" = FAILED ]; then
    echo "SUBINSTKEYSIM $decl: NOT RUN — the Lean step failed on it (see $OUT/lean.log)"
    continue
  fi
  simulate "$tag" cmd
  simulate "$tag" nofe
  r_c=$(compare "$OUT/${tag}_cmd.trace" "$OUT/${tag}_expect.txt")
  r_n=$(compare "$OUT/${tag}_nofe.trace" "$OUT/${tag}_expect.txt")
  r_cn=$(compare "$OUT/${tag}_cmd.trace" "$OUT/${tag}_nofe.trace")
  echo "SUBINSTKEYSIM $decl: command==source ${r_c%%|*} nofe==source ${r_n%%|*} command==nofe ${r_cn%%|*} x-cycles command=$(xcount "$OUT/${tag}_cmd.trace") nofe=$(xcount "$OUT/${tag}_nofe.trace") cycles=$ncyc"
  [ "${r_c%%|*}" = T ] || echo "  command/source: ${r_c#*|}"
  [ "${r_n%%|*}" = T ] || echo "  nofe/source: ${r_n#*|}"
  for v in cmd nofe; do
    if [ ! -s "$OUT/${tag}_$v.trace" ]; then
      echo "  $v: no trace; iverilog said:"
      head -5 "$OUT/${tag}_$v.iverilog.log" 2> /dev/null | cut -c1-200
    fi
  done
done < "$OUT/rows.txt"
exit 0
