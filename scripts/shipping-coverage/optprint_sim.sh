#!/usr/bin/env bash
# Limited simulation of the declarations of Tests/Compiler/OptPrintSourceTest.lean
# (register machines whose optimised module may be outside the print
# fragment: printOk false after the accepted optimizer candidate). The text
# of the REAL command of the tree, and the text the design writer WOULD print
# under the candidate guard `refineCheck m o && printOk o` (computed in the
# Lean step, the compiler is not changed), against the SOURCE (the Lean
# declaration evaluated cycle by cycle) on one stimulus.
#
# This is what separates "the shipped text is outside the proved fragment"
# (printOk false: UNPROVED) from "the shipped text differs from the source"
# (command==source F: a real difference, with its first cycle).
#
# HOW TO RUN (integrator; in the protected queue, after the test target):
#
#   scripts/shipping-coverage/cgrun.sh -n optprint-src -m 3G -t 1800 -- \
#     lake build Tests.Compiler.OptPrintSourceTest
#   scripts/shipping-coverage/cgrun.sh -n optprintsim -m 3G -t 900 -- \
#     scripts/shipping-coverage/optprint_sim.sh
#
# Requires a completed `lake build Tests.Compiler.OptPrintSourceTest`; must
# NOT run next to a `lake build`. Files: .lake/build/gen/optprint-sim/.
#
# One line per declaration:
#   OPTPRINTSIM <decl>: command==source <T/F/-> x-cycles=<n> cycles=<n> guarded==source <T/F/-> guard-changes-text=<T/F> printOk-shipped=<T/F>
# followed, when a comparison is not T, by the first differing cycle:
#   command/source: got [<phase> <cycle> <value>] want [<phase> <cycle> <value>]
# `-`: a trace is missing. X: an undriven wire simulates as x and is printed
# as the text `x`; the comparison is textual, so an x cycle DIFFERS from the
# source (F) and is counted in `x-cycles`.
#
# Evidence on one stimulus, not a proof. Exits 0 always (it reports).
set -u
cd "$(dirname "$0")/../.."
OUT=.lake/build/gen/optprint-sim
rm -rf "$OUT"
mkdir -p "$OUT"

DYN=.lake/build/lib/libsparkle_Sparkle.so
LOAD=()
[ -f "$DYN" ] && LOAD=("--load-dynlib=$DYN")
timeout -k 5 "${SPARKLE_OPTPRINTSIM_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/optprint_sim.lean > "$OUT/lean.log" 2>&1
echo "OPTPRINTSIM lean: exit=$? log=$OUT/lean.log"
grep -E "OPTPRINTSIM-GEN|error" "$OUT/lean.log" | cut -c1-400 | head -60

if [ ! -s "$OUT/rows.txt" ]; then
  echo "OPTPRINTSIM: NOT RUN — the Lean step wrote no rows (see $OUT/lean.log)"
  exit 0
fi
if ! command -v iverilog > /dev/null 2>&1 || ! command -v vvp > /dev/null 2>&1; then
  echo "OPTPRINTSIM: NOT RUN — iverilog / vvp not on PATH (the texts are in $OUT)"
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

total=0; cmd_t=0; cmd_f=0; cmd_none=0; changed_n=0; unproved_n=0
while read -r tag decl ncyc changed pk; do
  total=$((total + 1))
  if [ "$ncyc" = FAILED ]; then
    echo "OPTPRINTSIM $decl: NOT RUN — the Lean step failed on it (see $OUT/lean.log)"
    cmd_none=$((cmd_none + 1))
    continue
  fi
  simulate "$tag" cmd
  simulate "$tag" guard
  r_c=$(compare "$OUT/${tag}_cmd.trace" "$OUT/${tag}_expect.txt")
  r_g=$(compare "$OUT/${tag}_guard.trace" "$OUT/${tag}_expect.txt")
  echo "OPTPRINTSIM $decl: command==source ${r_c%%|*} x-cycles=$(xcount "$OUT/${tag}_cmd.trace") cycles=$ncyc guarded==source ${r_g%%|*} guard-changes-text=$changed printOk-shipped=$pk"
  [ "${r_c%%|*}" = T ] || echo "  command/source: ${r_c#*|}"
  [ "${r_g%%|*}" = T ] || echo "  guarded/source: ${r_g#*|}"
  case "${r_c%%|*}" in
    T) cmd_t=$((cmd_t + 1)) ;;
    F) cmd_f=$((cmd_f + 1)) ;;
    *) cmd_none=$((cmd_none + 1)) ;;
  esac
  [ "$changed" = T ] && changed_n=$((changed_n + 1))
  [ "$pk" = F ] && unproved_n=$((unproved_n + 1))
  for v in cmd guard; do
    if [ ! -s "$OUT/${tag}_$v.trace" ]; then
      echo "  $v: no trace; iverilog said:"
      head -5 "$OUT/${tag}_$v.iverilog.log" 2> /dev/null | cut -c1-200
    fi
  done
done < "$OUT/rows.txt"
echo "OPTPRINTSIM TOTAL: $total declarations; command==source T=$cmd_t F=$cmd_f not-compared=$cmd_none; shipped top with printOk false: $unproved_n; text changes under the guard: $changed_n (one stimulus; not a proof)"
exit 0
