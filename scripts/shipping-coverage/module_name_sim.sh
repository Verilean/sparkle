#!/usr/bin/env bash
# Limited simulation of the declarations of Finding H (nTop, nDirect, mTop,
# mmTop of Tests/Compiler/CacheCoherenceProbe.lean): the text of the REAL
# command of the tree against the SOURCE (the Lean declaration evaluated
# cycle by cycle) on one stimulus. Uses no declaration of the fix: it can be
# run on the tree before the renaming and on fix/module-name-injective.
#
#   scripts/shipping-coverage/cgrun.sh -n modnamesim -m 3G -t 900 -- \
#     scripts/shipping-coverage/module_name_sim.sh
#
# One line per declaration:
#   MODNAMESIM <decl>: command==source <T/F/-> x-cycles=<n> cycles=<n>
# `-`: no trace (the text did not compile, or the Lean step failed on the
# declaration; the reason follows). X: an undriven wire simulates as x and
# is printed as the text `x`; the comparison is textual, so an x cycle
# DIFFERS from the source (F) and is counted in `x-cycles`.
#
# Evidence on one stimulus, not a proof. Exits 0 always (it reports).
# Requires a completed `lake build Tests.Compiler.CacheCoherenceProbe`; must
# NOT run next to a `lake build`. Files: .lake/build/gen/module-name-sim/.
set -u
cd "$(dirname "$0")/../.."
OUT=.lake/build/gen/module-name-sim
rm -rf "$OUT"
mkdir -p "$OUT"

DYN=.lake/build/lib/libsparkle_Sparkle.so
LOAD=()
[ -f "$DYN" ] && LOAD=("--load-dynlib=$DYN")
timeout -k 5 "${SPARKLE_MODNAMESIM_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/module_name_sim.lean > "$OUT/lean.log" 2>&1
echo "MODNAMESIM lean: exit=$? log=$OUT/lean.log"
grep -E "MODNAMESIM-GEN|error" "$OUT/lean.log" | cut -c1-400 | head -40

if [ ! -s "$OUT/rows.txt" ]; then
  echo "MODNAMESIM: NOT RUN — the Lean step wrote no rows (see $OUT/lean.log)"
  exit 0
fi
if ! command -v iverilog > /dev/null 2>&1 || ! command -v vvp > /dev/null 2>&1; then
  echo "MODNAMESIM: NOT RUN — iverilog / vvp not on PATH (the texts are in $OUT)"
  exit 0
fi

simulate() { # tag
  local sv="$OUT/$1_cmd.sv" tr="$OUT/$1_cmd.trace"
  : > "$tr"
  [ -s "$sv" ] || return 0
  if timeout -k 5 120 iverilog -g2012 -s wsim_tb -o "$OUT/$1_cmd.vvp" "$OUT/$1_tb.sv" "$sv" \
      > "$OUT/$1_cmd.iverilog.log" 2>&1; then
    timeout -k 5 120 vvp -n "$OUT/$1_cmd.vvp" 2> "$OUT/$1_cmd.vvp.log" \
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
    echo "MODNAMESIM $decl: NOT RUN — the Lean step failed on it (see $OUT/lean.log)"
    continue
  fi
  simulate "$tag"
  r_c=$(compare "$OUT/${tag}_cmd.trace" "$OUT/${tag}_expect.txt")
  echo "MODNAMESIM $decl: command==source ${r_c%%|*} x-cycles=$(xcount "$OUT/${tag}_cmd.trace") cycles=$ncyc"
  [ "${r_c%%|*}" = T ] || echo "  command/source: ${r_c#*|}"
  echo "  modules: $(grep -E '^module ' "$OUT/${tag}_cmd.sv" 2> /dev/null | sed -E 's/^module ([^ (#]+).*/\1/' | tr '\n' ' ')"
  if [ ! -s "$OUT/${tag}_cmd.trace" ]; then
    echo "  no trace; iverilog said:"
    head -5 "$OUT/${tag}_cmd.iverilog.log" 2> /dev/null | cut -c1-200
  fi
done < "$OUT/rows.txt"
exit 0
