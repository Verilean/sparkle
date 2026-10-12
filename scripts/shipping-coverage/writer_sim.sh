#!/usr/bin/env bash
# Limited simulation of hierarchical designs under the design writer
# (`toVerilogDesignChecked`, called by `#writeVerilogDesign` / `#writeDesign`):
# for a few declarations with `@[hardware_module]` children, the text the
# REAL command writes ("new"), the text of the previous writer
# `toVerilogDesign` ("old") and the SOURCE (the Lean declaration evaluated
# cycle by cycle, `Signal.val`) are compared on one stimulus: reset asserted,
# released, asserted again in the middle of the run, the enable toggling,
# every output port at every cycle.
#
#   scripts/shipping-coverage/writer_sim.sh
#   scripts/shipping-coverage/cgrun.sh -n writersim -m 3G -t 1500 -- \
#     scripts/shipping-coverage/writer_sim.sh
#
# One line per declaration:
#   WRITERSIM <decl>: new==source <T/F> old==source <T/F> new==old <T/F> cycles=<n> outputs=<k>
# then the first differing cycle of each failed comparison, and
#   WRITERSIM-TEXT <decl>: command==function <T/F> writeVerilogDesign==writeDesign <T/F/-> new-text==old-text <T/F> bytes new=<n> old=<n>
#
# Evidence on a few stimuli, not a proof. Exits 0 on a mismatch (it reports).
#
# Starts ONE Lean process (`lake env lean`, which reads built oleans only),
# then `iverilog` / `vvp` (Icarus, as `Tests/RoundTrip/IVerilogSim.lean`) one
# at a time. Requires a completed `lake build Tests.AllTests`; must NOT run
# next to a `lake build`. Files: .lake/build/gen/writer-sim/.
# Cycles: SPARKLE_WRITERSIM_NA (default 96), SPARKLE_WRITERSIM_NB (default 40).
set -u
cd "$(dirname "$0")/../.."
OUT=.lake/build/gen/writer-sim
rm -rf "$OUT"
mkdir -p "$OUT"

DYN=.lake/build/lib/libsparkle_Sparkle.so
LOAD=()
[ -f "$DYN" ] && LOAD=("--load-dynlib=$DYN")
timeout -k 5 "${SPARKLE_WRITERSIM_LEAN_TIMEOUT:-1200}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/writer_sim.lean > "$OUT/lean.log" 2>&1
echo "WRITERSIM lean: exit=$? log=$OUT/lean.log"
grep -E "WRITERSIM-GEN|error" "$OUT/lean.log" | cut -c1-300 | head -40

if [ ! -s "$OUT/rows.txt" ]; then
  echo "WRITERSIM: NOT RUN — the Lean step wrote no rows (see $OUT/lean.log)"
  exit 0
fi
if ! command -v iverilog > /dev/null 2>&1 || ! command -v vvp > /dev/null 2>&1; then
  echo "WRITERSIM: NOT RUN — iverilog / vvp not on PATH (the texts are in $OUT)"
  exit 0
fi

# trace of one text under the row's testbench (empty file where it fails)
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

# compare a trace ($1) with a reference ($2); a reference line `<ph> <i> -`
# is not compared. Prints `T|` or `F|<first difference>`.
compare() {
  paste -d'|' "$1" "$2" | awk -F'|' '
    { n2 = split($2, e, " ")
      if (n2 >= 3 && e[3] == "-") next
      n++
      if ($1 != $2 && !bad) { bad = 1; first = "got [" $1 "] want [" $2 "]" } }
    END { if (n == 0) print "F|nothing to compare"
          else if (bad) print "F|" first
          else print "T|" }'
}

while read -r tag decl ncyc nout nkids topsel; do
  if [ "$ncyc" = FAILED ]; then
    echo "WRITERSIM $decl: NOT RUN — the Lean step failed on it (see $OUT/lean.log)"
    continue
  fi
  simulate "$tag" new
  simulate "$tag" old
  ns=$(compare "$OUT/${tag}_new.trace" "$OUT/${tag}_expect.txt")
  os=$(compare "$OUT/${tag}_old.trace" "$OUT/${tag}_expect.txt")
  no=$(compare "$OUT/${tag}_new.trace" "$OUT/${tag}_old.trace")
  lines=$(grep -c . "$OUT/${tag}_new.trace")
  echo "WRITERSIM $decl: new==source ${ns%%|*} old==source ${os%%|*} new==old ${no%%|*} cycles=$ncyc outputs=$nout (lines simulated: $lines; modules besides the top: $nkids; top by $topsel)"
  [ "${ns%%|*}" = T ] || echo "  first difference new/source: ${ns#*|}"
  [ "${os%%|*}" = T ] || echo "  first difference old/source: ${os#*|}"
  [ "${no%%|*}" = T ] || echo "  first difference new/old: ${no#*|}"
  [ -s "$OUT/${tag}_new.trace" ] || { echo "  new: no trace; iverilog said:"; head -5 "$OUT/${tag}_new.iverilog.log" 2> /dev/null | cut -c1-200; }
  [ -s "$OUT/${tag}_old.trace" ] || { echo "  old: no trace; iverilog said:"; head -5 "$OUT/${tag}_old.iverilog.log" 2> /dev/null | cut -c1-200; }
  # the texts
  if [ -s "$OUT/${tag}_new.sv" ] && cmp -s "$OUT/${tag}_new.sv" "$OUT/${tag}_fn.sv"; then cf=T; else cf=F; fi
  if [ -e "$OUT/${tag}_wd.sv" ]; then
    if cmp -s "$OUT/${tag}_new.sv" "$OUT/${tag}_wd.sv"; then wd=T; else wd=F; fi
  else wd=-; fi
  if cmp -s "$OUT/${tag}_new.sv" "$OUT/${tag}_old.sv"; then tx=T; else tx=F; fi
  echo "WRITERSIM-TEXT $decl: command==function $cf writeVerilogDesign==writeDesign $wd new-text==old-text $tx bytes new=$(wc -c < "$OUT/${tag}_new.sv" 2> /dev/null || echo 0) old=$(wc -c < "$OUT/${tag}_old.sv" 2> /dev/null || echo 0)"
done < "$OUT/rows.txt"
exit 0
