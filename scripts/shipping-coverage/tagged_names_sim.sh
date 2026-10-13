#!/usr/bin/env bash
# Tagged module names (Sparkle.IR.ModuleName.ofDecl: `Sp$D$...`) through the
# tools this repository actually uses: iverilog, yosys, Verilator and the
# repository's own C backend (CSim.toCJIT, compiled with the flags of
# Sparkle.Core.JIT.compile). Reviewer's ruling 2026-10-14, item 6.
#
#   scripts/shipping-coverage/cgrun.sh -n tagged -m 3G -t 1800 -- \
#     scripts/shipping-coverage/tagged_names_sim.sh
#
# One line per (example, tool):
#   TAGGEDNAMES <example> <tool>: exit=<n> <facts>
#   TAGGEDNAMES <example> <tool>: UNAVAILABLE          (tool not on PATH)
#   TAGGEDNAMES <example> <tool>: NOT RUN — <reason>   (no input for it)
# and a final summary. A tool's non-zero exit is RECORDED, never fatal: the
# script exits 0 always. Nothing is installed or downloaded.
#
# Tools (<tool>):
#   iverilog      compile + simulate <tag>_cmd.sv (the REAL #writeVerilogDesign
#                 text) against the SOURCE trace; `command==source T/F`
#   yosys         read_verilog -sv; hierarchy -check -top; proc; opt;
#                 check -assert; stat — exit and the module set of the
#                 `=== name ===` headers against the design's module names
#   verilator     --lint-only -sv --top-module <top>
#   verilator-cc  --cc (no build) with -fno-inline: the generated header
#                 names (how `$` is mangled), and whether `V<top>.h` exists
#                 under the literal top name (what SimVerilator.of includes)
#   csim-cc       cc -shared -fPIC -O2 -std=gnu11 -fvisibility=hidden on
#                 <tag>_jit.c (the flags of JIT.compile)
#   csim-ids      struct and function identifiers DEFINED in <tag>_jit.c and
#                 the duplicates among them; instance references that the
#                 backend left without `self->`
#   csim-run      a C main over jit_vtable() on the same stimulus, against the
#                 SOURCE trace; `c==source T/F`
# Further rows: `simcmd-*` (the real `#sim` command on tagged declarations),
# `simdup` (two files, one `#sim` output path).
#
# Evidence on one stimulus, not a proof. Requires a completed
# `lake build Tests.Compiler.CacheCoherenceProbe`; must NOT run next to a
# `lake build`. Files: .lake/build/gen/tagged-names/. The `#sim` rows also
# write (and this script removes) `tnz*`, `module*`, `1bad*` under
# .lake/build/gen/sim/.
set -u
cd "$(dirname "$0")/../.."
OUT=.lake/build/gen/tagged-names
SIMDIR=.lake/build/gen/sim
rm -rf "$OUT"
mkdir -p "$OUT"
SUM="$OUT/summary.tsv"
: > "$SUM"

have() { command -v "$1" > /dev/null 2>&1; }

CC=""
for c in cc gcc; do
  if have "$c"; then CC="$c"; break; fi
done

say() { # example tool exit facts
  echo "TAGGEDNAMES $1 $2: exit=$3 $4"
  printf '%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" >> "$SUM"
}

unavailable() { # example tool
  echo "TAGGEDNAMES $1 $2: UNAVAILABLE"
  printf '%s\t%s\tUNAVAILABLE\t\n' "$1" "$2" >> "$SUM"
}

notrun() { # example tool reason
  echo "TAGGEDNAMES $1 $2: NOT RUN — $3"
  printf '%s\t%s\tNOTRUN\t%s\n' "$1" "$2" "$3" >> "$SUM"
}

first_line() { # pattern file
  grep -m1 -E "$1" "$2" 2> /dev/null | tr '\t' ' ' | cut -c1-200
}

echo "TAGGEDNAMES tools: iverilog=$(have iverilog && echo yes || echo NO) vvp=$(have vvp && echo yes || echo NO) yosys=$(have yosys && echo yes || echo NO) verilator=$(have verilator && echo yes || echo NO) cc=${CC:-NO}"
have yosys && echo "TAGGEDNAMES version yosys: $(yosys -V 2>&1 | head -1 | cut -c1-80)"
have verilator && echo "TAGGEDNAMES version verilator: $(verilator --version 2>&1 | head -1 | cut -c1-80)"
have iverilog && echo "TAGGEDNAMES version iverilog: $(iverilog -V 2>&1 | head -1 | cut -c1-80)"
[ -n "$CC" ] && echo "TAGGEDNAMES version cc: $("$CC" --version 2>&1 | head -1 | cut -c1-80)"

DYN=.lake/build/lib/libsparkle_Sparkle.so
LOAD=()
[ -f "$DYN" ] && LOAD=("--load-dynlib=$DYN")

# ---------------------------------------------------------------- Lean step
echo "TAGGEDNAMES lean: START scripts/shipping-coverage/tagged_names_sim.lean"
timeout -k 5 "${SPARKLE_TAGGEDNAMES_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/tagged_names_sim.lean > "$OUT/lean.log" 2>&1
echo "TAGGEDNAMES lean: exit=$? log=$OUT/lean.log"
grep -E "TAGGEDNAMES-GEN|error" "$OUT/lean.log" | cut -c1-600 | head -80

compare() { # trace expect
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

run_iverilog() { # tag
  local sv="$OUT/$1_cmd.sv" tr="$OUT/$1_cmd.trace" rc r
  if ! have iverilog || ! have vvp; then unavailable "$1" iverilog; return 0; fi
  if [ ! -s "$sv" ]; then notrun "$1" iverilog "no $sv (see $OUT/lean.log)"; return 0; fi
  : > "$tr"
  timeout -k 5 120 iverilog -g2012 -s wsim_tb -o "$OUT/$1_cmd.vvp" "$OUT/$1_tb.sv" "$sv" \
    > "$OUT/$1_cmd.iverilog.log" 2>&1
  rc=$?
  if [ "$rc" = 0 ]; then
    timeout -k 5 120 vvp -n "$OUT/$1_cmd.vvp" 2> "$OUT/$1_cmd.vvp.log" \
      | grep -E '^(R1|A|R2|B) [0-9]+ ' > "$tr"
  fi
  r=$(compare "$tr" "$OUT/$1_expect.txt")
  say "$1" iverilog "$rc" "command==source ${r%%|*} x-cycles=$(xcount "$tr") ${r#*|} $(first_line 'error' "$OUT/$1_cmd.iverilog.log")"
}

run_yosys() { # tag top
  local sv="$OUT/$1_cmd.sv" log="$OUT/$1.yosys.log" ys="$OUT/$1.ys" rc match
  if ! have yosys; then unavailable "$1" yosys; return 0; fi
  if [ ! -s "$sv" ]; then notrun "$1" yosys "no $sv"; return 0; fi
  printf 'read_verilog -sv %s\nhierarchy -check -top %s\nproc\nopt\ncheck -assert\nstat\n' \
    "$sv" "$2" > "$ys"
  timeout -k 5 300 yosys -s "$ys" > "$log" 2>&1
  rc=$?
  grep -E '^=== .* ===$' "$log" | sed -E 's/^=== (.*) ===$/\1/' \
    | grep -v '^design hierarchy$' | sort -u > "$OUT/$1.yosys.mods"
  sort -u "$OUT/$1_names.txt" > "$OUT/$1.names.sorted"
  if cmp -s "$OUT/$1.yosys.mods" "$OUT/$1.names.sorted"; then match=T; else match=F; fi
  say "$1" yosys "$rc" "modules==expected $match yosys=[$(tr '\n' ' ' < "$OUT/$1.yosys.mods")] expected=[$(tr '\n' ' ' < "$OUT/$1.names.sorted")] $(first_line '^ERROR|Warning' "$log")"
}

run_verilator() { # tag top
  local sv="$OUT/$1_cmd.sv" log="$OUT/$1.verilator.log" d="$OUT/$1_vl" rc lit hdrs
  if ! have verilator; then
    unavailable "$1" verilator
    unavailable "$1" verilator-cc
    return 0
  fi
  if [ ! -s "$sv" ]; then
    notrun "$1" verilator "no $sv"
    notrun "$1" verilator-cc "no $sv"
    return 0
  fi
  timeout -k 5 300 verilator --lint-only -sv --top-module "$2" "$sv" > "$log" 2>&1
  rc=$?
  say "$1" verilator "$rc" "warnings=$(grep -c '^%Warning' "$log") $(first_line '^%(Error|Warning)' "$log")"
  rm -rf "$d"
  timeout -k 5 300 verilator --cc -sv --top-module "$2" -fno-inline \
    -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL -Wno-CASEINCOMPLETE \
    --Mdir "$d" "$sv" > "$OUT/$1.verilator-cc.log" 2>&1
  rc=$?
  if [ -f "$d/V$2.h" ]; then lit=T; else lit=F; fi
  hdrs=$(ls "$d" 2> /dev/null | grep -E '\.h$' | tr '\n' ' ')
  say "$1" verilator-cc "$rc" "literal-top-header(V<top>.h) $lit modules=$(wc -l < "$OUT/$1_names.txt" | tr -d ' ') nheaders=$(ls "$d" 2> /dev/null | grep -c -E '\.h$') headers=[$hdrs] $(first_line '^%Error' "$OUT/$1.verilator-cc.log")"
}

# identifiers DEFINED in a C text of the backend
c_structs() { grep -oE 'struct [A-Za-z0-9_$]+ \{' "$1" | awk '{ print $2 }'; }
c_funcs() { grep -oE 'sparkle_[A-Za-z0-9_$]+\([^;{]*\) \{' "$1" | sed -E 's/\(.*//'; }

c_ids() { # example cfile
  local s f ds df unq
  s=$(c_structs "$2" | wc -l | tr -d ' ')
  f=$(c_funcs "$2" | wc -l | tr -d ' ')
  ds=$(c_structs "$2" | sort | uniq -d | tr '\n' ' ')
  df=$(c_funcs "$2" | sort | uniq -d | tr '\n' ' ')
  unq=$(grep -c -E '\(&_tmp_inst|^ +_tmp_inst[A-Za-z0-9_$]*\.' "$2")
  say "$1" csim-ids 0 "structs=$s dup-structs=[$ds] funcs=$f dup-funcs=[$df] unqualified-inst-lines=$unq structs-are=[$(c_structs "$2" | tr '\n' ' ')]"
}

c_compile() { # example cfile so log
  local rc
  timeout -k 5 300 "$CC" -shared -fPIC -O2 -std=gnu11 -fvisibility=hidden \
    -I "$(dirname "$2")" -o "$3" "$2" > "$4" 2>&1
  rc=$?
  say "$1" csim-cc "$rc" "errors=$(grep -c -E '(^|[: ])error:' "$4") $(first_line 'error:' "$4")"
}

run_csim() { # tag cstat
  local c="$OUT/$1_jit.c" h="$OUT/$1_harness.c" tr="$OUT/$1_c.trace" rc r
  if [ ! -s "$c" ]; then
    notrun "$1" csim-cc "no C text (Lean C step: $2; see $OUT/lean.log)"
    notrun "$1" csim-ids "no C text"
    notrun "$1" csim-run "no C text"
    return 0
  fi
  c_ids "$1" "$c"
  if [ -z "$CC" ]; then
    unavailable "$1" csim-cc
    unavailable "$1" csim-run
    return 0
  fi
  c_compile "$1" "$c" "$OUT/$1_jit.so" "$OUT/$1.cc.log"
  : > "$tr"
  timeout -k 5 300 "$CC" -O1 -std=gnu11 -o "$OUT/$1_harness" "$h" > "$OUT/$1.harness.log" 2>&1
  rc=$?
  if [ "$rc" = 0 ]; then
    timeout -k 5 120 "$OUT/$1_harness" 2> "$OUT/$1.harness.run.log" \
      | grep -E '^(R1|A|R2|B) [0-9]+ ' > "$tr"
  fi
  r=$(compare "$tr" "$OUT/$1_expect.txt")
  say "$1" csim-run "$rc" "c==source ${r%%|*} ${r#*|} $(first_line 'error:' "$OUT/$1.harness.log")"
}

if [ ! -s "$OUT/rows.txt" ]; then
  echo "TAGGEDNAMES rows: NOT RUN — the Lean step wrote no rows (see $OUT/lean.log)"
else
  while read -r tag ncyc top cstat; do
    if [ "$ncyc" = FAILED ]; then
      for t in iverilog yosys verilator verilator-cc csim-cc csim-ids csim-run; do
        notrun "$tag" "$t" "the Lean step failed on the declaration (see $OUT/lean.log)"
      done
      continue
    fi
    echo "TAGGEDNAMES $tag: START top=$top cycles=$ncyc modules=[$(tr '\n' ' ' < "$OUT/${tag}_names.txt")]"
    echo "TAGGEDNAMES $tag text-modules: [$(grep -E '^module ' "$OUT/${tag}_cmd.sv" 2> /dev/null | sed -E 's/^module ([^ (#;]+).*/\1/' | tr '\n' ' ')]"
    run_iverilog "$tag"
    run_yosys "$tag" "$top"
    run_verilator "$tag" "$top"
    run_csim "$tag" "$cstat"
  done < "$OUT/rows.txt"
fi

# ------------------------------------------------- the real `#sim` command
sim_clean() {
  rm -f "$SIMDIR"/tnz*_jit.c "$SIMDIR"/tnz*.sv "$SIMDIR"/module_jit.c "$SIMDIR"/module.sv \
    "$SIMDIR"/1bad_jit.c "$SIMDIR"/1bad.sv
}
sim_clean

echo "TAGGEDNAMES simcmd lean: START scripts/shipping-coverage/tagged_names_simcmd.lean"
timeout -k 5 "${SPARKLE_TAGGEDNAMES_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/tagged_names_simcmd.lean > "$OUT/simcmd.log" 2>&1
echo "TAGGEDNAMES simcmd lean: exit=$? (1 is expected when a case is refused) log=$OUT/simcmd.log"

simcmd_case() { # case ns
  local ex="simcmd-$1" r n src="$SIMDIR/$2_jit.c" c="$OUT/simcmd_$1_jit.c"
  r=$(awk -v s="TAGGEDNAMES-SIMCMD $1 START" -v e="TAGGEDNAMES-SIMCMD $1 END" '
        index($0, s) { on = 1; seen = 1; next }
        index($0, e) { on = 0 }
        on && /error/ { n++; if (!f) f = $0 }
        END { print (seen ? n + 0 : "-") "|" f }' "$OUT/simcmd.log")
  n=${r%%|*}
  if [ "$n" = "-" ]; then
    notrun "$ex" sim "the case did not start (see $OUT/simcmd.log)"
    return 0
  fi
  say "$ex" sim "$([ "$n" = 0 ] && echo 0 || echo 1)" "lean-errors=$n ns=$2 file=$([ -s "$src" ] && echo written || echo absent) $(echo "${r#*|}" | cut -c1-240)"
  if [ ! -s "$src" ]; then
    notrun "$ex" csim-cc "no $src"
    return 0
  fi
  cp "$src" "$c"
  c_ids "$ex" "$c"
  if [ -z "$CC" ]; then unavailable "$ex" csim-cc; return 0; fi
  c_compile "$ex" "$c" "$OUT/simcmd_$1_jit.so" "$OUT/simcmd_$1.cc.log"
}

simcmd_case privself tnzPrivKid
simcmd_case priv tnzPrivTop
simcmd_case uni1 tnz_
simcmd_case uni2 tnz_
simcmd_case kw module
simcmd_case dig 1bad

# ------------------------------- two files, one `#sim` output path
dup_state() { # -> "<hash>(<top struct>)"
  local f="$SIMDIR/tnzDup_jit.c"
  if [ ! -s "$f" ]; then echo "absent"; return 0; fi
  echo "$(sha256sum "$f" | cut -c1-12)($(c_structs "$f" | tail -1))"
}

echo "TAGGEDNAMES simdup lean: START tagged_names_simdup_a.lean then tagged_names_simdup_b.lean"
timeout -k 5 "${SPARKLE_TAGGEDNAMES_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/tagged_names_simdup_a.lean > "$OUT/simdup_a.log" 2>&1
rc_a=$?
st_a=$(dup_state)
timeout -k 5 "${SPARKLE_TAGGEDNAMES_LEAN_TIMEOUT:-600}" \
  lake env lean "${LOAD[@]}" scripts/shipping-coverage/tagged_names_simdup_b.lean > "$OUT/simdup_b.log" 2>&1
rc_b=$?
st_b=$(dup_state)
if [ "$st_a" != absent ] && [ "$st_b" != absent ] && [ "$st_a" != "$st_b" ]; then ow=T; else ow=F; fi
say simdup sim-filename "$rc_a/$rc_b" "path=$SIMDIR/tnzDup_jit.c after-A=$st_a after-B=$st_b overwritten-without-error=$ow lean-errors=$(grep -c 'error' "$OUT/simdup_a.log")/$(grep -c 'error' "$OUT/simdup_b.log")"
sim_clean

# ----------------------------------------------------------------- summary
echo "TAGGEDNAMES summary: rows=$(wc -l < "$SUM" | tr -d ' ') exit0=$(awk -F'\t' '$3 == "0"' "$SUM" | wc -l | tr -d ' ') nonzero=$(awk -F'\t' '$3 != "0" && $3 != "UNAVAILABLE" && $3 != "NOTRUN"' "$SUM" | wc -l | tr -d ' ') unavailable=$(awk -F'\t' '$3 == "UNAVAILABLE"' "$SUM" | wc -l | tr -d ' ') notrun=$(awk -F'\t' '$3 == "NOTRUN"' "$SUM" | wc -l | tr -d ' ')"
echo "TAGGEDNAMES summary nonzero: $(awk -F'\t' '$3 != "0" && $3 != "UNAVAILABLE" && $3 != "NOTRUN" { printf "%s/%s(%s) ", $1, $2, $3 }' "$SUM")"
echo "TAGGEDNAMES summary trace mismatches: $(awk -F'\t' '$4 ~ /(command|c)==source (F|-)/ { printf "%s/%s ", $1, $2 }' "$SUM")"
echo "TAGGEDNAMES summary module-set mismatches: $(awk -F'\t' '$4 ~ /modules==expected F/ { printf "%s ", $1 }' "$SUM")"
echo "TAGGEDNAMES summary C identifier duplicates: $(awk -F'\t' '$2 == "csim-ids" && ($4 !~ /dup-structs=\[\]/ || $4 !~ /dup-funcs=\[\]/) { printf "%s ", $1 }' "$SUM")"
echo "TAGGEDNAMES summary unqualified instance references: $(awk -F'\t' '$2 == "csim-ids" && $4 !~ /unqualified-inst-lines=0 / { printf "%s ", $1 }' "$SUM")"
echo "TAGGEDNAMES: files in $OUT (summary.tsv; per row *.log)"
exit 0
