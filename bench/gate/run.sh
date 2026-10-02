#!/usr/bin/env bash
# ============================================================================
# Simulator instruction-count gate.
#
#   bench/gate/run.sh            check the current generator against the golden
#   bench/gate/run.sh --update   re-record the golden (after an intended change)
#
# What it does (details and rationale: bench/gate/README.md):
#   1. generates the CSim JIT C for the LiteX PicoRV32 SoC from the current
#      tree ("head");
#   2. co-simulates head against Verilator on the same RTL and the same
#      firmware: every UART byte must leave on the same cycle;
#   3. counts executed instructions per simulated cycle for head and for the
#      committed golden C, both built here with the same compiler;
#   4. fails if head is more than TOL % slower than the golden -- or more
#      than TOL % faster, so that an improvement is recorded with --update.
#
# Environment: WORK (scratch dir), TOL (percent, default 3), N1/N2 (cycle
# counts of the two counted runs), TRACE (co-simulated cycles), PICORV32
# (path to picorv32.v; fetched at a pinned commit otherwise), CC, CXX,
# NO_VERILATOR=1 (skip step 2 and the Verilator figure -- not for CI),
# BENCH_CYCLES / BENCH_JSON (wall-clock figures, informational), HEAD_C (a C
# file to gate instead of generating one -- for experiments on the emitted code).
# ============================================================================
set -euo pipefail
cd "$(dirname "$0")/../.."

MODE=check
for a in "$@"; do
  case "$a" in
    --update) MODE=update ;;
    *) echo "usage: $0 [--update]" >&2; exit 2 ;;
  esac
done

GATE=bench/gate
GOLDEN=$GATE/golden/litex_jit.c
FW=$PWD/$GATE/fw/litex_bench.hex
WORK=${WORK:-$(mktemp -d)}
TOL=${TOL:-3}
N1=${N1:-200000}
N2=${N2:-600000}
TRACE=${TRACE:-1000000}
CC=${CC:-cc}
CXX=${CXX:-g++}
PICO_REV=ef203c2b0a3fb793280f5114941416c425c5b461
mkdir -p "$WORK"
WORK=$(cd "$WORK" && pwd)

say() { echo "[gate] $*"; }
die() { echo "[gate] FAIL: $*" >&2; exit 1; }

# ---- instruction counter -------------------------------------------------
# cachegrind counts every executed instruction exactly; `perf stat` is the
# fallback where valgrind is not installed (a few 0.01 % of noise).
if command -v valgrind >/dev/null 2>&1; then COUNTER=valgrind
elif command -v perf >/dev/null 2>&1 && perf stat -e instructions:u true >/dev/null 2>&1; then COUNTER=perf
else die "need valgrind (preferred) or a working \`perf stat\` to count instructions"
fi
PIN=; command -v taskset >/dev/null 2>&1 && PIN="taskset -c 0"
count_instr() {  # <dir> <program> <args...>   (a real program: both tools exec it)
  local dir=$1; shift
  if [ "$COUNTER" = valgrind ]; then
    (cd "$dir" && valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=/dev/null "$@" 2>&1 >/dev/null) \
      | sed -n 's/.*I *refs: *\([0-9,]*\).*/\1/p' | tr -d ,
  else
    # pinned: on a hybrid CPU a migrating process is counted on two PMUs,
    # each scaled, and the sum is wrong
    (cd "$dir" && $PIN perf stat -x, -e instructions:u "$@" 2>&1 >/dev/null) \
      | awk -F, '$1 ~ /^[0-9]+$/ { s += $1 } END { print s }'
  fi
}
# instructions per cycle x 10, from two runs so that start-up cancels
per_cycle_x10() {  # <dir> <program> <args...>
  local a b
  a=$(count_instr "$@" "$N1"); b=$(count_instr "$@" "$N2")
  [ -n "$a" ] && [ -n "$b" ] || die "instruction counter produced no number for: $*"
  echo $(( (b - a) * 10 / (N2 - N1) ))
}
jit_cmd() { echo "$WORK $WORK/$1/harness $WORK/$1/jit.so $FW"; }   # no spaces in these paths
fmt() { echo "$(( $1 / 10 )).$(( $1 % 10 ))"; }

# ---- sources -------------------------------------------------------------
PICO=${PICORV32:-$WORK/picorv32.v}
if [ ! -s "$PICO" ]; then
  say "fetching picorv32.v @ ${PICO_REV:0:7}"
  curl -fsSL "https://raw.githubusercontent.com/YosysHQ/picorv32/$PICO_REV/picorv32.v" -o "$PICO" \
    || die "could not fetch picorv32.v (set PICORV32=<path>)"
fi
cat Tests/SVParser/fixtures/litex_sim_minimal.v "$PICO" > "$WORK/litex.v"

if [ -n "${HEAD_C:-}" ]; then
  say "HEAD_C set: using $HEAD_C instead of generating (experiments only)"
  cp "$HEAD_C" "$WORK/head.c"
else
  say "generating head JIT C"
  lake build Tools.SVParser Sparkle.Backend.CSim >"$WORK/lake.log" 2>&1 \
    || { tail -30 "$WORK/lake.log" >&2; die "lake build"; }
  lake env lean --run $GATE/gen.lean "$WORK/litex.v" "$WORK/head.c" >"$WORK/gen.log" 2>&1 \
    || { tail -30 "$WORK/gen.log" >&2; die "JIT generation"; }
fi

# ---- build one JIT model + its harness ----------------------------------
# Memory / port indices are read off the generated C: the vtable has no
# name lookup for them and they may differ between head and golden.
idx() {  # <c file> <function> <text on the case line>
  awk -v f="$2" -v pat="$3" '
    $0 ~ "^static .*" f "\\(" { on = 1 }
    on && index($0, pat) { match($0, /case [0-9]+/); print substr($0, RSTART + 5, RLENGTH - 5); exit }
    on && /^}/ { on = 0 }' "$1"
}
build_jit() {  # <name> <c file>
  local d=$WORK/$1 c=$2
  mkdir -p "$d"
  : > "$d/jit_map.h"
  def() {  # <macro> <function> <text on the case line>
    local v; v=$(idx "$c" "$2" "$3")
    [ -n "$v" ] || die "$1 not found in $c"
    echo "#define $1 $v" >> "$d/jit_map.h"
  }
  def ROM_IDX   sparkle_jit_set_mem    's->rom[addr]'
  def IN_READY  sparkle_jit_set_input  's->serial_source_ready '
  def OUT_DATA  sparkle_jit_get_output 's->serial_source_data;'
  def OUT_VALID sparkle_jit_get_output 's->serial_source_valid;'
  $CC -O2 -std=gnu11 -shared -fPIC -fvisibility=hidden -o "$d/jit.so" "$c" || die "compiling $c"
  $CXX -O2 -std=c++17 -I"$d" -o "$d/harness" $GATE/harness_jit.cpp -ldl || die "compiling the JIT harness"
}
jit() { local n=$1; shift; "$WORK/$n/harness" "$WORK/$n/jit.so" "$FW" "$@"; }

build_jit head "$WORK/head.c"

# ---- co-simulation against Verilator ------------------------------------
VL_X10=
if [ "${NO_VERILATOR:-0}" = 1 ]; then
  say "NO_VERILATOR=1: co-simulation SKIPPED"
else
  command -v verilator >/dev/null 2>&1 || die "verilator not found (NO_VERILATOR=1 skips the co-simulation)"
  say "building the Verilator model"
  mkdir -p "$WORK/vl"
  verilator --cc --exe --build -j 0 \
    -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL -Wno-CASEINCOMPLETE \
    -Wno-UNOPTFLAT -Wno-LATCH -Wno-MULTIDRIVEN -Wno-COMBDLY -Wno-PINMISSING \
    --top-module sim -CFLAGS "-O2" \
    "$WORK/litex.v" "$PWD/$GATE/harness_vl.cpp" --Mdir "$WORK/vl/obj" >"$WORK/vl/build.log" 2>&1 \
    || { tail -30 "$WORK/vl/build.log" >&2; die "verilator build"; }
  cp "$FW" "$WORK/vl/sim_rom.init"
  : > "$WORK/vl/sim_sram.init"; : > "$WORK/vl/sim_main_ram.init"; : > "$WORK/vl/sim_mem.init"
  vl() { (cd "$WORK/vl" && ./obj/Vsim "$@"); }

  say "co-simulating $TRACE cycles (UART bytes with their cycle numbers)"
  jit head "$TRACE" trace > "$WORK/head.trace"
  vl "$TRACE" trace > "$WORK/vl.trace" 2>/dev/null
  bytes=$(wc -l < "$WORK/vl.trace")
  [ "$bytes" -ge 100 ] || die "Verilator printed only $bytes UART bytes: the workload is not running"
  cmp -s "$WORK/head.trace" "$WORK/vl.trace" \
    || { diff "$WORK/head.trace" "$WORK/vl.trace" | head -5 >&2
         die "the JIT and Verilator disagree (traces in $WORK)"; }
  say "co-simulation OK: $bytes UART bytes, cycle-exact"
  VL_X10=$(per_cycle_x10 "$WORK/vl" ./obj/Vsim)
fi

# ---- instruction counts ---------------------------------------------------
say "counting instructions ($COUNTER, cycles $N1..$N2)"
HEAD_X10=$(per_cycle_x10 $(jit_cmd head))

if [ "$MODE" = update ]; then
  mkdir -p "$(dirname $GOLDEN)"
  cp "$WORK/head.c" $GOLDEN
  say "golden updated: $(fmt $HEAD_X10) instr/cycle${VL_X10:+ (Verilator $(fmt $VL_X10))}"
  say "commit $GOLDEN (it is under a *.c ignore rule: git add -f)"
  exit 0
fi

[ -s $GOLDEN ] || die "$GOLDEN is missing (run with --update)"
build_jit golden $GOLDEN
jit golden "$TRACE" trace > "$WORK/golden.trace"
jit head "$TRACE" trace > "$WORK/head.trace"
cmp -s "$WORK/head.trace" "$WORK/golden.trace" \
  || die "head and the golden model behave differently; if the change is intended, re-record with --update"
GOLD_X10=$(per_cycle_x10 $(jit_cmd golden))

delta=$(awk -v h="$HEAD_X10" -v g="$GOLD_X10" 'BEGIN { printf "%+.1f", (h - g) * 100 / g }')
verdict=$(awk -v h="$HEAD_X10" -v g="$GOLD_X10" -v t="$TOL" 'BEGIN {
  d = (h - g) * 100 / g; print (d > t) ? "slower" : (d < -t) ? "faster" : "ok" }')

{
  echo "| model | instructions / cycle |"
  echo "|---|---|"
  echo "| JIT, this tree | $(fmt $HEAD_X10) |"
  echo "| JIT, golden | $(fmt $GOLD_X10) |"
  if [ -n "$VL_X10" ]; then echo "| Verilator | $(fmt $VL_X10) |"; fi
  echo
  echo "this tree vs golden: ${delta} % (tolerance ±${TOL} %)"
  if [ -n "$VL_X10" ]; then echo "this tree vs Verilator: $(( HEAD_X10 * 100 / VL_X10 )) %"; fi
} | tee "$WORK/summary.md"

# ---- wall clock (informational: noisy on shared runners, never gated) -----
BENCH_CYCLES=${BENCH_CYCLES:-10000000}
cps() {  # cycles per second of "$@ <cycles>"
  local t0 t1
  t0=$(date +%s%N); "$@" "$BENCH_CYCLES" >/dev/null 2>&1; t1=$(date +%s%N)
  echo $(( BENCH_CYCLES * 1000000000 / (t1 - t0) ))
}
JIT_CPS=$(cps jit head)
VL_CPS=
[ -n "$VL_X10" ] && VL_CPS=$(cps vl)
{
  echo
  echo "wall clock, $BENCH_CYCLES cycles: JIT $JIT_CPS cyc/s${VL_CPS:+, Verilator $VL_CPS cyc/s}"
} | tee -a "$WORK/summary.md"
if [ -n "${BENCH_JSON:-}" ]; then
  {
    echo "["
    if [ -n "$VL_CPS" ]; then echo "  {\"name\": \"LiteX Verilator, firmware ($BENCH_CYCLES cycles)\", \"unit\": \"cycles/sec\", \"value\": $VL_CPS},"; fi
    echo "  {\"name\": \"LiteX JIT evalTick, firmware ($BENCH_CYCLES cycles)\", \"unit\": \"cycles/sec\", \"value\": $JIT_CPS}"
    echo "]"
  } > "$BENCH_JSON"
fi
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  { echo "### Simulator instruction-count gate"; cat "$WORK/summary.md"; } >> "$GITHUB_STEP_SUMMARY"
fi

case "$verdict" in
  slower) die "the generated simulator executes ${delta} % more instructions per cycle than the golden.
       If this cost is intended, record it:  bench/gate/run.sh --update" ;;
  faster) die "the generated simulator is ${delta} % against the golden -- an improvement that is not recorded.
       Lock it in:  bench/gate/run.sh --update   (and commit $GOLDEN)" ;;
esac
say "PASS"
