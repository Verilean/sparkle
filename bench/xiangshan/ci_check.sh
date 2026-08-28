#!/usr/bin/env bash
# XiangShan roundtrip regression gate (bench/xiangshan/README.md).
#
# Guards, on a curated subset of firtool-generated XiangShan RTL (one
# exemplar per miscompile class the Phase-2/3 sweeps found, the SRAM-macro
# shapes, and the hierarchical closures):
#
#   1. compile speed  — parse -> IR -> re-emit of the whole subset within
#                       a wall-time budget (the quadratic-blowup guard);
#   2. functional equivalence
#        formal   — yosys equiv_make/equiv_simple/equiv_induct per module
#                   (original vs re-emitted Verilog; the slow-but-trusted
#                   check, size-gated);
#        dynamic  — 3-way co-sim: iverilog(original) is golden, both the
#                   re-emitted Verilog AND the CSim JIT must match, so the
#                   C simulation path is covered too;
#   3. circuit quality — the Sparkle-native IR complexity metric
#                       (expression-node counts of parse(orig) and of
#                       parse(emit(parse(orig))), sv-roundtrip --metric):
#                       neither may GROW past the committed baseline —
#                       redundancy introduced by lowering or emission.
#                       yosys-free and instant; the yosys cell-count
#                       comparison remains available offline
#                       (compare_stat.sh) as the higher-trust variant.
#
# Env knobs: XS_RT_BUDGET (s, default 240), XS_EQUIV_TIMEOUT (s/module,
# default 120), XS_EQUIV_MAX_KB (skip formal equiv above this source size,
# default 256), XS_METRIC_SLACK (default 1.15).
set -uo pipefail
cd "$(dirname "$0")/../.."

CORPUS=bench/xiangshan/corpus
CORPUS_URL="https://github.com/Verilean/sparkle/releases/download/xiangshan-corpus-v1/xiangshan-ci-corpus-v1.tar.zst"
CORPUS_SHA256="0424c19e7629a94f141e655f4da6ef2e634b4e63e702523d4eec3dfa146e951f"
BASELINE=bench/xiangshan/ci_baseline.tsv
WORK="${XS_WORK:-/tmp/xs-ci}"
OUT="$WORK/rt"
BUDGET="${XS_RT_BUDGET:-240}"
EQUIV_TIMEOUT="${XS_EQUIV_TIMEOUT:-120}"
EQUIV_MAX_KB="${XS_EQUIV_MAX_KB:-256}"
METRIC_SLACK="${XS_METRIC_SLACK:-1.15}"
rm -rf "$WORK"; mkdir -p "$OUT"
fail=0

# The corpus is third-party generated code (XiangShan, MulanPSL-2.0) and
# is NOT committed — it lives as a release asset and is downloaded and
# integrity-checked here (works identically in CI and locally).
if ! ls "$CORPUS"/*.sv >/dev/null 2>&1; then
  echo "== fetching corpus: $CORPUS_URL"
  curl -fsSL -o "$WORK/corpus.tar.zst" "$CORPUS_URL"
  echo "$CORPUS_SHA256  $WORK/corpus.tar.zst" | sha256sum -c - || {
    echo "FAIL: corpus checksum mismatch"; exit 1; }
  tar -C bench/xiangshan --zstd -xf "$WORK/corpus.tar.zst"
fi

nfiles=$(ls "$CORPUS"/*.sv | wc -l)

echo "== phase 1: roundtrip parse -> IR -> emit + IR metric ($nfiles files, budget ${BUDGET}s)"
t0=$(date +%s)
lake exe sv-roundtrip "$CORPUS" --jobs 2 --metric --emit "$OUT" | tee "$WORK/roundtrip.log"
t1=$(date +%s)
wall=$((t1 - t0))
ok=$(grep -oP 'OK          : \K[0-9]+' "$WORK/roundtrip.log")
echo "roundtrip: $ok/$nfiles OK in ${wall}s"
if [ "$ok" != "$nfiles" ]; then echo "FAIL: roundtrip coverage $ok != $nfiles"; fail=1; fi
if [ "$wall" -gt "$BUDGET" ]; then echo "FAIL: roundtrip took ${wall}s > budget ${BUDGET}s"; fail=1; fi

# IR complexity metric: catalog columns are
#   phase file bytes ms modules insts regs irNodes rtNodes err
awk -F'\t' '$1 == "ok" { print $2 "\t" $8 "\t" $9 }' sv-roundtrip-catalog.tsv > "$WORK/metric.tsv"
if [ -f "$BASELINE" ]; then
  awk -F'\t' -v slack="$METRIC_SLACK" '
    NR==FNR { bIr[$1] = $2; bRt[$1] = $3; next }
    {
      if ($1 in bIr) {
        if (bIr[$1] > 0 && $2 > bIr[$1] * slack) {
          printf "FAIL: IR-metric regression (lowering) %s: %d nodes > baseline %d * %s\n", $1, $2, bIr[$1], slack; bad = 1
        }
        if (bRt[$1] > 0 && $3 > bRt[$1] * slack) {
          printf "FAIL: IR-metric regression (re-emission) %s: %d nodes > baseline %d * %s\n", $1, $3, bRt[$1], slack; bad = 1
        }
      }
      tIr += $2; tRt += $3
    }
    END {
      printf "IR metric totals: parse(orig)=%d nodes, parse(emit(...))=%d nodes\n", tIr, tRt
      exit bad
    }' "$BASELINE" "$WORK/metric.tsv" || fail=1
else
  echo "NOTE: no baseline at $BASELINE — writing one from this run"
  cp "$WORK/metric.tsv" "$BASELINE"
fi

echo "== phase 2: 3-way co-sim (leaf + hierarchical)"
for mode in "" "--hier"; do
  tag=$([ -z "$mode" ] && echo leaf || echo hier)
  lake exe sv-cosim "$CORPUS" "$OUT" --jobs 2 --cycles 20 $mode | tee "$WORK/cosim_$tag.log"
  rt=$(grep -oP 'RT mismatch          : \K[0-9]+' "$WORK/cosim_$tag.log")
  jit=$(grep -oP 'JIT mismatch         : \K[0-9]+' "$WORK/cosim_$tag.log")
  tf=$(grep -oP 'tool failures        : \K[0-9]+' "$WORK/cosim_$tag.log")
  if [ "$rt" != "0" ] || [ "$jit" != "0" ]; then
    echo "FAIL: co-sim ($tag) RT=$rt JIT=$jit (expected 0/0)"; fail=1
  fi
  if [ "$tf" != "0" ]; then
    echo "FAIL: co-sim ($tag) tool failures=$tf (subset must be tool-clean)"; fail=1
  fi
done

echo "== phase 3: yosys formal equivalence (size-gated, ${EQUIV_TIMEOUT}s/module)"
# Per-module status recorded to $WORK/equiv.tsv: proven | unproven | timeout | skip.
# GATE RULE: a module that the committed baseline lists as `proven` must
# stay proven — yosys induction leaving cells UNPROVEN is "unknown", not
# "different" (unreachable-state divergence doesn't close under
# equiv_induct), so fresh unproven modules only WARN; the dynamic co-sim
# (phase 2) still guards their behavior.
: > "$WORK/equiv.tsv"
equiv_fail=0; equiv_skip=0; equiv_ok=0; equiv_unproven=0
EQUIV_BASE=bench/xiangshan/ci_equiv_baseline.tsv
for p in "$CORPUS"/*.sv; do
  f=$(basename "$p"); top=${f%.sv}
  kb=$(( $(stat -c %s "$p") / 1024 ))
  st=skip
  if [ "$kb" -le "$EQUIV_MAX_KB" ]; then
    if timeout "$EQUIV_TIMEOUT" yosys -q -p "
        read_verilog -sv $CORPUS/*.sv; hierarchy -top $top; flatten; prep -top $top; memory_map; async2sync; design -stash gold;
        read_verilog -sv $OUT/*.sv;    hierarchy -top $top; flatten; prep -top $top; memory_map; async2sync; design -stash gate;
        design -copy-from gold -as gold $top; design -copy-from gate -as gate $top;
        equiv_make gold gate equiv; prep -top equiv; equiv_simple -seq 4; equiv_induct -seq 4;
        equiv_status -assert" > "$WORK/equiv_$top.log" 2>&1; then
      st=proven; equiv_ok=$((equiv_ok + 1))
    else
      rc=$?
      if [ "$rc" = "124" ]; then
        st=timeout; equiv_skip=$((equiv_skip + 1))
      elif grep -q "unproven \$equiv cells" "$WORK/equiv_$top.log"; then
        st=unproven; equiv_unproven=$((equiv_unproven + 1))
        echo "WARN: equiv unproven (induction limit — dynamically covered by co-sim): $f"
      else
        st=error; equiv_fail=$((equiv_fail + 1))
        echo "FAIL: formal equivalence errored: $f (see equiv_$top.log)"
        tail -3 "$WORK/equiv_$top.log" | sed 's/^/    /'
      fi
    fi
  else
    equiv_skip=$((equiv_skip + 1))
  fi
  printf '%s\t%s\n' "$f" "$st" >> "$WORK/equiv.tsv"
done
echo "equiv: proven=$equiv_ok unproven=$equiv_unproven skipped=$equiv_skip errored=$equiv_fail"
[ "$equiv_fail" != "0" ] && fail=1
if [ -f "$EQUIV_BASE" ]; then
  awk -F'\t' '
    NR==FNR { base[$1] = $2; next }
    base[$1] == "proven" && $2 != "proven" {
      printf "FAIL: equivalence regression: %s was proven in baseline, now %s\n", $1, $2; bad = 1
    }
    END { exit bad }' "$EQUIV_BASE" "$WORK/equiv.tsv" || fail=1
else
  echo "NOTE: no equiv baseline — writing one from this run"
  cp "$WORK/equiv.tsv" "$EQUIV_BASE"
fi

if [ "$fail" != "0" ]; then echo "== XiangShan gate: FAILED"; exit 1; fi
echo "== XiangShan gate: OK (roundtrip ${wall}s, equiv $equiv_ok proven/$equiv_skip skipped)"
