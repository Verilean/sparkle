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
#   3. lean₄ round trip — ingested RTL is decompiled back to circuit-DSL
#                       source and PROVEN equivalent per cone
#                       (`#verify_dsl_roundtrip`, bv_decide), and the
#                       decompiler's printable count is reported;
#   4. circuit quality — the Sparkle-native IR complexity metric
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

echo "== phase 4: verilog → IR → lean₄ → IR proofs (#verify_dsl_roundtrip)"
# The committed proof file holds machine-generated circuit-DSL source for
# a register-count-stratified set of real XiangShan modules; every cone
# must close under bv_decide.  Also report the decompiler's printable
# count so a drop shows up in the log.
DSL_FILE=Tests/Verification/XiangShanDslRoundtrip.lean
if [ -f "$DSL_FILE" ]; then
  # `lake env lean` does NOT build missing dependencies — it needs the
  # oleans of the file's import closure on disk.  On the dev box those
  # are always present; in CI only the phase-1/2 exes were built, so
  # phase 4 failed with "object file ... does not exist" on every run
  # since it was added (masked at first behind a phase-1 failure).
  lake build Sparkle Tools.SVParser.DslEmit > "$WORK/dsl_build.log" 2>&1 || {
    echo "FAIL: could not build the dsl-roundtrip import closure"
    tail -5 "$WORK/dsl_build.log" | sed 's/^/    /'
    fail=1
  }
  if lake env lean "$DSL_FILE" > "$WORK/dsl_roundtrip.log" 2>&1; then
    proven=$(grep -c '✅' "$WORK/dsl_roundtrip.log")
    cones=$(grep -oE '— [0-9]+ cone' "$WORK/dsl_roundtrip.log" | grep -oE '[0-9]+' | paste -sd+ | bc)
    echo "dsl-roundtrip: $proven modules proven, ${cones:-0} cone obligations"
    if [ "$proven" -lt 1 ]; then echo "FAIL: no dsl-roundtrip proofs ran"; fail=1; fi
  else
    echo "FAIL: #verify_dsl_roundtrip proofs did not close"
    grep -m3 -E "error" "$WORK/dsl_roundtrip.log" | sed 's/^/    /'
    fail=1
  fi
  lake exe sv-to-dsl "$CORPUS" --jobs 2 --max-kb 128 > "$WORK/sv_to_dsl.log" 2>&1 || true
  printable=$(grep -oP 'printable as circuit-DSL : \K[0-9]+' "$WORK/sv_to_dsl.log")
  echo "dsl-printable on the CI corpus: ${printable:-0}"
fi

# == phase 5: the Signal↔IR link (#verify_elab) ======================
# Generates and kernel-checks, per demo circuit, that the elaborated
# IR's register/output trace under the PROVEN evalExpr equals the
# circuit's own Signal semantics.  The command aborts itself if any
# generated proof smuggles in sorryAx, so grepping PROVEN is sound.
ELAB_FILE=Tests/Verification/VerifyElabDemo.lean
if [ -f "$ELAB_FILE" ]; then
  echo "== phase 5: Signal ↔ IR (#verify_elab)"
  lake build Sparkle Tools.VerifyElab > "$WORK/velab_build.log" 2>&1 || {
    echo "FAIL: could not build the verify-elab import closure"
    tail -5 "$WORK/velab_build.log" | sed 's/^/    /'
    fail=1
  }
  if lake env lean "$ELAB_FILE" > "$WORK/verify_elab.log" 2>&1; then
    vproven=$(grep -c 'PROVEN' "$WORK/verify_elab.log")
    echo "verify-elab: $vproven circuits proven (axioms audited)"
    if [ "$vproven" -lt 7 ]; then
      echo "FAIL: verify-elab proved $vproven < 7 demo circuits"; fail=1
    fi
  else
    echo "FAIL: #verify_elab demo did not close"
    grep -m3 -E "error" "$WORK/verify_elab.log" | sed 's/^/    /'
    fail=1
  fi
  # the GENERAL-theorem route: same circuits reified into the deep
  # grammar, certified through Cdo.elab_general
  DEEP_FILE=Tests/Verification/DeepElabReifyDemo.lean
  if [ -f "$DEEP_FILE" ]; then
    lake build Tools.DeepElab > "$WORK/deep_build.log" 2>&1 || {
      echo "FAIL: could not build the deep-elab import closure"; fail=1; }
    if lake env lean "$DEEP_FILE" > "$WORK/deep_elab.log" 2>&1; then
      dproven=$(grep -c 'PROVEN' "$WORK/deep_elab.log")
      echo "deep-elab (general theorem): $dproven circuits proven"
      # 13 flat demos + 3 nested-circuit demos (outerNest, outerFb, lvl0)
      # + 2 value-parameter wrappers (accK15, accN200)
      # + 3 memory demos (memAcc, memTwo, comboAcc)
      if [ "$dproven" -lt 21 ]; then
        echo "FAIL: deep-elab proved $dproven < 21 demo circuits"; fail=1
      fi
    else
      echo "FAIL: #verify_elab_deep demo did not close"
      grep -m3 -E "error" "$WORK/deep_elab.log" | sed 's/^/    /'
      fail=1
    fi
  fi
  # the general theorem on REAL shipping IP (crc32Engine, …)
  REAL_FILE=Tests/Verification/DeepElabRealIP.lean
  if [ -f "$REAL_FILE" ]; then
    lake build IP.Net.CRC32 IP.Net.UART IP.Crypto.EcdsaSignSmall IP.Bus.DroneCANHW IP.Bus.SBUSHW IP.Bus.SPIHW >> "$WORK/deep_build.log" 2>&1 || {
      echo "FAIL: could not build the real-IP import closure"; fail=1; }
    if lake env lean "$REAL_FILE" > "$WORK/deep_real.log" 2>&1; then
      # one PROVEN line per output port: crc32Engine (1) + uartTxHW (2)
      # + regFile (2) + transferIdTrackerHW (3) + frameAccumulatorHW (4)
      # + spiMasterHW (5)
      rproven=$(grep -c 'PROVEN' "$WORK/deep_real.log")
      echo "deep-elab (real IP): $rproven ports proven"
      if [ "$rproven" -lt 17 ]; then
        echo "FAIL: deep-elab real-IP proved $rproven < 17 ports"; fail=1
      fi
    else
      echo "FAIL: #verify_elab_deep real-IP did not close"
      grep -m3 -E "error" "$WORK/deep_real.log" | sed 's/^/    /'
      fail=1
    fi
  fi
  # STATE CORRESPONDENCE + duplication-freedom: the trace theorems are
  # invariant under duplicated hardware (two copies of one register hold
  # the same value every cycle), so this is what catches the three
  # duplication bugs the chain could not see.  The file's negative
  # section pins non-vacuity, so a build failure here means either a
  # real duplication or a broken checker.
  CORR_FILE=Tests/Verification/StateCorrespondenceTest.lean
  if [ -f "$CORR_FILE" ]; then
    if lake build Tests.Verification.StateCorrespondenceTest \
        > "$WORK/state_corr.log" 2>&1; then
      echo "state correspondence: 6 shipping circuits, duplication-free"
    else
      echo "FAIL: state correspondence / duplication-freedom regressed"
      grep -m5 -E "error" "$WORK/state_corr.log" | sed 's/^/    /'
      fail=1
    fi
  fi
  # value-parameter register inits: the shape the deep route used to
  # die on with an internal `unknown free variable` (loop-node analysis
  # ran outside the lambda scope it opened).  The file carries the
  # once-failing circuit, its controls, a Nat-derived init and a
  # two-level wrapper chain, plus a run_cmd pinning the IR init value.
  # Checked BY NAME, not by count: each of the five circuits must have
  # its PROVEN line, and the file's own run_cmd must emit a `VPI OK:`
  # line for it — printed only after both `_deep_trace` and
  # `_deep_signal_run` are found in the environment and pass the
  # ALLOWED-AXIOMS policy (a subset check: capstone → standard axioms
  # only; replay → standard + Lean.ofReduceBool + native_decide
  # auxiliaries recognised by name STRUCTURE for that circuit; anything
  # else, incl. sorryAx, rejects).  The file's negative cases must also
  # report `VPI NEG OK`, so a classifier that accepts everything fails
  # here.  A missing file is a failure, not a skip.
  VPI_FILE=Tests/Verification/ValueParamInitRepro.lean
  VPI_CIRCUITS="accK9 litInit initCirc7 natInit5 initCirc7Again"
  if [ ! -f "$VPI_FILE" ]; then
    echo "FAIL: $VPI_FILE is missing (value-param init regression gate)"
    fail=1
  elif lake build Tests.Verification.ValueParamInitRepro \
      > "$WORK/vpi.log" 2>&1; then
    vpi_ok=1
    for c in $VPI_CIRCUITS; do
      grep -q "ValueParamInitRepro\.$c: PROVEN" "$WORK/vpi.log" || {
        echo "FAIL: value-param inits — $c not PROVEN"; vpi_ok=0; }
      grep -q "VPI OK: $c " "$WORK/vpi.log" || {
        echo "FAIL: value-param inits — $c trace/replay theorem check missing"; vpi_ok=0; }
    done
    grep -q "VPI NEG OK" "$WORK/vpi.log" || {
      echo "FAIL: value-param inits — axiom-policy negative cases did not run"; vpi_ok=0; }
    if [ "$vpi_ok" -eq 1 ]; then
      echo "value-param register inits: 5 named circuits proven, trace+replay under allowed-axioms policy, negatives rejected"
    else
      fail=1
    fi
  else
    echo "FAIL: ValueParamInitRepro did not build"
    grep -m5 -E "error" "$WORK/vpi.log" | sed 's/^/    /'
    fail=1
  fi
  # cone-sharing premises on crc16's REAL body (build-time run_cmd that
  # throws on any failed premise; see the file header for the numbers)
  CSP_FILE=Tests/Verification/ConeSharingPremises.lean
  if [ ! -f "$CSP_FILE" ]; then
    echo "FAIL: $CSP_FILE is missing (cone-sharing premise gate)"; fail=1
  elif lake build Tests.Verification.ConeSharingPremises > "$WORK/csp.log" 2>&1 \
      && grep -q "CONE-SHARING crc16: 26 shared wires" "$WORK/csp.log"; then
    echo "cone-sharing premises: crc16 body, 26 shared wires, all premises hold"
  else
    echo "FAIL: cone-sharing premises on crc16 regressed"
    grep -m5 -E "error" "$WORK/csp.log" | sed 's/^/    /'; fail=1
  fi
  # cone-sharing PROTOTYPE: the CdoW route on shareX4 (the inlined route
  # fails this circuit); must build with no sorryAx in the trace theorem
  CSPROTO_FILE=Tests/Verification/ConeSharingProto.lean
  if [ ! -f "$CSPROTO_FILE" ]; then
    echo "FAIL: $CSPROTO_FILE is missing (cone-sharing prototype gate)"; fail=1
  elif lake build Tests.Verification.ConeSharingProto > "$WORK/csproto.log" 2>&1 \
      && grep -q "ShareW.trace' depends on axioms" "$WORK/csproto.log" \
      && ! grep -q "sorryAx" "$WORK/csproto.log"; then
    echo "cone-sharing prototype: shareX4 trace theorem proven on the CdoW route"
  else
    echo "FAIL: cone-sharing prototype (ConeSharingProto) regressed"
    grep -m5 -E "error|sorryAx" "$WORK/csproto.log" | sed 's/^/    /'; fail=1
  fi
  # cone-sharing REPLAY (plan step 2): signal_run on the shared route for
  # shareX4, with an in-file axiom policy (std + decision-procedure
  # auxiliaries only, never sorryAx); both policy lines must appear
  CSR_FILE=Tests/Verification/ConeSharingReplay.lean
  if [ ! -f "$CSR_FILE" ]; then
    echo "FAIL: $CSR_FILE is missing (cone-sharing replay gate)"; fail=1
  elif lake build Tests.Verification.ConeSharingReplay > "$WORK/csr.log" 2>&1 \
      && grep -q "CONE-SHARING REPLAY OK: Sparkle.Tests.ShareW.trace" "$WORK/csr.log" \
      && grep -q "CONE-SHARING REPLAY OK: Sparkle.Tests.ShareW.signal_run" "$WORK/csr.log"; then
    echo "cone-sharing replay: shareX4 trace + signal_run proven on the CdoW route (axiom policy ok)"
  else
    echo "FAIL: cone-sharing replay (ConeSharingReplay) regressed"
    grep -m5 -E "error|disallowed" "$WORK/csr.log" | sed 's/^/    /'; fail=1
  fi
  # F2 step 11 gate: the Opt and RT replay theorems must report the SAME
  # decision-procedure auxiliary count as the plain IR replay — i.e. the
  # optimizer/text bridges add no native_decide of their own; only the
  # trace's bv_decide auxiliaries remain (docs/SharedRoute-Guarantees.md
  # status table).  Reads the generator's "axioms: standard + N" clauses.
  replay_aux_match() {
    local log=$1 f=$2 n0 n1 n2
    n0=$(grep -oE "IR replay ${f}_sdeep_signal_run PROVEN \(axioms: standard \+ [0-9]+" "$log" | grep -oE '[0-9]+$')
    n1=$(grep -oE "${f}_sdeep_signal_runOpt PROVEN \([^)]*standard \+ [0-9]+" "$log" | grep -oE '[0-9]+$')
    n2=$(grep -oE "${f}_sdeep_signal_runRT PROVEN \([^)]*standard \+ [0-9]+" "$log" | grep -oE '[0-9]+$')
    if [ -n "$n0" ] && [ "$n0" = "$n1" ] && [ "$n0" = "$n2" ]; then return 0; fi
    echo "  replay auxiliaries differ for $f: run=$n0 runOpt=$n1 runRT=$n2"; return 1
  }
  # the GENERATOR's cone-sharing route (set_option sparkle.deepShare true):
  # trace + IR replay for shareX4 / shareX8, which the default route cannot
  # prove; both "PROVEN via CdoW.elab_general … IR replay … PROVEN" lines
  CSGEN_FILE=Tests/Verification/ConeSharingGen.lean
  if [ ! -f "$CSGEN_FILE" ]; then
    echo "FAIL: $CSGEN_FILE is missing (generator cone-sharing gate)"; fail=1
  elif lake build Tests.Verification.ConeSharingGen > "$WORK/csgen.log" 2>&1 \
      && [ "$(grep -c 'PROVEN via CdoW.elab_general' "$WORK/csgen.log")" -eq 2 ] \
      && [ "$(grep -c 'IR replay .* PROVEN' "$WORK/csgen.log")" -eq 2 ] \
      && [ "$(grep -c '_sdeep_signal_runOpt PROVEN' "$WORK/csgen.log")" -eq 2 ] \
      && [ "$(grep -c '_sdeep_signal_svOpt PROVEN' "$WORK/csgen.log")" -eq 2 ] \
      && [ "$(grep -c '_sdeep_signal_runRT PROVEN' "$WORK/csgen.log")" -eq 2 ] \
      && [ "$(grep -c '_sdeep_text_parses PROVEN' "$WORK/csgen.log")" -eq 2 ] \
      && replay_aux_match "$WORK/csgen.log" shareX4 \
      && replay_aux_match "$WORK/csgen.log" shareX8 \
      && ! grep -q 'SKIPPED' "$WORK/csgen.log"; then
    echo "generator cone-sharing route: shareX4 + shareX8 trace, replay, optimizer + SV + text bridges proven (Opt/RT replay axioms = the trace's)"
  else
    echo "FAIL: generator cone-sharing route (ConeSharingGen) regressed"
    grep -m5 -E "error|FAILED" "$WORK/csgen.log" | sed 's/^/    /'; fail=1
  fi
  # crc16CcittHW on the generator's cone-sharing route: trace + replay
  # (the default route cannot finish this circuit).  ~12 min; its own step.
  # F2: a cone equation discharged by the KERNEL (no native_decide).
  # Both slots must depend on the standard three axioms only.
  # (the two circuits' test modules cannot be imported into one file)
  kslot_ok=1
  for ks in ShareX Crc16; do
    KSLOT_FILE=Tests/Verification/ConeKernelSlot$ks.lean
    if [ ! -f "$KSLOT_FILE" ]; then
      echo "FAIL: $KSLOT_FILE is missing (kernel cone-equation gate)"; kslot_ok=0
    elif lake build Tests.Verification.ConeKernelSlot$ks > "$WORK/kslot$ks.log" 2>&1 \
        && grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$WORK/kslot$ks.log" \
        && ! grep -q "native_decide\|sorryAx" "$WORK/kslot$ks.log"; then
      :
    else
      echo "FAIL: kernel cone-equation slot $ks regressed (or picked up a decision-procedure axiom)"
      grep -m5 -E "error|axioms" "$WORK/kslot$ks.log" | sed 's/^/    /'; kslot_ok=0
    fi
  done
  if [ "$kslot_ok" = 1 ]; then
    echo "kernel cone equations: shareX4 + crc16 slots proven, standard axioms only"
  else
    fail=1
  fi
  CRC_FILE=Tests/Verification/ConeSharingCrc16.lean
  if [ ! -f "$CRC_FILE" ]; then
    echo "FAIL: $CRC_FILE is missing (crc16 cone-sharing gate)"; fail=1
  elif lake build Tests.Verification.ConeSharingCrc16 > "$WORK/crc16share.log" 2>&1 \
      && grep -q "crc16CcittHW: PROVEN via CdoW.elab_general" "$WORK/crc16share.log" \
      && grep -q "IR replay crc16CcittHW_sdeep_signal_run PROVEN" "$WORK/crc16share.log" \
      && grep -q "crc16CcittHW_sdeep_signal_runOpt PROVEN" "$WORK/crc16share.log" \
      && grep -q "crc16CcittHW_sdeep_signal_runRT PROVEN" "$WORK/crc16share.log" \
      && grep -q "crc16CcittHW_sdeep_text_parses PROVEN" "$WORK/crc16share.log" \
      && replay_aux_match "$WORK/crc16share.log" crc16CcittHW \
      && [ "$(grep -c 'SKIPPED' "$WORK/crc16share.log")" -eq 1 ] \
      && grep -q "Opt SV-semantics theorem SKIPPED" "$WORK/crc16share.log"; then
    echo "crc16 cone-sharing route: trace, IR replay, optimizer + text bridges proven (Opt/RT replay axioms = the trace's; SV-semantics theorem skipped by the M4 shl rule, as documented)"
  else
    echo "FAIL: crc16 on the cone-sharing route regressed"
    grep -m5 -E "error|FAILED" "$WORK/crc16share.log" | sed 's/^/    /'; fail=1
  fi
  # Strict roundtrip acceptance: a proof-carrying artifact requires all links,
  # and composes the parse theorem with replay. Partial PROVEN is not accepted.
  cert_files_ok=1
  for ct in CertifiedRoundtripTest CertifySharedCommandTest CertifiedRoundtripCrc16 VerifiedBlockTest VerifiedStateTest VerifiedCircuitTest VerifiedSourceTest; do
    if [ ! -f "Tests/Verification/$ct.lean" ]; then
      echo "FAIL: missing strict certification test $ct"; cert_files_ok=0
    fi
  done
  if [ "$cert_files_ok" -eq 1 ] \
      && lake build Tests.Verification.CertifiedRoundtripTest \
        Tests.Verification.CertifySharedCommandTest \
        Tests.Verification.CertifiedRoundtripCrc16 \
        Tests.Verification.VerifiedBlockTest \
        Tests.Verification.VerifiedStateTest \
        Tests.Verification.VerifiedCircuitTest \
        Tests.Verification.VerifiedSourceTest > "$WORK/certification.log" 2>&1 \
      && grep -Fq "CERTIFICATION TEST OK:" "$WORK/certification.log" \
      && grep -Fq "CERTIFIED_ROUNDTRIP Sparkle.Tests.CertifySharedCommandTest.counter:" "$WORK/certification.log" \
      && grep -Fq "CRC16 CERTIFICATION OK:" "$WORK/certification.log" \
      && grep -Fq "VERIFIED BLOCK OK:" "$WORK/certification.log" \
      && grep -Fq "VERIFIED STATE OK:" "$WORK/certification.log" \
      && grep -Fq "VERIFIED CIRCUIT OK:" "$WORK/certification.log" \
      && grep -Fq "VERIFIED SOURCE OK:" "$WORK/certification.log"; then
    echo "certification: complete roundtrip artifacts, general soundness, negative cases checked"
  else
    echo "FAIL: strict roundtrip certification gate"; fail=1
  fi
  # the SEAM bridge: per-instance composition of the generated
  # recurrence with the module-level fold semantics (ConeFold capstone
  # instantiated on cnt8; checker hypotheses by native_decide)
  BRIDGE_FILE=Tests/Verification/ConeBridgeDemo.lean
  if [ -f "$BRIDGE_FILE" ]; then
    lake build Tools.ConeFoldSlices Tests.Verification.VerifyElabDemo \
        >> "$WORK/deep_build.log" 2>&1 || {
      echo "FAIL: could not build the cone-bridge import closure"; fail=1; }
    if lake env lean "$BRIDGE_FILE" > "$WORK/cone_bridge.log" 2>&1; then
      echo "cone-bridge (seam per-instance): cnt8 step agreement proven"
    else
      echo "FAIL: cone-bridge demo did not close"
      grep -m3 -E "error" "$WORK/cone_bridge.log" | sed 's/^/    /'
      fail=1
    fi
  fi
fi

if [ "$fail" != "0" ]; then echo "== XiangShan gate: FAILED"; exit 1; fi
echo "== XiangShan gate: OK (roundtrip ${wall}s, equiv $equiv_ok proven/$equiv_skip skipped)"
