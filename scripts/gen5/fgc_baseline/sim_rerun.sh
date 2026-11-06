#!/usr/bin/env bash
# S0: rerun of the 11 simulation checks that were not exit 0 in kjob-run-src-fgc-s0run-babb.
#
#   timeout 900 scripts/gen5/fgc_baseline/sim_rerun.sh GROUP OUT
#
# GROUP: env      cdc_runner.so + SoC Verilog, then the env-dependent exes, verify-parameterized-csim
#        h264     delete the generated .lake/build/gen/h264, regenerate, rerun the 3 JIT exes
#        test     `lake exe test` (its own log; the earlier run's log was overwritten by the timeout run)
#        toplevel toplevel-sim-test (pure-Lean Signal eval, O(t^2)) vs its JIT variant toplevel-sim-jit-test
# Run inside `kjob lake env` (LEAN / LEAN_PATH set).  Logs -> OUT/sim_rerun/<name>.log, one line per
# check -> OUT/sim_rerun/<GROUP>.tsv (name, exit, seconds).  Raw logs stay outside the source tree.
set -u
cd "$(dirname "$0")/../../.."
G="$1"; OUT="$2"; D="$OUT/sim_rerun"; mkdir -p "$D"; : > "$D/$G.tsv"
TMO="${SIM_TMO:-900}"
run() {  # name, command...
  n="$1"; shift; t0=$(date +%s)
  timeout -k 5 "$TMO" "$@" > "$D/$n.log" 2>&1; rc=$?
  echo -e "$n\t$rc\t$(( $(date +%s) - t0 ))" | tee -a "$D/$G.tsv"
}
# Inside `kjob lake env`, a nested `lake exe` cannot start the built binary ("could not execute external
# process .../.lake/build/bin/<exe>", first rerun 2026-11-06), so build with `lake build` and run the binary
# directly.  Each `kjob lake` invocation is a fresh job copy, so everything a check needs is built here.
xrun() { local n="$1" e="$2"; lake build "$e" > "$D/build-$e.log" 2>&1 || { echo -e "$n\t1\t0" >> "$D/$G.tsv"; return; }; run "$n" "./.lake/build/bin/$e"; }
case "$G" in
  env)
    run make-cdc_runner make -C c_src/cdc cdc_runner.so
    # verilator/generated_soc.sv is written by #writeDesign while IP/RV32/SoCVerilog.lean elaborates; a cached
    # lake build only replays the .olean and does not write it (bitnet-soc / rv32-flow failed on that, 2026-11-06).
    run build-SoCVerilog lake build IP.RV32.SoCVerilog
    run write-SoCVerilog "${LEAN:-lean}" --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so IP/RV32/SoCVerilog.lean
    run check-generated_soc test -s verilator/generated_soc.sv
    for e in cdc-multi-clock-test sim-runner-test bitnet-soc-test rv32-flow-test; do xrun "exe-$e" "$e"; done
    lake build Tests.SymbolicParameterCircuits > "$D/build-symbolic.log" 2>&1
    run verify-parameterized-csim bash scripts/verify_parameterized_csim.sh ;;
  h264)
    rm -rf .lake/build/gen/h264
    run build-h264 lake build h264-bitstream-test h264-playable-test h264-frame-encoder-test
    for f in encoder_pipeline cavlc_synth; do
      echo "== $f: wires in generated JIT" > "$D/jitwires-$f.log"
      grep -o '"_gen_[A-Za-z0-9_]*"' ".lake/build/gen/h264/${f}_jit.c" | sort -u >> "$D/jitwires-$f.log" 2>&1
    done
    for e in h264-bitstream-test h264-playable-test h264-frame-encoder-test; do xrun "exe-$e" "$e"; done ;;
  test)
    # the test driver also checks verilator/generated_soc{.sv,_cppsim.h} (RV32 SoC flow): write them first, as in env
    run build-SoCVerilog lake build IP.RV32.SoCVerilog
    run write-SoCVerilog "${LEAN:-lean}" --load-dynlib=.lake/build/lib/libsparkle_Sparkle.so IP/RV32/SoCVerilog.lean
    run check-generated_soc test -s verilator/generated_soc.sv
    xrun exe-test-rerun test ;;
  toplevel) xrun exe-toplevel-sim-test toplevel-sim-test; xrun exe-toplevel-sim-jit-test toplevel-sim-jit-test ;;
  *) echo "unknown group $G" >&2; exit 2 ;;
esac
