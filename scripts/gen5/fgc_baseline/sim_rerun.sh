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
case "$G" in
  env)
    run make-cdc_runner make -C c_src/cdc cdc_runner.so
    run build-SoCVerilog lake build IP.RV32.SoCVerilog
    for e in cdc-multi-clock-test sim-runner-test bitnet-soc-test rv32-flow-test; do run "exe-$e" lake exe "$e"; done
    run verify-parameterized-csim bash scripts/verify_parameterized_csim.sh ;;
  h264)
    rm -rf .lake/build/gen/h264
    run build-h264 lake build h264-bitstream-test h264-playable-test h264-frame-encoder-test
    for f in encoder_pipeline cavlc_synth; do
      echo "== $f: wires in generated JIT" > "$D/jitwires-$f.log"
      grep -o '"_gen_[A-Za-z0-9_]*"' ".lake/build/gen/h264/${f}_jit.c" | sort -u >> "$D/jitwires-$f.log" 2>&1
    done
    for e in h264-bitstream-test h264-playable-test h264-frame-encoder-test; do run "exe-$e" lake exe "$e"; done ;;
  test) run exe-test-rerun lake exe test ;;
  toplevel) run exe-toplevel-sim-test lake exe toplevel-sim-test; run exe-toplevel-sim-jit-test lake exe toplevel-sim-jit-test ;;
  *) echo "unknown group $G" >&2; exit 2 ;;
esac
