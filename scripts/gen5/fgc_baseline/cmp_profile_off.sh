#!/usr/bin/env bash
# S1q baseline comparison: build the libs, then capture every inventory file with SPARKLE_PROFILE unset
# (CAP_PROFILE=0) and the 16 output-writing files. Raw output goes next to KJOB_REPORT_PATH (outside the tree).
# Run as: kjob run ... -- kjob lake env bash scripts/gen5/fgc_baseline/cmp_profile_off.sh
set -u
cd "$(dirname "$0")/../../.."
S=scripts/gen5/fgc_baseline
OUT="$(dirname "${KJOB_REPORT_PATH:?}")/fgc_cmp_off"
mkdir -p "$OUT" && cp $S/inventory.tsv "$OUT/"
lake build Tests.AllTests || exit 10
lake build IP.RV32 IP.YOLOv8 IP.Video IP.Bus IP.Arbiter Examples.CDC || exit 11
lake build IP.RV32.SoCVerilog || exit 12
CAP_PROFILE=0 bash $S/capture.sh "$OUT" || exit 13
CAP_PROFILE=0 bash $S/capture_outputs.sh "$OUT"; echo "capture_outputs rc=$?"
echo "cmp_profile_off done: $OUT"
