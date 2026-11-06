#!/usr/bin/env bash
# S0 output baseline: re-elaborate the files that contain #writeDesign / #writeVerilogDesign (18 commands in
# 16 files) with the same compiler, then hash and store every file those commands wrote (collect_outputs.py).
#
#   timeout 900 scripts/gen5/fgc_baseline/capture_outputs.sh OUT
#
# Run inside `kjob lake env` (LEAN / LEAN_PATH set) after `lake build Sparkle IP.Video IP.RV32 ...` (the same
# libs capture.sh needs; the files import them).  Raw stdout -> OUT/out_outputs/, status -> OUT/status_outputs/,
# stored output files + output_baseline.tsv -> OUT/output_store/ (all outside the source tree).
# Afterwards: python3 scripts/gen5/fgc_baseline/summarize.py RAW DEST --outputs OUT/output_store/output_baseline.tsv
# Exit 1 if any output is missing/empty (not a baseline).
set -u
cd "$(dirname "$0")/../../.."
OUT="$1"; S=scripts/gen5/fgc_baseline
mkdir -p "$OUT/outputs_run"
awk -F'\t' 'NR>1 && ($3=="#writeDesign" || $3=="#writeVerilogDesign") {print $1}' $S/inventory.tsv | sort -u > "$OUT/outputs_run/files.txt"
# capture.sh keeps raw stdout under OUT/out and the status under OUT/status; use a separate OUT so the full capture is untouched
cp $S/inventory.tsv "$OUT/outputs_run/"
REDO=1 bash $S/capture.sh "$OUT/outputs_run" "$OUT/outputs_run/files.txt" || exit $?
python3 -I $S/collect_outputs.py "$OUT/outputs_run" "$OUT/output_store"
