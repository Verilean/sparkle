#!/usr/bin/env bash
# Tang Nano 20k build + flash for the Sparkle UART signing demo.
#   1. lake env lean build/GenSignDemoSynth.lean   # -> build/sign_z_demo.v
#   2. ./sign_z_demo_build.sh                          # yosys -> nextpnr -> gowin_pack
#   3. ./sign_z_demo_build.sh flash                    # openFPGALoader (SRAM)
#      ./sign_z_demo_build.sh flash-spi                # persist to on-board flash
set -euo pipefail
cd "$(dirname "$0")"

DEVICE_PNR="GW2AR-LV18QN88C8/I7"
DEVICE_PACK="GW2A-18C"
TOP="sign_z_demo_top"
CST="sign_z_demo.cst"
B=build

if [ "${1:-build}" = "flash" ]; then
    openFPGALoader -b tangnano20k "$B/sign_z_demo.fs"; exit 0
fi
if [ "${1:-build}" = "flash-spi" ]; then
    openFPGALoader -b tangnano20k -f "$B/sign_z_demo.fs"; exit 0
fi

echo "== yosys (synth_gowin, ABC9 LUT packing, -top $TOP) =="
# ABC9 (default) packs LUTs ~30% tighter than -noabc9; this design is small
# enough that it fits in RAM (unlike the full fast signer, which needs -noabc9).
# FLAT synth gives the tight cross-module LUT packing that fits the fabric
# (~72% LUT4), unlike -noflatten which triples the LUT count (221%, unplaceable).
# Replace the stock `abc9 -maxlut 8 -W 500` with `abc9 -maxlut 8` — the -W
# wire-delay refinement is a memory hog; without it abc9 packs identically at
# ~1 GB.  The map_cells techmap is still RAM-heavy on an 8 GB host (LUT-template
# expansion) but completes through swap.
yosys -p "read_verilog -sv $B/sign_z_demo.v; \
          read_verilog -sv ${TOP}.v; \
          synth_gowin -top $TOP -run :map_luts; \
          read_verilog -icells -lib -specify +/abc9_model.v; \
          abc9 -maxlut 8; \
          synth_gowin -top $TOP -run map_cells:; \
          write_json $B/sign_z_demo.json" 2>&1 | tee "$B/szd_yosys.log" | \
  grep -E "Number of cells|LUT|DFF|ALU|BSRAM|Warnings" || true

echo "== nextpnr-himbaechel (--device $DEVICE_PNR) =="
# --no-tmdriv + high --placer-heap-beta pack for DENSITY (the design sits at
# ~87% LUT4; timing-driven placement leaves too much slack to legalise).
nextpnr-himbaechel --device "$DEVICE_PNR" \
    --vopt family=GW2A-18C --vopt cst="$CST" \
    --json "$B/sign_z_demo.json" --write "$B/sign_z_demo_pnr.json" 2>&1 | tee "$B/szd_pnr.log" | \
  grep -iE "Device utilisation|Info:.*[0-9]+/[0-9]+|error|Max frequency|Program finished" || true

echo "== gowin_pack (-d $DEVICE_PACK) =="
gowin_pack -d "$DEVICE_PACK" -o "$B/sign_z_demo.fs" "$B/sign_z_demo_pnr.json"

echo "OK -> $B/sign_z_demo.fs   (flash with: ./sign_z_demo_build.sh flash)"
