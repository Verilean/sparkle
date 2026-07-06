#!/usr/bin/env bash
# Tang Nano 20k build + flash for the Sparkle UART signing demo.
#   1. lake env lean build/GenSignDemoSynth.lean   # -> build/sign_msg_demo.v
#   2. ./sign_msg_demo_build.sh                          # yosys -> nextpnr -> gowin_pack
#   3. ./sign_msg_demo_build.sh flash                    # openFPGALoader (SRAM)
#      ./sign_msg_demo_build.sh flash-spi                # persist to on-board flash
set -euo pipefail
cd "$(dirname "$0")"

DEVICE_PNR="GW2AR-LV18QN88C8/I7"
DEVICE_PACK="GW2A-18C"
TOP="sign_msg_demo_top"
CST="sign_msg_demo.cst"
B=build

if [ "${1:-build}" = "flash" ]; then
    openFPGALoader -b tangnano20k "$B/sign_msg_demo.fs"; exit 0
fi
if [ "${1:-build}" = "flash-spi" ]; then
    openFPGALoader -b tangnano20k -f "$B/sign_msg_demo.fs"; exit 0
fi

echo "== yosys (synth_gowin, ABC9 LUT packing, -top $TOP) =="
# ABC9 (default) packs LUTs ~30% tighter than -noabc9; this design is small
# enough that it fits in RAM (unlike the full fast signer, which needs -noabc9).
yosys -p "read_verilog -sv $B/sign_msg_demo.v; \
          read_verilog -sv ${TOP}.v; \
          synth_gowin -top $TOP -json $B/sign_msg_demo.json" 2>&1 | tee "$B/smd_yosys.log" | \
  grep -E "Number of cells|LUT|DFF|ALU|BSRAM|Warnings" || true

echo "== nextpnr-himbaechel (--device $DEVICE_PNR) =="
nextpnr-himbaechel --device "$DEVICE_PNR" \
    --vopt family=GW2A-18C --vopt cst="$CST" \
    --json "$B/sign_msg_demo.json" --write "$B/sign_msg_demo_pnr.json" 2>&1 | tee "$B/smd_pnr.log" | \
  grep -iE "Device utilisation|Info:.*[0-9]+/[0-9]+.*%|error|Max frequency|Program finished" || true

echo "== gowin_pack (-d $DEVICE_PACK) =="
gowin_pack -d "$DEVICE_PACK" -o "$B/sign_msg_demo.fs" "$B/sign_msg_demo_pnr.json"

echo "OK -> $B/sign_msg_demo.fs   (flash with: ./sign_msg_demo_build.sh flash)"
