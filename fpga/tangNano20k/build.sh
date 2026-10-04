#!/usr/bin/env bash
# Tang Nano 20k (GW2AR-18) build + flash for the Sparkle policy signer.
#
#   1. lake env lean build/GenPolicySigner.lean   # -> build/policy_signer.v (full design)
#   2. ./build.sh                                  # yosys -> nextpnr -> gowin_pack
#   3. ./build.sh flash                            # openFPGALoader (SRAM) ; 'flash-spi' for flash
#
# Toolchain: yosys + nextpnr-himbaechel + gowin_pack (apycula) + openFPGALoader.
set -euo pipefail
cd "$(dirname "$0")"

DEVICE_PNR="GW2AR-LV18QN88C8/I7"   # nextpnr-himbaechel --device
DEVICE_PACK="GW2A-18C"             # gowin_pack -d
TOP="policy_signer_top"
CST="policy_signer.cst"
B=build

if [ "${1:-build}" = "flash" ]; then
    openFPGALoader -b tangnano20k "$B/policy_signer.fs"
    exit 0
fi
if [ "${1:-build}" = "flash-spi" ]; then
    openFPGALoader -b tangnano20k -f "$B/policy_signer.fs"   # persist to on-board flash
    exit 0
fi

echo "== yosys (synth_gowin -noabc9, -top $TOP) =="
# -noabc9: the ABC9 LUT-mapping pass blows RAM past this box's 7.7 GiB on the
# secp256k1 signer (~8.6M wire bits) and forces heavy swap.  Classic mapping is
# far lighter; LUT packing is only slightly looser.
yosys -p "read_verilog -sv $B/policy_signer.v; \
          read_verilog -sv ${TOP}.v; \
          synth_gowin -noabc9 -top $TOP -json $B/policy_signer.json" 2>&1 | tee "$B/yosys.log" | \
  grep -E "Number of cells|LUT|DFF|ALU|BSRAM|MUX|Warnings" || true

echo "== nextpnr-himbaechel (--device $DEVICE_PNR) =="
# GW2A-series himbaechel needs an explicit `--vopt family=…` (validated
# against the blinky bring-up on real hardware).
nextpnr-himbaechel --device "$DEVICE_PNR" \
    --vopt family=GW2A-18C \
    --vopt cst="$CST" \
    --json "$B/policy_signer.json" \
    --write "$B/policy_signer_pnr.json" 2>&1 | tee "$B/pnr.log" | \
  grep -iE "Info:.*[0-9]+/[0-9]+|LUT|DFF|ALU|error|Max frequency" || true

echo "== gowin_pack (-d $DEVICE_PACK) =="
gowin_pack -d "$DEVICE_PACK" -o "$B/policy_signer.fs" "$B/policy_signer_pnr.json"

echo "OK -> $B/policy_signer.fs   (flash with: ./build.sh flash)"
