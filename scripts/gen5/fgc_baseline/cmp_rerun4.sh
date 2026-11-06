#!/usr/bin/env bash
# Re-capture the 4 inventory files whose imported IP modules the first comparison run did not build
# (IP.Net.MemcachedHW, IP.Crypto.GHASHHW, IP.Net.SLIP, IP.Net.UsbWebServer), with SPARKLE_PROFILE unset.
# Run as: kjob run ... -- kjob lake env bash scripts/gen5/fgc_baseline/cmp_rerun4.sh
set -u
cd "$(dirname "$0")/../../.."
S=scripts/gen5/fgc_baseline
OUT="$(dirname "${KJOB_REPORT_PATH:?}")/fgc_cmp_off4"
mkdir -p "$OUT" && cp $S/inventory.tsv "$OUT/"
printf '%s\n' Tests/Compiler/MultiOutputSubModuleHangRepro.lean Tests/IP/Crypto/GHASHHWSynth.lean Tests/IP/Net/SLIPTest.lean Tests/IP/Net/UsbWebServerSynth.lean > "$OUT/files4.txt"
lake build Sparkle IP.Net.MemcachedHW IP.Crypto.GHASHHW IP.Net.SLIP IP.Net.UsbWebServer || exit 10
CAP_PROFILE=0 REDO=1 bash $S/capture.sh "$OUT" "$OUT/files4.txt" || exit 13
echo "cmp_rerun4 done: $OUT"
