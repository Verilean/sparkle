#!/usr/bin/env bash
# D.D-4 res3: one batch of the iota probe: roots FROM..FROM+4 (5 roots), fuel FUEL, wrapped in timeout 900.
#   iota_probe_batch.sh OUTDIR FROM FUEL      (run under `kjob lake env`-less shell; this script calls kjob lake env itself)
set -u
OUT="$1"; FROM="$2"; FUEL="$3"
mkdir -p "$OUT"
f="$OUT/probe_$FROM.lean"
printf 'import Tests.Gen5.IotaStudy\nopen Tests.Gen5.IotaStudy\n#iota_probe %s 5\n' "$FUEL" > "$f"
s=$(date +%s)
PRIM_PROBE_FROM="$FROM" KJOB_REPORT_PATH="$OUT/r" timeout 900 kjob lake env lean "$f" > "$OUT/log_$FROM.txt" 2>&1
echo "$FROM rc=$? secs=$(( $(date +%s) - s ))" >> "$OUT/batches.txt"
