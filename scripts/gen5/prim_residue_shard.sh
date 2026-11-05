#!/usr/bin/env bash
# D.D-4 res3: one shard of the per-file scan as a kjob Job.  usage: prim_residue_shard.sh LISTFILE TAG
# Output goes next to KJOB_REPORT_PATH (outside the source tree).
set -u
LIST="$1"; TAG="$2"
OUT="$(dirname "$KJOB_REPORT_PATH")/res3/$TAG"
mkdir -p "$OUT"
timeout 900 kjob lake build Tests.Gen5.PrimResidueLib || exit 1
kjob lake env bash scripts/gen5/prim_residue_dyn.sh "$LIST" "$OUT"
