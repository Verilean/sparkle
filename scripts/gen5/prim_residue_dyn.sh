#!/usr/bin/env bash
# D.D-4 res2: run each listed corpus file standalone (`lean FILE`, SPARKLE_PROFILE=1) with the residue scan appended.
#   kjob lake env bash scripts/gen5/prim_residue_dyn.sh LIST OUTDIR      (cwd = repository root; OUTDIR outside the source tree)
# Per file: OUTDIR/raw/TAG.{roots,consts,recsites,poly,prof,missing}  (from #prim_residue_scan), OUTDIR/err/TAG.txt (error lines),
# OUTDIR/status.tsv (file, rc, seconds, stdout lines, error lines).  Roots = the declarations the compiler's own log shows past the
# front-end dispatch in THIS run, plus the file's own route-marked / @[hardware_module] definitions.
set -u
LIST="$1"; OUT="$2"
mkdir -p "$OUT/raw" "$OUT/err" "$OUT/src"
LOG=/tmp/sparkle-profile.log
: > "$LOG"
while read -r f; do
  [ -z "$f" ] && continue
  tag=$(echo "$f" | tr / _ | sed 's/\.lean$//')
  src="$OUT/src/$tag.lean"
  n=$(grep -nE '^import ' "$f" | tail -1 | cut -d: -f1); n=${n:-0}
  { head -n "$n" "$f"; echo "import Tests.Gen5.PrimResidueLib"; tail -n +"$((n+1))" "$f"; printf '\n#prim_residue_scan\n'; } > "$src"
  off=$(stat -c %s "$LOG")
  s=$(date +%s)
  PRIM_RES_OUT="$OUT/raw/$tag" PRIM_RES_MODS='<local>' PRIM_RES_PROFILE="$LOG" PRIM_RES_PROFOFF="$off" \
    SPARKLE_PROFILE=1 timeout 900 lean "$src" > "$OUT/stdout.tmp" 2> "$OUT/stderr.tmp"
  rc=$?
  e=$(date +%s)
  grep -E 'error' "$OUT/stdout.tmp" > "$OUT/err/$tag.txt"
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$rc" "$((e-s))" "$(wc -l < "$OUT/stdout.tmp")" "$(wc -l < "$OUT/err/$tag.txt")" >> "$OUT/status.tsv"
  rm -f "$OUT/src/$tag.lean"
done < "$LIST"
