#!/usr/bin/env bash
# Round-trip and 3-way co-simulate every corpus under <dest>/split.
# usage: run.sh <dest> [jobs=4]
# SV_COSIM_FLAGS=--fused-local (or --fused) drives the JIT side through
# eval_tick, the fused fast path, instead of eval + tick.
# Run it under a memory limit, e.g.
#   systemd-run --user --scope -p MemoryMax=60G -p MemorySwapMax=0 bench/cpus/run.sh <dest>
set -uo pipefail
cd "$(dirname "$0")/../.."
dest="${1:?usage: run.sh <dest> [jobs]}"; jobs="${2:-4}"
bin="$PWD/.lake/build/bin"
[ -x "$bin/sv-roundtrip" ] && [ -x "$bin/sv-cosim" ] || lake build sv-roundtrip sv-cosim
rm -rf "$dest/rt" "$dest/logs"; mkdir -p "$dest/rt" "$dest/logs"
count() { grep -E "^  $2" "$1" | awk '{print $NF}' | head -1; }
fail=0
printf '%-24s %-10s %-22s %-22s\n' corpus roundtrip "leaf ok/rt/jit/skip" "hier ok/rt/jit/skip"
for d in "$dest"/split/*; do n=$(basename "$d")
  (cd "$dest/logs" && "$bin/sv-roundtrip" "$d" --jobs "$jobs" --emit "$dest/rt/$n" > "$n.rt" 2>&1)
  "$bin/sv-cosim" "$d" "$dest/rt/$n" --jobs "$jobs" --cycles 300 --max-kb 4096 --zero-init ${SV_COSIM_FLAGS:-} > "$dest/logs/$n.leaf" 2>&1
  "$bin/sv-cosim" "$d" "$dest/rt/$n" --jobs "$jobs" --cycles 300 --max-kb 4096 --hier --zero-init ${SV_COSIM_FLAGS:-} > "$dest/logs/$n.hier" 2>&1
  row() { echo "$(count "$1" OK)/$(count "$1" 'RT mismatch')/$(count "$1" 'JIT mismatch')/$(count "$1" skipped)"; }
  nfiles=$(ls "$d" | wc -l)
  printf '%-24s %-10s %-22s %-22s\n' "$n" "$(count "$dest/logs/$n.rt" OK)/$nfiles" "$(row "$dest/logs/$n.leaf")" "$(row "$dest/logs/$n.hier")"
  [ "$(count "$dest/logs/$n.rt" OK)" = "$nfiles" ] || fail=1
  grep -qE 'RT✗|JIT✗|TOOL✗' "$dest/logs/$n.leaf" "$dest/logs/$n.hier" && fail=1
done
grep -hE 'RT✗|JIT✗|TOOL✗' "$dest"/logs/*.leaf "$dest"/logs/*.hier | cut -c1-200 | sort | uniq -c | sort -rn | head -20
if [ -f "$dest/src/picorv32/picorv32.v" ]; then
  bench/cpus/picorv32_prog/run.sh "$dest/src/picorv32/picorv32.v" "$dest/rt/picorv32" "$dest/logs/prog" || fail=1
fi
exit $fail
