#!/usr/bin/env bash
# Redundancy metric: yosys cell counts, original vs roundtripped, per module.
# Usage: ./compare_stat.sh <orig-dir> <rt-dir> <out.tsv> [jobs]
set -u
ORIG=$1; RT=$2; OUT=$3; JOBS=${4:-24}
one() {
  f=$(basename "$1")
  # `synth -run coarse` : techn.-independent optimization (proc/opt/memory/fsm)
  # — enough to expose real redundancy without gate mapping noise.
  # yosys 0.62 stat format: "       N cells"
  o=$(yosys -p "read_verilog -sv $2/$f; hierarchy -auto-top; synth -run coarse; stat" 2>/dev/null \
      | awk '$2=="cells" && $1 ~ /^[0-9]+$/{print $1}' | tail -1)
  r=$(yosys -p "read_verilog -sv $3/$f; hierarchy -auto-top; synth -run coarse; stat" 2>/dev/null \
      | awk '$2=="cells" && $1 ~ /^[0-9]+$/{print $1}' | tail -1)
  echo -e "$f\t${o:-ERR}\t${r:-ERR}"
}
export -f one
ls "$RT" | xargs -P "$JOBS" -I{} bash -c 'one "$@"' _ {} "$ORIG" "$RT" > "$OUT"
echo "done → $OUT"
