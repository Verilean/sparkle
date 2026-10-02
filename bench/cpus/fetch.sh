#!/usr/bin/env bash
# Fetch the pinned CPU sources and lay them out one module per file under
# <dest>/split/<corpus>/ (the layout sv-roundtrip / sv-cosim --hier expect).
# usage: fetch.sh <dest>
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
dest="${1:?usage: fetch.sh <dest>}"; mkdir -p "$dest/src" "$dest/split"
get() {  # get <name> <repo> <commit>
  if [ ! -d "$dest/src/$1" ]; then
    git init -q "$dest/src/$1"
    git -C "$dest/src/$1" fetch -q --depth 1 "https://github.com/$2.git" "$3"
    git -C "$dest/src/$1" checkout -q FETCH_HEAD
  fi
}
get picorv32 YosysHQ/picorv32 ef203c2b0a3fb793280f5114941416c425c5b461
get vexriscv litex-hub/pythondata-cpu-vexriscv 642ecfed1c84460555d6d803d660cc60cfc1ecb6
python3 "$here/split.py" "$dest/src/picorv32/picorv32.v" "$dest/split/picorv32"
for f in "$dest"/src/vexriscv/pythondata_cpu_vexriscv/verilog/*.v; do
  python3 "$here/split.py" "$f" "$dest/split/$(basename "$f" .v)"
done
echo "corpora: $(ls "$dest/split" | wc -l) directories under $dest/split"
