#!/usr/bin/env bash
# Fetch the third-party designs the SV-interop examples run against, at
# pinned commits, into Examples/SvInterop/third_party/ (git-ignored).
#
#   verilog-axi   (Alex Forencich, MIT)  axil_ram.v
#   verilog-axis  (Alex Forencich, MIT)  axis_adapter.v, axis_fifo.v
#   picorv32      (Claire Wolf, ISC)     picorv32.v
#
# Nothing from these repositories is committed here.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p third_party
fetch() {  # name url commit
  local dir="third_party/$1"
  if [ -d "$dir/.git" ] && [ "$(git -C "$dir" rev-parse HEAD)" = "$3" ]; then
    echo "$1: already at $3"; return
  fi
  rm -rf "$dir"
  git init -q "$dir"
  git -C "$dir" remote add origin "$2"
  git -C "$dir" fetch -q --depth 1 origin "$3"
  git -C "$dir" checkout -q FETCH_HEAD
  echo "$1: fetched $3"
}
fetch verilog-axi  https://github.com/alexforencich/verilog-axi.git  516bd5dadc3365b7f9e225d2af8fe0b8d804fe53
fetch verilog-axis https://github.com/alexforencich/verilog-axis.git 48ff7a7e2ef782cf778d47910cf85835c64b1bce
fetch picorv32     https://github.com/YosysHQ/picorv32.git           ef203c2b0a3fb793280f5114941416c425c5b461
