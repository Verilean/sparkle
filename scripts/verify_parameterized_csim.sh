#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

cd "$repo_root"
template="Tests/ParameterizedCppSimEmit.lean.in"
fixture="Tests/Fixtures/symbolic_xor_csim.c.in"

for width in 3 17 65; do
  lean_source="$work_dir/symbolic_xor_w${width}.lean"
  generated_c="$work_dir/symbolic_xor_w${width}.c"
  executable="$work_dir/symbolic_xor_w${width}"

  sed \
    -e "s|@WIDTH@|${width}|g" \
    -e "s|@OUTPUT_C@|${generated_c}|g" \
    "$template" > "$lean_source"

  lake env lean "$lean_source"
  if [[ ! -s "$generated_c" ]]; then
    echo "parameterized CSim did not generate W=${width}" >&2
    exit 1
  fi

  cc -O2 -std=gnu11 -Wall -Wextra -Werror \
    -DTEST_WIDTH="$width" \
    -include "$generated_c" \
    -x c \
    "$fixture" \
    -o "$executable"
  "$executable"
done
