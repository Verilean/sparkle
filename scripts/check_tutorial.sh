#!/usr/bin/env bash
# Type-check every ```lean block in docs/Tutorial.md.
#
# Usage: bash scripts/check_tutorial.sh [path/to/Tutorial.md]
#
# Exits non-zero if any block fails `lake env lean`. Blocks annotated with
# `<!-- no-compile -->` immediately before the fence are skipped.

set -euo pipefail

MD="${1:-docs/Tutorial.md}"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

# Ensure every module a tutorial block might `import` is built. `lake build`
# alone does not transitively compile modules that aren't reachable from
# `Sparkle.lean` (e.g. the lint module). List them explicitly here.
lake build Sparkle.Compiler.SynthesizableLint

python3 scripts/extract_tutorial_blocks.py "$MD" "$OUT"

fail=0
for f in "$OUT"/block_*.lean; do
  [ -e "$f" ] || continue
  echo "=== Type-checking $(basename "$f") ==="
  # Capture output without `set -e` killing us on `lake env lean`'s nonzero
  # exits, and without `pipefail` failing when grep finds no matches.
  set +e
  log=$(lake env lean "$f" 2>&1)
  set -e
  echo "$log"
  # `lake env lean` may exit nonzero for pure `#eval` runtime failures (e.g.
  # missing native symbols for opaque functions). Ignore those and only fail
  # on real elaboration errors.
  real_errors=$(printf '%s\n' "$log" \
    | grep -E '^([^:]+):[0-9]+:[0-9]+: error:' \
    | grep -v 'Could not find native implementation' \
    || true)
  if [ -n "$real_errors" ]; then
    echo "FAIL: $(basename "$f") (elaboration error)"
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo ""
  echo "One or more tutorial blocks failed to type-check." >&2
  echo "Fix the markdown in $MD or annotate the block with <!-- no-compile --> if intentional." >&2
  exit 1
fi

echo ""
echo "All tutorial blocks type-check cleanly."
