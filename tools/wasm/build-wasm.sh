#!/usr/bin/env bash
#
# tools/wasm/build-wasm.sh — Pack Sparkle into a staging directory
# consumable by xeus-lean's `-DEXTRA_WASM_DIRS=<staging>` extension
# point.  Modeled on
#   https://github.com/Verilean/xeus-lean/blob/main/tests/fixtures/mock-extra/build-wasm.sh
#
# Produces inside <staging-dir>:
#   <staging>/Sparkle/...                 ← olean tree from `lake build`
#   <staging>/Sparkle.olean               ← top-level umbrella olean
#   <staging>/lib/libsparkle_wasm.a       ← C externs (barrier + JIT stub)
#                                            + Lean-generated wrappers
#   <staging>/lib/sparkle_exports.txt     ← exported symbols (for emcc)
#   <staging>/xeus-lean-extra.json        ← manifest xlean's CMake reads
#   <staging>/.xeus-auto-imports          ← pre-import `Sparkle` in REPL
#
# Run from an emscripten-enabled shell (e.g. xeus-lean's
# `pixi run -e wasm-build …`) so emcc / emar / lake are on PATH.
#
# Usage:
#   tools/wasm/build-wasm.sh <staging-dir>

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "usage: $0 <staging-dir>" >&2
    exit 2
fi

STAGING="$(realpath "$1")"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

mkdir -p "$STAGING/lib"

echo "[sparkle-wasm] staging dir : $STAGING"
echo "[sparkle-wasm] repo root   : $REPO_ROOT"

# ---------------------------------------------------------------------
# 1. Build the Sparkle olean tree.  We only need the `Sparkle.*`
#    umbrella — the IP/* libraries are tutorial-out-of-scope and
#    would inflate the download size unnecessarily.
# ---------------------------------------------------------------------
pushd "$REPO_ROOT" >/dev/null
echo "[sparkle-wasm] running 'lake build Sparkle' …"
lake build Sparkle
OLEAN_SRC="$REPO_ROOT/.lake/build/lib/lean"
if [ ! -f "$OLEAN_SRC/Sparkle.olean" ]; then
    echo "[sparkle-wasm] ERROR: lake didn't produce $OLEAN_SRC/Sparkle.olean" >&2
    exit 1
fi
popd >/dev/null

# Copy oleans into the staging dir.  Umbrella file at
# <staging>/Sparkle.olean, per-module tree at <staging>/Sparkle/…
# Layout matches xlean's CMake expectations when `olean_root` =
# "Sparkle" in the manifest.
cp "$OLEAN_SRC/Sparkle.olean" "$STAGING/Sparkle.olean"
if [ -d "$OLEAN_SRC/Sparkle" ]; then
    cp -r "$OLEAN_SRC/Sparkle" "$STAGING/Sparkle"
else
    mkdir -p "$STAGING/Sparkle"
fi
# Sibling files lake sometimes produces (depending on toolchain).
for ext in olean.private olean.server ir ilean; do
    if [ -f "$OLEAN_SRC/Sparkle.$ext" ]; then
        cp "$OLEAN_SRC/Sparkle.$ext" "$STAGING/"
    fi
done

# ---------------------------------------------------------------------
# 1b. Olean version-header reconciliation.
#
# The `.olean` header carries a fixed-width version string (offsets
# [7,40); githash follows at offset 40).  Lean's loader compares that
# string EXACTLY.  xeus-lean's WASM kernel is a *source* build of
# lean4 → its stdlib oleans are tagged e.g. "4.28.0-pre", while the
# repo's oleans (built with the release toolchain at the SAME commit)
# are tagged "4.28.0".  Same commit ⇒ byte-identical olean format, but
# the differing version string makes the WASM kernel REJECT our oleans
# — `import Sparkle` then "loads" nothing and `Sparkle.Core.Domain`
# shows up as an unknown namespace in the lab.
#
# Fix: rewrite our staged oleans' version field to the WASM kernel's
# version string.  We read the target string from a WASM stdlib olean
# (WASM_LEAN_OLEAN, or a probe of common locations); this is only sound
# when the githashes match, which we assert.  If we can't find a
# reference olean we leave the headers untouched (no-op, no regression).
WASM_REF_OLEAN="${WASM_LEAN_OLEAN:-}"
if [ -z "$WASM_REF_OLEAN" ]; then
    for cand in \
        /opt/xeus-lean/wasm-build/test_olean_staging/lib/lean/Init.olean \
        /opt/xeus-lean/.pixi/envs/wasm-host/lib/lean/Init.olean; do
        [ -f "$cand" ] && WASM_REF_OLEAN="$cand" && break
    done
fi
if [ -n "$WASM_REF_OLEAN" ] && [ -f "$WASM_REF_OLEAN" ]; then
    echo "[sparkle-wasm] reconciling olean version headers against: $WASM_REF_OLEAN"
    python3 - "$WASM_REF_OLEAN" "$STAGING" <<'PYEOF'
import sys, os, pathlib
ref, staging = sys.argv[1], sys.argv[2]
MAGIC = b"olean"
VER_OFF, GIT_OFF = 7, 40   # version field [7,40); githash at 40

def read_hdr(p):
    with open(p, "rb") as f:
        h = f.read(64)
    if h[:5] != MAGIC:
        return None
    ver = h[VER_OFF:h.index(b"\x00", VER_OFF)]
    git = h[GIT_OFF:GIT_OFF+8]
    return ver, git

r = read_hdr(ref)
if r is None:
    print(f"[sparkle-wasm] WARN: reference {ref} is not an olean; skipping", file=sys.stderr)
    sys.exit(0)
tgt_ver, ref_git = r
if len(tgt_ver) > (GIT_OFF - VER_OFF):
    print("[sparkle-wasm] WARN: target version too long for header field; skipping", file=sys.stderr)
    sys.exit(0)

patched = skipped = 0
for p in pathlib.Path(staging).rglob("*.olean"):
    with open(p, "rb") as f:
        data = bytearray(f.read())
    if data[:5] != MAGIC:
        continue
    cur_ver = bytes(data[VER_OFF:data.index(b"\x00", VER_OFF)])
    cur_git = bytes(data[GIT_OFF:GIT_OFF+8])
    if cur_ver == tgt_ver:
        continue
    # Only safe when the underlying Lean commit matches.
    if cur_git != ref_git:
        print(f"[sparkle-wasm] WARN: githash mismatch on {p.name} "
              f"({cur_git!r} vs ref {ref_git!r}); NOT patching", file=sys.stderr)
        skipped += 1
        continue
    for i in range(VER_OFF, GIT_OFF):
        data[i] = 0
    data[VER_OFF:VER_OFF+len(tgt_ver)] = tgt_ver
    with open(p, "wb") as f:
        f.write(data)
    patched += 1
print(f"[sparkle-wasm] olean version reconcile: {patched} patched "
      f"-> {tgt_ver.decode()}, {skipped} skipped")
if skipped:
    sys.exit(1)   # githash mismatch is a real problem — fail loudly
PYEOF
else
    echo "[sparkle-wasm] WARN: no WASM reference olean found; leaving version headers as-is"
fi

# ---------------------------------------------------------------------
# 2. Compile the WASM static library.  Three pieces:
#
#   (a) sparkle_barrier.c — pure C, WASM-safe.  Implements
#       `sparkle_cache_get` / `sparkle_eval_at` (the Signal-evaluator
#       memoization barriers); used by every Sparkle program.
#
#   (b) sparkle_jit_wasm_stub.c — replaces sparkle_jit.c for WASM.
#       Native JIT uses dlopen, which doesn't exist in the WASM
#       sandbox.  The stub satisfies every `@[extern "sparkle_jit_*"]`
#       at link time and throws a clear IO error at run time.
#
#   (c) the Lean-generated `.c` wrappers — Lake produces these in
#       `.lake/build/ir/Sparkle/Core/JIT.c` (and friends) for every
#       `@[extern]` declaration.  The Lean interpreter resolves the
#       boxed wrappers (`lp_…___boxed`) via dlsym, so they MUST be
#       archived alongside the hand-written C — the mock-extra
#       fixture in xeus-lean spells out exactly why.
# ---------------------------------------------------------------------
LEAN_PREFIX="$(lean --print-prefix)"
LEAN_INCLUDE="$LEAN_PREFIX/include"
if [ ! -d "$LEAN_INCLUDE" ]; then
    echo "[sparkle-wasm] ERROR: lean include dir not found: $LEAN_INCLUDE" >&2
    exit 1
fi

# Same `LEAN_MIMALLOC` workaround as the mock-extra fixture — without
# this, generated wrappers inline mimalloc inlines from `lean/config.h`
# and trip "memory access out of bounds" inside emscripten's free().
OVERRIDE_H="$STAGING/lib/sparkle_no_mimalloc.h"
cat > "$OVERRIDE_H" <<'EOF'
#undef LEAN_MIMALLOC
EOF

# 2a. sparkle_barrier.c
# Apply the same LEAN_MIMALLOC override here too: even hand-written
# C that only `#include <lean/lean.h>` indirectly pulls in the
# mimalloc inline expansions through `lean/config.h`, leaving the
# WASM link with unresolved `mi_malloc_small`/`mi_free`/etc.  The
# override switches the allocator pragma off before lean.h is
# evaluated, so the file falls through to libc malloc/free.
OBJ_BARRIER="$STAGING/lib/sparkle_barrier.o"
emcc -O2 -sMEMORY64 -fPIC -w \
     -I"$LEAN_INCLUDE" \
     -include lean/config.h \
     -include "$OVERRIDE_H" \
     -c "$REPO_ROOT/c_src/sparkle_barrier.c" \
     -o "$OBJ_BARRIER"

# 2b. sparkle_jit_wasm_stub.c (replaces sparkle_jit.c for WASM)
OBJ_JIT_STUB="$STAGING/lib/sparkle_jit_wasm_stub.o"
emcc -O2 -sMEMORY64 -fPIC -w \
     -I"$LEAN_INCLUDE" \
     -include lean/config.h \
     -include "$OVERRIDE_H" \
     -c "$REPO_ROOT/c_src/sparkle_jit_wasm_stub.c" \
     -o "$OBJ_JIT_STUB"

# 2c. Lake-generated `.c` wrappers for every `@[extern]` declaration.
# These live under `.lake/build/ir/<module-path>.c`.  We find every
# .c there and compile it with the LEAN_MIMALLOC override.
IR_ROOT="$REPO_ROOT/.lake/build/ir"
declare -a WRAPPER_OBJS=()
WRAPPER_COUNT=0
if [ -d "$IR_ROOT/Sparkle" ]; then
    while IFS= read -r -d '' src; do
        rel="${src#$IR_ROOT/}"
        # Strip ".c" → "obj name".  Underscore-escape the slashes so
        # we keep a flat staging/lib/.
        obj_name="$(echo "${rel%.c}" | tr '/' '_').o"
        obj="$STAGING/lib/$obj_name"
        emcc -O2 -sMEMORY64 -fPIC -w \
             -I"$LEAN_INCLUDE" \
             -include lean/config.h \
             -include "$OVERRIDE_H" \
             -c "$src" \
             -o "$obj"
        WRAPPER_OBJS+=("$obj")
        WRAPPER_COUNT=$((WRAPPER_COUNT + 1))
    done < <(find "$IR_ROOT/Sparkle" -name '*.c' -print0)
fi
echo "[sparkle-wasm] compiled $WRAPPER_COUNT Lean-generated wrappers"

rm -f "$OVERRIDE_H"

# Archive everything together.
emar rcs "$STAGING/lib/libsparkle_wasm.a" \
     "$OBJ_BARRIER" "$OBJ_JIT_STUB" "${WRAPPER_OBJS[@]}"
rm -f "$OBJ_BARRIER" "$OBJ_JIT_STUB" "${WRAPPER_OBJS[@]}"

# ---------------------------------------------------------------------
# 3. Exports list.  One C symbol per line, with the leading
#    underscore emscripten expects on `-sEXPORTED_FUNCTIONS`.
#
# Sources:
#   - sparkle_cache_get / sparkle_eval_at  ← from sparkle_barrier.c
#   - every sparkle_jit_*                  ← from sparkle_jit_wasm_stub.c
#   - every LEAN_EXPORT in the generated wrappers (boxed entry points
#     the Lean interpreter resolves via dlsym).
# ---------------------------------------------------------------------
EXPORTS="$STAGING/lib/sparkle_exports.txt"
{
    # Hand-written externs.
    echo "_sparkle_cache_get"
    echo "_sparkle_eval_at"
    # JIT stubs.
    for sym in \
        sparkle_jit_load sparkle_jit_eval sparkle_jit_tick \
        sparkle_jit_eval_tick sparkle_jit_reset sparkle_jit_destroy \
        sparkle_jit_set_input sparkle_jit_get_output sparkle_jit_get_wire \
        sparkle_jit_set_mem sparkle_jit_get_mem sparkle_jit_memset_word \
        sparkle_jit_snapshot sparkle_jit_restore sparkle_jit_free_snapshot \
        sparkle_jit_wire_name sparkle_jit_num_wires \
        sparkle_jit_set_reg sparkle_jit_get_reg \
        sparkle_jit_reg_name sparkle_jit_num_regs sparkle_jit_run_cdc
    do
        echo "_$sym"
    done
    # Pick up LEAN_EXPORTs from every generated wrapper .c.  Same
    # extractor as the mock-extra fixture uses.
    if [ -d "$IR_ROOT/Sparkle" ]; then
        find "$IR_ROOT/Sparkle" -name '*.c' -print0 \
          | xargs -0 grep -hoE 'LEAN_EXPORT[[:space:]]+[a-zA-Z_][a-zA-Z_0-9*]*[[:space:]]+[a-zA-Z_][a-zA-Z_0-9]*[[:space:]]*\(' \
          | sed -E 's/^LEAN_EXPORT[[:space:]]+[a-zA-Z_][a-zA-Z_0-9*]*[[:space:]]+([a-zA-Z_][a-zA-Z_0-9]*).*/_\1/'
    fi
} | sort -u > "$EXPORTS"

EXPORT_COUNT=$(wc -l < "$EXPORTS")
echo "[sparkle-wasm] $EXPORT_COUNT symbol(s) → $EXPORTS"

# ---------------------------------------------------------------------
# 4. xeus-lean-extra.json — the contract xlean's CMake reads.
# ---------------------------------------------------------------------
cat > "$STAGING/xeus-lean-extra.json" <<'EOF'
{
  "archive":    "lib/libsparkle_wasm.a",
  "exports":    "lib/sparkle_exports.txt",
  "olean_root": "Sparkle"
}
EOF

# ---------------------------------------------------------------------
# 5. .xeus-auto-imports — pre-load Sparkle into REPL cell 1 so users
#    don't have to write `import Sparkle` themselves at the top of
#    every notebook.
# ---------------------------------------------------------------------
cat > "$STAGING/.xeus-auto-imports" <<'EOF'
# Modules auto-imported into the xlean REPL's first cell.
# One module name per line; lines starting with `#` are comments.
Sparkle
EOF

echo "[sparkle-wasm] DONE.  Hand this to xlean's WASM build via:"
echo "                -DEXTRA_WASM_DIRS=\"$STAGING\""
