#!/usr/bin/env bash
# build-from-md.sh — convert Markdown chapter sources to .lean (for
# `lake build`) and .ipynb (for JupyterLab) using xlean-convert.
#
# Source of truth: docs/tutorial/md/Ch*.md
# Generated (gitignored):
#   docs/tutorial/Notebooks/Gen/Ch*.lean              (lake build target)
#   docs/tutorial/Notebooks/Gen/notebooks/ch*.ipynb   (JupyterLab)
#
# Requires the `xlean-convert` binary from xeus-lean (merged in
# upstream main):
#
#   git clone https://github.com/Verilean/xeus-lean
#   cd xeus-lean && lake build xlean-convert
#   export XLEAN_CONVERT=$PWD/.lake/build/bin/xlean-convert
#
# (Or in the bundled tutorial Docker image, `xlean-convert` is on
# the PATH; no env var needed.)
#
# Optionally run `jupyter nbconvert --execute` afterwards to fill in
# output cells (requires the xeus-lean kernel installed).
set -euo pipefail

XLEAN_CONVERT="${XLEAN_CONVERT:-xlean-convert}"
SRC_DIR="docs/tutorial/md"
LEAN_OUT_DIR="docs/tutorial/Notebooks/Gen"
IPYNB_OUT_DIR="docs/tutorial/Notebooks/Gen/notebooks"

if ! command -v "${XLEAN_CONVERT}" >/dev/null 2>&1; then
    echo "xlean-convert not on PATH (and \$XLEAN_CONVERT not set)" >&2
    echo "Build it from xeus-lean (see https://github.com/Verilean/xeus-lean)" >&2
    exit 1
fi

mkdir -p "${LEAN_OUT_DIR}" "${IPYNB_OUT_DIR}"

shopt -s nullglob
chapters=( "${SRC_DIR}"/Ch*.md )

if [ "${#chapters[@]}" -eq 0 ]; then
    echo "no Markdown chapters under ${SRC_DIR}" >&2
    exit 1
fi

# Map "Ch00_Setup.md" → ipynb "ch00-setup.ipynb"
nb_name() {
    basename "$1" .md \
        | tr '[:upper:]' '[:lower:]' \
        | tr '_' '-'
}

for src in "${chapters[@]}"; do
    base="$(basename "$src" .md)"
    lean_out="${LEAN_OUT_DIR}/${base}.lean"
    ipynb_out="${IPYNB_OUT_DIR}/$(nb_name "$src").ipynb"

    echo ">> ${src} → ${lean_out}"
    "${XLEAN_CONVERT}" --to lean -o "${lean_out}" "${src}"

    echo "             → ${ipynb_out}"
    "${XLEAN_CONVERT}" --to ipynb -o "${ipynb_out}" "${src}"
done

echo
echo "Done.  ${#chapters[@]} chapters converted."
echo "Run \`lake build TutorialNotebooks\` to typecheck the .lean output."
