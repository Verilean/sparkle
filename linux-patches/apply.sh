#!/usr/bin/env bash
#
# Patch the Sparkle BitNet driver into a Linux source tree.
#
# Idempotent: safe to re-run on the same tree. Only writes files that
# are missing or stale.
#
# Usage:
#   bash linux-patches/apply.sh [LINUX_DIR]
#
# Defaults to LINUX_DIR=/tmp/linux (the path setup.sh checks out into).

set -euo pipefail

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PATCH_DIR="${REPO_DIR}/linux-patches"
LINUX_DIR="${1:-/tmp/linux}"

if [ ! -d "${LINUX_DIR}" ]; then
    echo "ERROR: Linux source tree not found at ${LINUX_DIR}" >&2
    echo "Run firmware/opensbi/setup.sh first to clone the kernel." >&2
    exit 1
fi

DRIVERS_DIR="${LINUX_DIR}/drivers/misc"
UAPI_DIR="${LINUX_DIR}/include/uapi/linux"

echo "Patching Sparkle BitNet driver into ${LINUX_DIR}"

# 1. Driver source.
install -m 0644 "${PATCH_DIR}/sparkle-bitnet.c" "${DRIVERS_DIR}/sparkle-bitnet.c"

# 2. UAPI header (so userspace + driver agree on ioctl numbers).
install -m 0644 "${PATCH_DIR}/sparkle-bitnet.h" "${UAPI_DIR}/sparkle-bitnet.h"

# 3. Kconfig: append our entry once, just before the closing `endmenu`
# of drivers/misc/Kconfig.
KCONFIG="${DRIVERS_DIR}/Kconfig"
if ! grep -q '^config SPARKLE_BITNET$' "${KCONFIG}"; then
    awk -v frag="${PATCH_DIR}/Kconfig.fragment" '
        BEGIN { while ((getline line < frag) > 0) extra = extra line "\n"; close(frag) }
        /^endmenu/ && !done { print extra; done = 1 }
        { print }
    ' "${KCONFIG}" > "${KCONFIG}.new"
    mv "${KCONFIG}.new" "${KCONFIG}"
    echo "  + added CONFIG_SPARKLE_BITNET to drivers/misc/Kconfig"
else
    echo "  = drivers/misc/Kconfig already has SPARKLE_BITNET"
fi

# 4. Makefile: register the object.
MAKEFILE="${DRIVERS_DIR}/Makefile"
if ! grep -q 'sparkle-bitnet' "${MAKEFILE}"; then
    echo 'obj-$(CONFIG_SPARKLE_BITNET)	+= sparkle-bitnet.o' >> "${MAKEFILE}"
    echo "  + added sparkle-bitnet.o to drivers/misc/Makefile"
else
    echo "  = drivers/misc/Makefile already builds sparkle-bitnet"
fi

# 5. Force the option on in the existing .config.
if [ -f "${LINUX_DIR}/.config" ]; then
    "${LINUX_DIR}/scripts/config" --file "${LINUX_DIR}/.config" \
        --enable CONFIG_SPARKLE_BITNET
    echo "  + set CONFIG_SPARKLE_BITNET=y in .config"
fi

# 6. Optional debug-trace patch (apply if present and not already applied).
DEBUG_PATCH="${PATCH_DIR}/debug-uart-trace.patch"
if [ -f "${DEBUG_PATCH}" ]; then
    if ! grep -q 'SPARKLE-DEBUG' "${LINUX_DIR}/init/main.c" 2>/dev/null; then
        if patch -d "${LINUX_DIR}" -p1 --forward --silent < "${DEBUG_PATCH}"; then
            echo "  + applied debug-uart-trace.patch"
        else
            echo "  ! debug-uart-trace.patch failed (already partially applied?)"
        fi
    else
        echo "  = debug-uart-trace.patch already applied"
    fi
fi

echo "Patched."
