#!/usr/bin/env bash
# setup.sh — Build OpenSBI fw_jump.bin + Linux kernel Image for Sparkle SoC
#
# IMPORTANT: The Sparkle SoC is rv32ima (NO compressed instruction extension).
# Both OpenSBI and Linux must be built WITHOUT the C extension.
#
# Prerequisites:
#   OpenSBI: riscv64-elf-gcc, dtc
#   Linux:   Docker (builds in container to avoid macOS host tool issues)
#
# Usage:
#   cd firmware/opensbi && bash setup.sh
#
# Outputs:
#   /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin
#   /tmp/linux/arch/riscv/boot/Image

set -euo pipefail

CROSS_COMPILE="${CROSS_COMPILE:-riscv64-elf-}"
NPROC=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Use gmake if available (macOS ships GNU Make 3.81, Linux 6.x needs >= 3.82)
if command -v gmake &>/dev/null; then
    MAKE=gmake
else
    MAKE=make
fi

OPENSBI_DIR="/tmp/opensbi"
LINUX_DIR="/tmp/linux"

OPENSBI_BIN="${OPENSBI_DIR}/build/platform/generic/firmware/fw_jump.bin"
LINUX_IMAGE="${LINUX_DIR}/arch/riscv/boot/Image"

# ─── GCC 15+ / C23 compatibility patch for OpenSBI v0.9 ─────────
# GCC 15 defaults to -std=gnu23 where `bool` is a keyword.
# OpenSBI v0.9 has `typedef int bool;` which fails. Patch it.
patch_opensbi_for_gcc15() {
    local types_h="${OPENSBI_DIR}/include/sbi/sbi_types.h"
    if grep -q 'typedef int.*bool;' "${types_h}" 2>/dev/null; then
        echo "Patching sbi_types.h for GCC 15 C23 compatibility..."
        python3 -c "
import re
with open('${types_h}') as f:
    content = f.read()
content = content.replace('typedef int\t\t\tbool;', '#include <stdbool.h>')
content = re.sub(r'#define true\s+TRUE\n', '', content)
content = re.sub(r'#define false\s+FALSE\n', '', content)
with open('${types_h}', 'w') as f:
    f.write(content)
"
    fi
}

# ─── OpenSBI v0.9 ────────────────────────────────────────────────
echo "=== OpenSBI v0.9 (rv32ima, no C extension) ==="
if [ -f "${OPENSBI_BIN}" ]; then
    echo "Already built: ${OPENSBI_BIN}"
else
    if [ ! -f "${OPENSBI_DIR}/Makefile" ]; then
        echo "Cloning OpenSBI v0.9..."
        rm -rf "${OPENSBI_DIR}"
        git clone --depth 1 --branch v0.9 \
            https://github.com/riscv-software-src/opensbi.git "${OPENSBI_DIR}"
    fi
    patch_opensbi_for_gcc15
    echo "Building OpenSBI (CROSS_COMPILE=${CROSS_COMPILE})..."
    cd "${OPENSBI_DIR}"

    # Detect rv32im libgcc path for GCC 15 multilib (no rv32ima variant exists)
    LIBGCC_DIR="$(dirname "$(${CROSS_COMPILE}gcc -march=rv32im -mabi=ilp32 -print-libgcc-file-name)")"

    # Build with rv32ima (no C extension) + zicsr/zifencei for GCC 15 assembler
    # Link against rv32im libgcc since no rv32ima multilib exists
    ${MAKE} CROSS_COMPILE="${CROSS_COMPILE}" PLATFORM=generic \
        PLATFORM_RISCV_XLEN=32 PLATFORM_RISCV_ISA=rv32ima_zicsr_zifencei \
        FW_JUMP_ADDR=0x80400000 FW_JUMP_FDT_ADDR=0x80F00000 \
        ELFFLAGS="-Wl,--build-id=none -N -static-libgcc -L${LIBGCC_DIR} -lgcc" \
        -j"${NPROC}"
    echo "Built: ${OPENSBI_BIN}"
fi

# ─── Linux 6.6 ───────────────────────────────────────────────────
# Linux kernel host tools require Linux-specific headers (elf.h, uuid_t),
# so we build inside a Docker container on macOS.
#
# CONFIG_RISCV_ISA_C is disabled to match the rv32ima SoC (no compressed).
# Large subsystems (NET, BLOCK, etc.) are disabled to fit in 32MB DRAM.
LINUX_CONFIG_CMDS="
    scripts/config --enable CONFIG_SERIAL_8250
    scripts/config --enable CONFIG_SERIAL_8250_CONSOLE
    scripts/config --enable CONFIG_SERIAL_EARLYCON
    scripts/config --enable CONFIG_HVC_RISCV_SBI
    scripts/config --enable CONFIG_RISCV_SBI_V01
    scripts/config --enable CONFIG_RISCV_TIMER
    scripts/config --disable CONFIG_RISCV_ISA_C
    scripts/config --disable CONFIG_NETWORK
    scripts/config --disable CONFIG_NET
    scripts/config --disable CONFIG_SOUND
    scripts/config --disable CONFIG_USB_SUPPORT
    scripts/config --disable CONFIG_INPUT
    scripts/config --disable CONFIG_HW_RANDOM
    scripts/config --disable CONFIG_DRM
    scripts/config --disable CONFIG_FB
    scripts/config --disable CONFIG_CRYPTO
    scripts/config --disable CONFIG_SECURITY
    scripts/config --disable CONFIG_DEBUG_INFO
    scripts/config --disable CONFIG_DEBUG_INFO_DWARF_TOOLCHAIN_DEFAULT
    scripts/config --disable CONFIG_MODULES
    scripts/config --disable CONFIG_BLOCK
"

echo ""
echo "=== Linux v6.6 (rv32ima, no C extension, minimal config) ==="
if [ -f "${LINUX_IMAGE}" ]; then
    echo "Already built: ${LINUX_IMAGE}"
else
    if [ ! -f "${LINUX_DIR}/Makefile" ]; then
        echo "Cloning Linux v6.6 (depth=1, may take a few minutes)..."
        rm -rf "${LINUX_DIR}"
        git clone --depth 1 --branch v6.6 \
            https://github.com/torvalds/linux.git "${LINUX_DIR}"
    fi

    if [[ "$(uname)" == "Darwin" ]]; then
        echo "Building Linux in Docker (macOS detected)..."
        if ! command -v docker &>/dev/null; then
            echo "ERROR: Docker is required to build Linux on macOS"
            echo "Install Docker Desktop: https://www.docker.com/products/docker-desktop/"
            exit 1
        fi
        docker run --rm -v "${LINUX_DIR}:${LINUX_DIR}" -w "${LINUX_DIR}" debian:bookworm bash -c "
            apt-get update -qq && apt-get install -y -qq gcc-riscv64-linux-gnu make bc flex bison libssl-dev >/dev/null 2>&1
            make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- mrproper
            make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- rv32_defconfig
            ${LINUX_CONFIG_CMDS}
            make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- olddefconfig
            make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- -j\$(nproc) Image
        "
    else
        echo "Configuring Linux (rv32_defconfig)..."
        cd "${LINUX_DIR}"
        ${MAKE} ARCH=riscv CROSS_COMPILE="${CROSS_COMPILE}" mrproper
        ${MAKE} ARCH=riscv CROSS_COMPILE="${CROSS_COMPILE}" rv32_defconfig
        eval "${LINUX_CONFIG_CMDS}"
        ${MAKE} ARCH=riscv CROSS_COMPILE="${CROSS_COMPILE}" olddefconfig
        echo "Building Linux Image..."
        ${MAKE} ARCH=riscv CROSS_COMPILE="${CROSS_COMPILE}" -j"${NPROC}" Image
    fi
    echo "Built: ${LINUX_IMAGE}"
fi

# ─── Summary ─────────────────────────────────────────────────────
echo ""
echo "=== Build Complete ==="
echo "  OpenSBI: ${OPENSBI_BIN}"
echo "  Linux:   ${LINUX_IMAGE}"
echo ""
echo "Run the JIT Linux boot test:"
echo "  lake exe rv32-jit-linux-boot-test"
