#!/bin/bash
# ============================================================================
# Sparkle RV32I SoC — Unified Benchmark Script
#
# Compares Verilator, CppSim, and JIT simulation backends side-by-side.
# Runs each backend for the same number of cycles with the same firmware.
#
# Usage:
#   ./bench.sh                         # firmware.hex, 10M cycles
#   ./bench.sh 50000000                # firmware.hex, 50M cycles
#   ./bench.sh 10000000 path/to.hex    # custom firmware, 10M cycles
#
# Prerequisites:
#   make build        — Verilator binary (obj_dir/Vrv32i_soc)
#   make build-cppsim — CppSim binary (cppsim_soc)
#   make build-jit    — JIT dylib (generated_soc_jit.dylib)
#   clang++ -O2 -std=c++17 -o verilator_bench tb_verilator_bench.cpp \
#       -Iobj_dir -Lobj_dir obj_dir/*.o $(pkg-config --libs verilator)
#   clang++ -O2 -std=c++17 -o jit_bench tb_jit_bench.cpp -ldl
# ============================================================================

set -euo pipefail
cd "$(dirname "$0")"

CYCLES="${1:-10000000}"
HEX="${2:-../firmware/firmware.hex}"
DYLIB="generated_soc_jit.dylib"

echo "=========================================="
echo "  Sparkle RV32I SoC Benchmark"
echo "=========================================="
echo "  Firmware:  $HEX"
echo "  Cycles:    $CYCLES"
echo "  Date:      $(date '+%Y-%m-%d %H:%M:%S')"
echo "  Machine:   $(uname -m) / $(sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -p)"
echo "=========================================="

# --- Check prerequisites ---
MISSING=""
[ ! -f verilator_bench ] && MISSING="$MISSING verilator_bench"
[ ! -f jit_bench ]       && MISSING="$MISSING jit_bench"
[ ! -f "$DYLIB" ]        && MISSING="$MISSING $DYLIB"

if [ -n "$MISSING" ]; then
    echo ""
    echo "Building missing binaries:$MISSING"

    if [ ! -f "$DYLIB" ]; then
        echo "  -> make build-jit"
        make build-jit 2>&1 | tail -1
    fi

    if [ ! -f verilator_bench ]; then
        echo "  -> Building verilator_bench..."
        make build 2>&1 | tail -1
        clang++ -O2 -std=c++17 -o verilator_bench tb_verilator_bench.cpp \
            obj_dir/*.o \
            -Iobj_dir \
            $(pkg-config --cflags --libs verilator 2>/dev/null || echo "-I$(verilator --getenv VERILATOR_ROOT)/include -I$(verilator --getenv VERILATOR_ROOT)/include/vltstd") \
            $(verilator --getenv VERILATOR_ROOT)/include/verilated.cpp \
            $(verilator --getenv VERILATOR_ROOT)/include/verilated_vcd_c.cpp \
            $(verilator --getenv VERILATOR_ROOT)/include/verilated_threads.cpp \
            2>&1 | tail -3
    fi

    if [ ! -f jit_bench ]; then
        echo "  -> Building jit_bench..."
        clang++ -O2 -std=c++17 -o jit_bench tb_jit_bench.cpp -ldl
    fi
    echo ""
fi

# --- Run benchmarks ---

echo ""
echo ">>> Verilator (pure eval loop, no I/O) <<<"
./verilator_bench "$HEX" "$CYCLES" 2>&1

echo ""
echo ">>> JIT Benchmark (5 modes) <<<"
./jit_bench "$HEX" "$CYCLES" "$DYLIB" 2>&1

echo ""
echo "=========================================="
echo "  Benchmark Complete"
echo "=========================================="
