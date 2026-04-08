#!/usr/bin/env bash
# ============================================================================
# Sparkle Benchmark Suite
#
# Usage:
#   ./bench.sh                  # All benchmarks (10M cycles)
#   ./bench.sh litex            # LiteX 1-core only
#   ./bench.sh multicore        # 8-core parallel only
#   ./bench.sh all 50000000     # All benchmarks, 50M cycles
# ============================================================================
set -euo pipefail
cd "$(dirname "$0")/.."

MODE="${1:-all}"
CYCLES="${2:-10000000}"
CXX="${CXX:-g++}"

echo "=========================================="
echo "  Sparkle Benchmark Suite"
echo "  Mode: $MODE, Cycles: $CYCLES"
echo "=========================================="

# ---- Prerequisites ----
if [ ! -f /tmp/picorv32.v ]; then
    echo "Fetching PicoRV32..."
    curl -sL https://raw.githubusercontent.com/YosysHQ/picorv32/main/picorv32.v -o /tmp/picorv32.v
fi

# ---- Build bench tools ----
$CXX -O2 -std=c++17 -o /tmp/bench_jit bench/bench_jit.cpp -ldl 2>/dev/null
$CXX -O2 -std=c++17 -o /tmp/bench_mc bench/bench_multicore.cpp -ldl 2>/dev/null

# ---- LiteX 1-Core ----
bench_litex() {
    echo ""
    echo "--- LiteX 1-Core ---"

    # Verilator
    python3 Tests/SVParser/fixtures/gen_litex_multicore.py 1
    cat Tests/SVParser/fixtures/litex_1core.v /tmp/picorv32.v > /tmp/litex_bench.v
    cat > /tmp/tb_litex.cpp << 'EOF'
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include "Vsim_1core.h"
int main(int argc, char** argv) {
    uint64_t N = argc > 1 ? strtoull(argv[1],0,10) : 10000000;
    auto* t = new Vsim_1core;
    t->sys_clk = 0; t->serial_sink_data_0 = 0; t->serial_sink_valid_0 = 0;
    t->serial_source_ready_0 = 1; t->eval();
    auto t0 = std::chrono::high_resolution_clock::now();
    for (uint64_t c = 0; c < N; c++) { t->sys_clk = 1; t->eval(); t->sys_clk = 0; t->eval(); }
    auto t1 = std::chrono::high_resolution_clock::now();
    double ms = std::chrono::duration<double,std::milli>(t1-t0).count();
    printf("%.2f", N/ms/1000.0);
    delete t; return 0;
}
EOF
    rm -rf /tmp/litex_bench_obj
    verilator --cc --exe --build -j 0 \
        -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL \
        -Wno-CASEINCOMPLETE -Wno-UNOPTFLAT -Wno-LATCH -Wno-MULTIDRIVEN \
        -Wno-COMBDLY -Wno-PINMISSING -Wno-UNDRIVEN \
        --top-module sim_1core -CFLAGS "-O2" \
        /tmp/litex_bench.v /tmp/tb_litex.cpp --Mdir /tmp/litex_bench_obj 2>&1 | tail -1

    # JIT
    python3 bench/preprocess_litex.py
    cat > /tmp/gen_jit.lean << 'LEOF'
import Tools.SVParser
import Sparkle.Backend.CppSim
open Tools.SVParser.Lower
def main : IO Unit := do
  let src ← IO.FS.readFile "/tmp/litex_pp.v"
  let design ← IO.ofExcept (parseAndLowerFlat src)
  IO.FS.writeFile "/tmp/litex_jit.cpp" (Sparkle.Backend.CppSim.toCppSimJIT design)
LEOF
    lake env lean --run /tmp/gen_jit.lean 2>/dev/null
    $CXX -O2 -std=c++17 -shared -fPIC -o /tmp/litex_jit.so /tmp/litex_jit.cpp 2>/dev/null

    VLTR=$(/tmp/litex_bench_obj/Vsim_1core $CYCLES 2>/dev/null)
    JIT=$(/tmp/bench_jit $CYCLES /tmp/litex_jit.so)
    echo "  Verilator:    ${VLTR}M cyc/s"
    echo "  Sparkle JIT:  ${JIT}M cyc/s"
}

# ---- Multi-Core Parallel ----
bench_multicore() {
    echo ""
    echo "--- 8-Core Multi-Thread ---"

    # Hierarchical JIT
    python3 Tests/SVParser/fixtures/gen_litex_multicore.py 1
    cat > /tmp/gen_hier.lean << 'LEOF'
import Tools.SVParser
import Sparkle.Backend.CppSim
open Tools.SVParser.Lower
def main : IO Unit := do
  let s ← IO.FS.readFile "Tests/SVParser/fixtures/litex_1core.v"
  let p ← IO.FS.readFile "/tmp/picorv32.v"
  let d ← IO.ofExcept (parseAndLowerHierarchical (s ++ "\n" ++ p))
  IO.FS.writeFile "/tmp/hier_jit.cpp" (Sparkle.Backend.CppSim.toCppSimJIT d)
LEOF
    lake env lean --run /tmp/gen_hier.lean 2>/dev/null
    $CXX -O2 -std=c++17 -shared -fPIC -o /tmp/hier_jit.so /tmp/hier_jit.cpp 2>/dev/null

    # Runner
    $CXX -O2 -std=c++20 -shared -fPIC -o /tmp/mc_runner.so c_src/cdc/multicore_runner.cpp -lpthread

    # Verilator 8-core
    python3 Tests/SVParser/fixtures/gen_litex_multicore.py 8
    cat Tests/SVParser/fixtures/litex_8core.v /tmp/picorv32.v > /tmp/litex_8core.v
    cat > /tmp/tb_8core.cpp << 'EOF'
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include "Vsim_8core.h"
int main(int argc, char** argv) {
    uint64_t N = argc > 1 ? strtoull(argv[1],0,10) : 10000000;
    auto* t = new Vsim_8core;
    t->sys_clk = 0;
    t->serial_sink_data_0=0; t->serial_sink_valid_0=0; t->serial_source_ready_0=1;
    t->serial_sink_data_1=0; t->serial_sink_valid_1=0; t->serial_source_ready_1=1;
    t->serial_sink_data_2=0; t->serial_sink_valid_2=0; t->serial_source_ready_2=1;
    t->serial_sink_data_3=0; t->serial_sink_valid_3=0; t->serial_source_ready_3=1;
    t->serial_sink_data_4=0; t->serial_sink_valid_4=0; t->serial_source_ready_4=1;
    t->serial_sink_data_5=0; t->serial_sink_valid_5=0; t->serial_source_ready_5=1;
    t->serial_sink_data_6=0; t->serial_sink_valid_6=0; t->serial_source_ready_6=1;
    t->serial_sink_data_7=0; t->serial_sink_valid_7=0; t->serial_source_ready_7=1;
    t->eval();
    auto t0=std::chrono::high_resolution_clock::now();
    for(uint64_t c=0;c<N;c++){t->sys_clk=1;t->eval();t->sys_clk=0;t->eval();}
    auto t1=std::chrono::high_resolution_clock::now();
    double ms=std::chrono::duration<double,std::milli>(t1-t0).count();
    printf("%.2f", N/ms/1000.0);
    delete t; return 0;
}
EOF
    rm -rf /tmp/litex_8core_obj
    verilator --cc --exe --build -j 0 \
        -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL \
        -Wno-CASEINCOMPLETE -Wno-UNOPTFLAT -Wno-LATCH -Wno-MULTIDRIVEN \
        -Wno-COMBDLY -Wno-PINMISSING -Wno-UNDRIVEN \
        --top-module sim_8core -CFLAGS "-O2" \
        /tmp/litex_8core.v /tmp/tb_8core.cpp --Mdir /tmp/litex_8core_obj 2>&1 | tail -1

    echo ""
    /tmp/bench_mc $CYCLES /tmp/hier_jit.so /tmp/mc_runner.so
    echo "Verilator 8: $(/tmp/litex_8core_obj/Vsim_8core $CYCLES 2>/dev/null)M cyc/s"
}

# ---- Main ----
case "$MODE" in
    litex)     bench_litex ;;
    multicore) bench_multicore ;;
    all)       bench_litex; bench_multicore ;;
    *)         echo "Usage: $0 {litex|multicore|all} [cycles]" ;;
esac

echo ""
echo "=========================================="
echo "  Benchmark Complete"
echo "=========================================="
