// Verilator side of bench/gate/run.sh (top module `sim`, the same RTL the
// JIT is generated from).  The ROM comes from `sim_rom.init` in the
// working directory through the design's own $readmemh.
//   Vsim <cycles> [trace]
// Outputs are sampled BEFORE the clock edge of cycle c, which is what
// the JIT's get_output returns after its eval_tick of cycle c.
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include "Vsim.h"

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s <cycles> [trace]\n", argv[0]); return 2; }
    uint64_t n = strtoull(argv[1], 0, 10);
    auto* top = new Vsim;
    top->serial_sink_data = 0; top->serial_sink_valid = 0;
    top->serial_source_ready = 1;
    top->sys_clk = 0; top->eval();
    if (argc > 2 && !strcmp(argv[2], "trace")) {
        for (uint64_t c = 0; c < n; c++) {
            if (top->serial_source_valid)
                printf("%llu %02x\n", (unsigned long long)c, (unsigned)top->serial_source_data);
            top->sys_clk = 1; top->eval();
            top->sys_clk = 0; top->eval();
        }
    } else {
        for (uint64_t c = 0; c < n; c++) {
            top->sys_clk = 1; top->eval();
            top->sys_clk = 0; top->eval();
        }
    }
    delete top;
    return 0;
}
