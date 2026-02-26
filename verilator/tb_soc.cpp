// ============================================================================
// Verilator Testbench for Sparkle RV32I SoC
//
// Loads firmware hex file, runs simulation, monitors UART output.
// Usage: ./Vrv32i_soc [firmware.hex] [max_cycles]
// ============================================================================

#include "Vrv32i_soc.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>

// Load hex file (one 32-bit word per line, hex format)
static std::vector<uint32_t> load_hex(const std::string& path) {
    std::vector<uint32_t> words;
    std::ifstream f(path);
    if (!f.is_open()) {
        fprintf(stderr, "Error: cannot open %s\n", path.c_str());
        return words;
    }
    std::string line;
    while (std::getline(f, line)) {
        if (line.empty() || line[0] == '/' || line[0] == '#' || line[0] == '@') continue;
        uint32_t val = (uint32_t)strtoul(line.c_str(), nullptr, 16);
        words.push_back(val);
    }
    return words;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    std::string hex_path = "../firmware/firmware.hex";
    uint64_t max_cycles = 100000;

    if (argc > 1) hex_path = argv[1];
    if (argc > 2) max_cycles = strtoull(argv[2], nullptr, 10);

    // Load firmware
    auto firmware = load_hex(hex_path);
    printf("Loading firmware from %s...\n", hex_path.c_str());
    printf("Loaded %zu words\n", firmware.size());

    // Instantiate DUT
    Vrv32i_soc* dut = new Vrv32i_soc;

    // VCD tracing (optional, enabled by default)
    VerilatedVcdC* vcd = nullptr;
    Verilated::traceEverOn(true);
    vcd = new VerilatedVcdC;
    dut->trace(vcd, 99);
    vcd->open("sim_trace.vcd");

    // Initialize firmware into IMEM via backdoor
    // Write firmware words during reset
    dut->clk = 0;
    dut->rst = 1;
    dut->imem_wr_en = 0;
    dut->imem_wr_addr = 0;
    dut->imem_wr_data = 0;
    dut->uart_rx_valid = 0;
    dut->uart_rx_data = 0;
    dut->eval();

    // Load firmware via IMEM write port during reset
    for (size_t i = 0; i < firmware.size() && i < (1 << 12); i++) {
        dut->imem_wr_en = 1;
        dut->imem_wr_addr = (uint16_t)i;
        dut->imem_wr_data = firmware[i];
        dut->clk = 0; dut->eval();
        if (vcd) vcd->dump((uint64_t)(i * 2));
        dut->clk = 1; dut->eval();
        if (vcd) vcd->dump((uint64_t)(i * 2 + 1));
    }
    dut->imem_wr_en = 0;

    // Release reset
    dut->rst = 0;

    // Simulation
    printf("Running Verilator simulation for %llu cycles...\n",
           (unsigned long long)max_cycles);

    uint64_t time_ps = firmware.size() * 2 + 10;
    uint32_t prev_pc = 0xFFFFFFFF;
    int halt_count = 0;
    std::vector<uint32_t> uart_log;

    for (uint64_t cycle = 0; cycle < max_cycles; cycle++) {
        // Rising edge
        dut->clk = 1;
        dut->eval();
        time_ps++;
        if (vcd) vcd->dump(time_ps);

        // Sample outputs on rising edge
        uint32_t pc = dut->pc_out;
        bool uart_valid = dut->uart_tx_valid;
        uint32_t uart_data = dut->uart_tx_data;

        // Print PC for first few cycles and periodically
        if (cycle < 5 || cycle % 10000 == 0) {
            printf("cycle %llu: PC = 0x%08x\n",
                   (unsigned long long)cycle, pc);
        }

        // UART output
        if (uart_valid) {
            uart_log.push_back(uart_data);
            printf("  UART[%zu]: 0x%08x\n", uart_log.size(), uart_data);
            // Stop shortly after pass/fail marker
            if (uart_data == 0xCAFE0000u || uart_data == 0xDEADDEADu) {
                // Run a few more cycles to drain the pipeline
                for (int drain = 0; drain < 20; drain++) {
                    dut->clk = 0; dut->eval(); time_ps++;
                    dut->clk = 1; dut->eval(); time_ps++;
                    if (dut->uart_tx_valid) {
                        uart_log.push_back(dut->uart_tx_data);
                        printf("  UART[%zu]: 0x%08x\n", uart_log.size(), dut->uart_tx_data);
                    }
                }
                printf("Simulation complete at cycle %llu\n",
                       (unsigned long long)cycle);
                break;
            }
        }

        // Halt detection (self-loop)
        if (pc == prev_pc) {
            halt_count++;
            if (halt_count >= 10) {
                printf("Halt detected at cycle %llu: PC = 0x%08x\n",
                       (unsigned long long)cycle, pc);
                break;
            }
        } else {
            halt_count = 0;
        }
        prev_pc = pc;

        // Falling edge
        dut->clk = 0;
        dut->eval();
        time_ps++;
        if (vcd) vcd->dump(time_ps);
    }

    // Print UART summary
    printf("\n=== UART Output (%zu words) ===\n", uart_log.size());
    for (size_t i = 0; i < uart_log.size(); i++) {
        printf("  0x%08x\n", uart_log[i]);
    }

    // Check pass/fail markers
    bool found_pass = false, found_fail = false;
    for (auto v : uart_log) {
        if (v == 0xCAFE0000u) found_pass = true;
        if (v == 0xDEADDEADu) found_fail = true;
    }
    if (found_pass) printf("\n*** ALL TESTS PASSED ***\n");
    else if (found_fail) printf("\n*** SOME TESTS FAILED ***\n");
    else printf("\n*** No pass/fail marker found ***\n");

    // Cleanup
    if (vcd) { vcd->close(); delete vcd; }
    delete dut;
    return found_pass ? 0 : 1;
}
