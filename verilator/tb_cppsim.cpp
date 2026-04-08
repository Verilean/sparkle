// ============================================================================
// CppSim Testbench for Sparkle RV32I SoC
//
// Pure C++ simulation — no Verilator dependency.
// Loads firmware hex file, runs simulation, monitors UART output.
// Usage: ./cppsim_soc [firmware.hex] [max_cycles]
// ============================================================================

#include "generated_soc_cppsim.h"

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>
#include <chrono>
#include <memory>

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
    std::string hex_path = "../firmware/firmware.hex";
    uint64_t max_cycles = 100000;

    // Parse arguments
    if (argc > 1) hex_path = argv[1];
    if (argc > 2) max_cycles = strtoull(argv[2], nullptr, 10);

    // Load firmware
    auto firmware = load_hex(hex_path);
    printf("CppSim: Loading firmware from %s...\n", hex_path.c_str());
    printf("CppSim: Loaded %zu words\n", firmware.size());

    // Instantiate SoC on heap (large memory arrays exceed stack size)
    auto soc_ptr = std::make_unique<Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth>();
    auto& soc = *soc_ptr;

    // Load firmware directly into IMEM array (no CPU cycles consumed)
    for (size_t i = 0; i < firmware.size() && i < (1 << 12); i++) {
        soc._gen_imem_rdata[i] = firmware[i];
    }
    soc._gen_imem_wr_en = 0;
    soc._gen_imem_wr_addr = 0;
    soc._gen_imem_wr_data = 0;
    soc._gen_dmem_wr_en = 0;
    soc._gen_dmem_wr_addr = 0;
    soc._gen_dmem_wr_data = 0;

    // Simulation
    printf("CppSim: Running for %llu cycles...\n", (unsigned long long)max_cycles);

    uint32_t prev_pc = 0xFFFFFFFF;
    int halt_count = 0;
    std::vector<uint32_t> uart_log;

    auto t_start = std::chrono::high_resolution_clock::now();

    uint64_t actual_cycles = 0;
    for (uint64_t cycle = 0; cycle < max_cycles; cycle++) {
        soc.eval();
        actual_cycles = cycle + 1;

        // Read outputs
        uint32_t pc = soc._gen_pcReg;
        uint32_t uart_valid = soc._gen_uartValidBV;
        uint32_t uart_data = soc._gen_prevStoreData;

        // PC trace (first few cycles + periodic)
        if (cycle < 5 || cycle % 100000 == 0) {
            printf("cycle %llu: PC = 0x%08x\n", (unsigned long long)cycle, pc);
        }

        // UART output
        if (uart_valid) {
            uart_log.push_back(uart_data);
            printf("  UART[%zu]: 0x%08x\n", uart_log.size(), uart_data);

            // Stop after pass/fail marker
            if (uart_data == 0xCAFE0000u || uart_data == 0xDEADDEADu) {
                // Drain pipeline
                for (int drain = 0; drain < 20; drain++) {
                    soc.eval();
                    soc.tick();
                    if (soc._gen_uartValidBV) {
                        uart_log.push_back(soc._gen_prevStoreData);
                        printf("  UART[%zu]: 0x%08x\n", uart_log.size(), soc._gen_prevStoreData);
                    }
                }
                printf("Simulation complete at cycle %llu\n", (unsigned long long)cycle);
                break;
            }
        }

        // Halt detection (self-loop)
        if (pc == prev_pc) {
            halt_count++;
            if (halt_count >= 50) {
                printf("\nHalt detected at cycle %llu: PC = 0x%08x\n",
                       (unsigned long long)cycle, pc);
                break;
            }
        } else {
            halt_count = 0;
        }
        prev_pc = pc;

        soc.tick();
    }

    auto t_end = std::chrono::high_resolution_clock::now();
    double elapsed_ms = std::chrono::duration<double, std::milli>(t_end - t_start).count();

    // Summary
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

    // Timing
    printf("\nCppSim: %llu cycles in %.1f ms (%.0f cycles/sec)\n",
           (unsigned long long)actual_cycles, elapsed_ms,
           (double)actual_cycles / (elapsed_ms / 1000.0));

    return found_pass ? 0 : 1;
}
