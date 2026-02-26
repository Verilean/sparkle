// ============================================================================
// Verilator Testbench for Sparkle RV32I SoC
//
// Loads firmware hex file, runs simulation, monitors UART output.
// Usage: ./Vrv32i_soc [firmware.hex] [max_cycles] [--dram <binary>] [--dtb <dtb_file>] [--payload <binary>]
// ============================================================================

#include "Vrv32i_soc.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
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

// Load raw binary file into byte vector
static std::vector<uint8_t> load_binary(const std::string& path) {
    std::vector<uint8_t> data;
    std::ifstream f(path, std::ios::binary);
    if (!f.is_open()) {
        fprintf(stderr, "Error: cannot open binary %s\n", path.c_str());
        return data;
    }
    f.seekg(0, std::ios::end);
    size_t sz = f.tellg();
    f.seekg(0, std::ios::beg);
    data.resize(sz);
    f.read(reinterpret_cast<char*>(data.data()), sz);
    return data;
}

// Load binary data into DMEM via write port during reset
// base_addr is the physical byte address (e.g. 0x80000000)
static void load_dram(Vrv32i_soc* dut, VerilatedVcdC* vcd,
                      const uint8_t* data, size_t len,
                      uint32_t base_addr, uint64_t& time_ps) {
    // Convert base_addr to word address: addr[24:2]
    // Physical address 0x80000000 maps to DMEM word address 0
    uint32_t word_addr_base = (base_addr & 0x01FFFFFF) >> 2;
    size_t num_words = (len + 3) / 4;

    printf("Loading %zu bytes (%zu words) to DRAM at 0x%08x (word addr 0x%06x)\n",
           len, num_words, base_addr, word_addr_base);

    for (size_t i = 0; i < num_words; i++) {
        uint32_t word = 0;
        for (int b = 0; b < 4; b++) {
            size_t idx = i * 4 + b;
            if (idx < len) word |= ((uint32_t)data[idx]) << (b * 8);
        }
        dut->dmem_wr_en = 1;
        dut->dmem_wr_addr = word_addr_base + i;
        dut->dmem_wr_data = word;

        dut->clk = 0; dut->eval();
        if (vcd) vcd->dump(time_ps++);
        dut->clk = 1; dut->eval();
        if (vcd) vcd->dump(time_ps++);
    }
    dut->dmem_wr_en = 0;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    std::string hex_path = "../firmware/firmware.hex";
    uint64_t max_cycles = 100000;
    std::string dram_path;
    std::string dtb_path;
    std::string payload_path;

    // Parse arguments: positional: <hex_path> [max_cycles], named: --dram/--dtb/--payload
    int pos_idx = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--dram") == 0 && i + 1 < argc) {
            dram_path = argv[++i];
        } else if (strcmp(argv[i], "--dtb") == 0 && i + 1 < argc) {
            dtb_path = argv[++i];
        } else if (strcmp(argv[i], "--payload") == 0 && i + 1 < argc) {
            payload_path = argv[++i];
        } else if (argv[i][0] != '-') {
            if (pos_idx == 0) { hex_path = argv[i]; pos_idx++; }
            else if (pos_idx == 1) { max_cycles = strtoull(argv[i], nullptr, 10); pos_idx++; }
        }
    }

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
    dut->dmem_wr_en = 0;
    dut->dmem_wr_addr = 0;
    dut->dmem_wr_data = 0;
    dut->uart_rx_valid = 0;
    dut->uart_rx_data = 0;
    dut->eval();

    // Load firmware via IMEM write port during reset
    uint64_t time_ps = 0;
    for (size_t i = 0; i < firmware.size() && i < (1 << 12); i++) {
        dut->imem_wr_en = 1;
        dut->imem_wr_addr = (uint16_t)i;
        dut->imem_wr_data = firmware[i];
        dut->clk = 0; dut->eval();
        if (vcd) vcd->dump(time_ps++);
        dut->clk = 1; dut->eval();
        if (vcd) vcd->dump(time_ps++);
    }
    dut->imem_wr_en = 0;

    // Load DRAM binary (e.g. OpenSBI fw_jump.bin) at 0x80000000
    if (!dram_path.empty()) {
        auto dram_data = load_binary(dram_path);
        if (!dram_data.empty()) {
            load_dram(dut, vcd, dram_data.data(), dram_data.size(),
                      0x80000000, time_ps);
        }
    }

    // Load DTB at 0x80F00000
    if (!dtb_path.empty()) {
        auto dtb_data = load_binary(dtb_path);
        if (!dtb_data.empty()) {
            load_dram(dut, vcd, dtb_data.data(), dtb_data.size(),
                      0x80F00000, time_ps);
        }
    }

    // Load payload (e.g. Linux kernel) at 0x80400000 (FW_JUMP_ADDR, 4MB-aligned for Sv32 megapages)
    if (!payload_path.empty()) {
        auto payload_data = load_binary(payload_path);
        if (!payload_data.empty()) {
            load_dram(dut, vcd, payload_data.data(), payload_data.size(),
                      0x80400000, time_ps);
        }
    }

    // Release reset
    dut->rst = 0;

    // Simulation
    printf("Running Verilator simulation for %llu cycles...\n",
           (unsigned long long)max_cycles);

    // Determine mode: OpenSBI (has DRAM) vs firmware test
    bool opensbi_mode = !dram_path.empty();

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
        // trap signals sampled below

        // Sample trap signals
        bool trap = dut->trap_out;
        uint32_t trap_cause = dut->trap_cause_out;
        uint32_t trap_pc = dut->trap_pc_out;

        // Print PC for first few cycles and periodically
        if (cycle < 5 || cycle % 100000 == 0) {
            printf("cycle %llu: PC = 0x%08x\n",
                   (unsigned long long)cycle, pc);
        }

        // Trap/iTLB debug logging (disabled for clean output)

        // UART output
        if (uart_valid) {
            uart_log.push_back(uart_data);

            if (opensbi_mode) {
                // OpenSBI mode: print characters (byte in data[7:0])
                uint8_t ch = uart_data & 0xFF;
                if (ch >= 0x20 && ch <= 0x7E) {
                    putchar(ch);
                } else if (ch == '\n') {
                    putchar('\n');
                } else if (ch == '\r') {
                    // ignore CR
                } else {
                    printf("[0x%02x]", ch);
                }
                fflush(stdout);
            } else {
                // Firmware test mode: print hex words
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

        // Falling edge
        dut->clk = 0;
        dut->eval();
        time_ps++;
        if (vcd) vcd->dump(time_ps);
    }

    // Print summary
    if (opensbi_mode) {
        printf("\n=== OpenSBI simulation ended (%zu UART bytes) ===\n", uart_log.size());
    } else {
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

    // Cleanup
    if (vcd) { vcd->close(); delete vcd; }
    delete dut;
    return 0;
}
