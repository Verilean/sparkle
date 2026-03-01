// Minimal testbench for hand-written rv32i_soc — no internal signal access
#include "Vrv32i_soc.h"
#include "verilated.h"
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>

static std::vector<uint32_t> load_hex(const std::string& path) {
    std::vector<uint32_t> words;
    std::ifstream f(path);
    if (!f.is_open()) { fprintf(stderr, "Error: cannot open %s\n", path.c_str()); return words; }
    std::string line;
    while (std::getline(f, line)) {
        if (line.empty() || line[0] == '/' || line[0] == '#' || line[0] == '@') continue;
        words.push_back((uint32_t)strtoul(line.c_str(), nullptr, 16));
    }
    return words;
}

static std::vector<uint8_t> load_binary(const std::string& path) {
    std::vector<uint8_t> data;
    std::ifstream f(path, std::ios::binary);
    if (!f.is_open()) { fprintf(stderr, "Error: cannot open binary %s\n", path.c_str()); return data; }
    f.seekg(0, std::ios::end); size_t sz = f.tellg(); f.seekg(0, std::ios::beg);
    data.resize(sz); f.read(reinterpret_cast<char*>(data.data()), sz);
    return data;
}

static void load_dram(Vrv32i_soc* dut, const uint8_t* data, size_t len,
                      uint32_t base_addr, uint64_t& time_ps) {
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
        dut->clk = 0; dut->eval(); time_ps++;
        dut->clk = 1; dut->eval(); time_ps++;
    }
    dut->dmem_wr_en = 0;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    std::string hex_path = "../firmware/firmware.hex";
    uint64_t max_cycles = 100000;
    std::string dram_path, dtb_path, payload_path;

    int pos_idx = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--dram") == 0 && i + 1 < argc) dram_path = argv[++i];
        else if (strcmp(argv[i], "--dtb") == 0 && i + 1 < argc) dtb_path = argv[++i];
        else if (strcmp(argv[i], "--payload") == 0 && i + 1 < argc) payload_path = argv[++i];
        else if (argv[i][0] != '-') {
            if (pos_idx == 0) { hex_path = argv[i]; pos_idx++; }
            else if (pos_idx == 1) { max_cycles = strtoull(argv[i], nullptr, 10); pos_idx++; }
        }
    }

    auto firmware = load_hex(hex_path);
    printf("Loaded %zu firmware words from %s\n", firmware.size(), hex_path.c_str());

    Vrv32i_soc* dut = new Vrv32i_soc;
    dut->clk = 0; dut->rst = 1;
    dut->imem_wr_en = 0; dut->dmem_wr_en = 0;
    dut->uart_rx_valid = 0; dut->uart_rx_data = 0;
    dut->eval();

    uint64_t time_ps = 0;
    for (size_t i = 0; i < firmware.size() && i < (1 << 12); i++) {
        dut->imem_wr_en = 1; dut->imem_wr_addr = (uint16_t)i; dut->imem_wr_data = firmware[i];
        dut->clk = 0; dut->eval(); time_ps++;
        dut->clk = 1; dut->eval(); time_ps++;
    }
    dut->imem_wr_en = 0;

    if (!dram_path.empty()) {
        auto d = load_binary(dram_path);
        if (!d.empty()) load_dram(dut, d.data(), d.size(), 0x80000000, time_ps);
    }
    if (!dtb_path.empty()) {
        auto d = load_binary(dtb_path);
        if (!d.empty()) load_dram(dut, d.data(), d.size(), 0x80F00000, time_ps);
    }
    if (!payload_path.empty()) {
        auto d = load_binary(payload_path);
        if (!d.empty()) load_dram(dut, d.data(), d.size(), 0x80400000, time_ps);
    }

    dut->rst = 0;
    printf("Running simulation for %llu cycles...\n", (unsigned long long)max_cycles);

    bool opensbi_mode = !dram_path.empty();
    uint32_t prev_pc = 0xFFFFFFFF;
    int halt_count = 0;
    std::vector<uint32_t> uart_log;

    for (uint64_t cycle = 0; cycle < max_cycles; cycle++) {
        dut->clk = 1; dut->eval(); time_ps++;
        uint32_t pc = dut->pc_out;
        bool uart_valid = dut->uart_tx_valid;
        uint32_t uart_data = dut->uart_tx_data;

        static uint32_t prev_pc_log = 0;
        bool pc_changed_region = ((pc & 0xF0000000) != (prev_pc_log & 0xF0000000));
        if (cycle < 10 || cycle % 100000 == 0 || pc_changed_region) {
            printf("cycle %llu: PC = 0x%08x\n", (unsigned long long)cycle, pc);
        }
        prev_pc_log = pc;

        if (uart_valid) {
            uart_log.push_back(uart_data);
            if (opensbi_mode) {
                uint8_t ch = uart_data & 0xFF;
                if (ch >= 0x20 && ch <= 0x7E) putchar(ch);
                else if (ch == '\n') putchar('\n');
                else if (ch != '\r') printf("[0x%02x]", ch);
                fflush(stdout);
            } else {
                printf("  UART[%zu]: 0x%08x\n", uart_log.size(), uart_data);
                if (uart_data == 0xCAFE0000u || uart_data == 0xDEADDEADu) {
                    for (int drain = 0; drain < 20; drain++) {
                        dut->clk = 0; dut->eval(); time_ps++;
                        dut->clk = 1; dut->eval(); time_ps++;
                        if (dut->uart_tx_valid) {
                            uart_log.push_back(dut->uart_tx_data);
                            printf("  UART[%zu]: 0x%08x\n", uart_log.size(), dut->uart_tx_data);
                        }
                    }
                    break;
                }
            }
        }

        // === dt_scan_memory monitoring (same as generated SoC testbench) ===
        if (pc == 0xC0151484) {
            printf("cycle %llu: early_init_dt_scan_memory: sw a0,8(sp) at PC=0xc0151484\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC0151488) {
            printf("cycle %llu: dt_scan_memory: bnez a0 at C0151488 (reg found → jump to C01514A4)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC015148C) {
            printf("cycle %llu: dt_scan_memory: FALLTHROUGH to linux,usable-memory (reg was NULL!)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC01514A0) {
            printf("cycle %llu: early_init_dt_scan_memory: sw a0,8(sp) at PC=0xc01514a0\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC01514A4) {
            printf("cycle %llu: early_init_dt_scan_memory: lw/beqz s4,8(sp) at PC=0xc01514a4\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC01514F8) {
            printf("cycle %llu: dt_scan_memory: bge check at C01514F8\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC0151510) {
            printf("cycle %llu: dt_mem_next_cell for BASE (C0151510)\n", (unsigned long long)cycle);
        }
        if (pc == 0xC015154C) {
            printf("cycle %llu: early_init_dt_add_memory_arch CALL (C015154C)\n",
                   (unsigned long long)cycle);
        }

        if (pc == prev_pc) {
            halt_count++;
            if (halt_count >= 50) {
                printf("\nHalt detected at cycle %llu: PC = 0x%08x\n",
                       (unsigned long long)cycle, pc);
                break;
            }
        } else halt_count = 0;
        prev_pc = pc;

        dut->clk = 0; dut->eval(); time_ps++;
    }

    printf("\n=== Simulation ended (%zu UART %s) ===\n",
           uart_log.size(), opensbi_mode ? "bytes" : "words");
    delete dut;
    return 0;
}
