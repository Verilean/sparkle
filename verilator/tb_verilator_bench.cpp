// Minimal Verilator benchmark — pure eval loop, no printf, no early exit
#include "obj_dir/Vrv32i_soc.h"
#include "obj_dir/Vrv32i_soc___024root.h"
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <chrono>
#include <fstream>
#include <string>
#include <vector>

double sc_time_stamp() { return 0; }

static std::vector<uint32_t> load_hex(const std::string& path) {
    std::vector<uint32_t> words;
    std::ifstream f(path);
    if (!f.is_open()) return words;
    std::string line;
    while (std::getline(f, line)) {
        if (line.empty() || line[0] == '/' || line[0] == '#' || line[0] == '@') continue;
        words.push_back((uint32_t)strtoul(line.c_str(), nullptr, 16));
    }
    return words;
}

int main(int argc, char** argv) {
    std::string hex_path = "../firmware/firmware.hex";
    uint64_t max_cycles = 10000000;
    if (argc > 1) hex_path = argv[1];
    if (argc > 2) max_cycles = strtoull(argv[2], nullptr, 10);

    auto firmware = load_hex(hex_path);
    printf("Verilator Bench: %zu firmware words, %llu cycles\n",
           firmware.size(), max_cycles);

    Verilated::commandArgs(argc, argv);
    auto* dut = new Vrv32i_soc;

    // Reset
    dut->rst = 1; dut->clk = 0;
    dut->eval(); dut->clk = 1; dut->eval();
    dut->clk = 0; dut->eval(); dut->clk = 1; dut->eval();
    dut->rst = 0;

    // Benchmark: pure eval loop, no firmware (NOP sled)
    auto t0 = std::chrono::high_resolution_clock::now();
    for (uint64_t c = 0; c < max_cycles; c++) {
        dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
    }
    auto t1 = std::chrono::high_resolution_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();

    printf("  %llu cycles in %.1f ms (%.0f cycles/sec)\n",
           max_cycles, ms, max_cycles * 1000.0 / ms);

    delete dut;
    return 0;
}
