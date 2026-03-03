// ============================================================================
// JIT Benchmark Testbench for Sparkle RV32I SoC
//
// Measures pure JIT performance by calling the shared library directly.
// Compares against CppSim (inline) and Verilator baselines.
// Usage: ./jit_bench [firmware.hex] [max_cycles] [jit_dylib]
// ============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>
#include <chrono>
#include <dlfcn.h>

// Load hex file
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

// JIT function types
typedef void* (*jit_create_fn)();
typedef void  (*jit_destroy_fn)(void*);
typedef void  (*jit_eval_fn)(void*);
typedef void  (*jit_tick_fn)(void*);
typedef void  (*jit_eval_tick_fn)(void*);
typedef void  (*jit_reset_fn)(void*);
typedef void  (*jit_set_mem_fn)(void*, uint32_t, uint32_t, uint32_t);
typedef uint64_t (*jit_get_wire_fn)(void*, uint32_t);
typedef const char* (*jit_wire_name_fn)(uint32_t);
typedef uint32_t (*jit_num_wires_fn)();

int main(int argc, char** argv) {
    std::string hex_path = "../firmware/opensbi/boot.hex";
    uint64_t max_cycles = 1000000;
    std::string dylib_path = "generated_soc_jit.dylib";

    if (argc > 1) hex_path = argv[1];
    if (argc > 2) max_cycles = strtoull(argv[2], nullptr, 10);
    if (argc > 3) dylib_path = argv[3];

    // Load firmware
    auto firmware = load_hex(hex_path);
    printf("JIT Bench: Loaded %zu firmware words from %s\n", firmware.size(), hex_path.c_str());

    // Load shared library
    printf("JIT Bench: Loading %s...\n", dylib_path.c_str());
    void* lib = dlopen(dylib_path.c_str(), RTLD_LAZY);
    if (!lib) {
        fprintf(stderr, "dlopen failed: %s\n", dlerror());
        return 1;
    }

    auto create   = (jit_create_fn)dlsym(lib, "jit_create");
    auto destroy  = (jit_destroy_fn)dlsym(lib, "jit_destroy");
    auto eval     = (jit_eval_fn)dlsym(lib, "jit_eval");
    auto tick     = (jit_tick_fn)dlsym(lib, "jit_tick");
    auto eval_tick = (jit_eval_tick_fn)dlsym(lib, "jit_eval_tick");
    auto reset    = (jit_reset_fn)dlsym(lib, "jit_reset");
    auto set_mem  = (jit_set_mem_fn)dlsym(lib, "jit_set_mem");
    auto get_wire = (jit_get_wire_fn)dlsym(lib, "jit_get_wire");
    auto wire_name = (jit_wire_name_fn)dlsym(lib, "jit_wire_name");
    auto num_wires = (jit_num_wires_fn)dlsym(lib, "jit_num_wires");

    if (!create || !eval || !tick || !set_mem || !get_wire) {
        fprintf(stderr, "Failed to resolve JIT symbols\n");
        return 1;
    }

    void* ctx = create();

    // Load firmware into IMEM (memory 0)
    uint32_t mem_size = firmware.size();
    if (mem_size > 4096) mem_size = 4096;
    for (uint32_t i = 0; i < mem_size; i++) {
        set_mem(ctx, 0, i, firmware[i]);
    }

    // Find wire indices for PC and UART
    uint32_t n_wires = num_wires();
    uint32_t pc_idx = 0, uart_valid_idx = 0, uart_data_idx = 0;
    bool found_pc = false, found_uv = false, found_ud = false;
    for (uint32_t i = 0; i < n_wires; i++) {
        const char* name = wire_name(i);
        if (!name) continue;
        if (strcmp(name, "_gen_pcReg") == 0) { pc_idx = i; found_pc = true; }
        if (strcmp(name, "_gen_uartValidBV") == 0) { uart_valid_idx = i; found_uv = true; }
        if (strcmp(name, "_gen_prevStoreData") == 0) { uart_data_idx = i; found_ud = true; }
    }
    printf("JIT Bench: Wires — pcReg=%u, uartValid=%u, uartData=%u\n",
           pc_idx, uart_valid_idx, uart_data_idx);

    // ================================================================
    // Benchmark 1: eval+tick only (no wire reads) — pure simulation speed
    // ================================================================
    printf("\n=== Benchmark 1: Pure eval+tick (no wire reads) ===\n");
    reset(ctx);
    for (uint32_t i = 0; i < mem_size; i++) {
        set_mem(ctx, 0, i, firmware[i]);
    }
    auto t0 = std::chrono::high_resolution_clock::now();
    for (uint64_t c = 0; c < max_cycles; c++) {
        eval(ctx);
        tick(ctx);
    }
    auto t1 = std::chrono::high_resolution_clock::now();
    double ms1 = std::chrono::duration<double, std::milli>(t1 - t0).count();
    printf("  %llu cycles in %.1f ms (%.0f cycles/sec)\n",
           max_cycles, ms1, max_cycles * 1000.0 / ms1);

    // ================================================================
    // Benchmark 2: eval+tick + read 1 wire (PC only)
    // ================================================================
    printf("\n=== Benchmark 2: eval+tick + read PC wire ===\n");
    reset(ctx);
    for (uint32_t i = 0; i < mem_size; i++) {
        set_mem(ctx, 0, i, firmware[i]);
    }
    t0 = std::chrono::high_resolution_clock::now();
    uint64_t last_pc = 0;
    for (uint64_t c = 0; c < max_cycles; c++) {
        eval(ctx);
        last_pc = get_wire(ctx, pc_idx);
        tick(ctx);
    }
    t1 = std::chrono::high_resolution_clock::now();
    double ms2 = std::chrono::duration<double, std::milli>(t1 - t0).count();
    printf("  %llu cycles in %.1f ms (%.0f cycles/sec), final PC=0x%08llx\n",
           max_cycles, ms2, max_cycles * 1000.0 / ms2, last_pc);

    // ================================================================
    // Benchmark 3: eval+tick + read 6 wires (like loopMemoJIT)
    // ================================================================
    printf("\n=== Benchmark 3: eval+tick + read 6 output wires ===\n");
    reset(ctx);
    for (uint32_t i = 0; i < mem_size; i++) {
        set_mem(ctx, 0, i, firmware[i]);
    }

    // Find all 6 output wire indices
    const char* output_names[] = {
        "_gen_pcReg", "_gen_uartValidBV", "_gen_prevStoreData",
        "_gen_satpReg", "_gen_ptwPteReg", "_gen_ptwVaddrReg"
    };
    uint32_t output_idx[6];
    for (int j = 0; j < 6; j++) {
        output_idx[j] = 0;
        for (uint32_t i = 0; i < n_wires; i++) {
            const char* name = wire_name(i);
            if (name && strcmp(name, output_names[j]) == 0) {
                output_idx[j] = i;
                break;
            }
        }
    }

    t0 = std::chrono::high_resolution_clock::now();
    uint64_t uart_count = 0;
    for (uint64_t c = 0; c < max_cycles; c++) {
        eval(ctx);
        uint64_t vals[6];
        for (int j = 0; j < 6; j++) {
            vals[j] = get_wire(ctx, output_idx[j]);
        }
        if (vals[1] != 0) uart_count++;
        if (c % 100000 == 0) {
            printf("  cycle %llu: PC=0x%08llx\n", c, vals[0]);
        }
        tick(ctx);
    }
    t1 = std::chrono::high_resolution_clock::now();
    double ms3 = std::chrono::duration<double, std::milli>(t1 - t0).count();
    printf("  %llu cycles in %.1f ms (%.0f cycles/sec), %llu UART words\n",
           max_cycles, ms3, max_cycles * 1000.0 / ms3, uart_count);

    // ================================================================
    // Benchmark 4: evalTick (fused) — no wire reads
    // ================================================================
    double ms4 = 0;
    if (eval_tick) {
        printf("\n=== Benchmark 4: Fused evalTick (no wire reads) ===\n");
        reset(ctx);
        for (uint32_t i = 0; i < mem_size; i++) {
            set_mem(ctx, 0, i, firmware[i]);
        }
        t0 = std::chrono::high_resolution_clock::now();
        for (uint64_t c = 0; c < max_cycles; c++) {
            eval_tick(ctx);
        }
        t1 = std::chrono::high_resolution_clock::now();
        ms4 = std::chrono::duration<double, std::milli>(t1 - t0).count();
        printf("  %llu cycles in %.1f ms (%.0f cycles/sec)\n",
               max_cycles, ms4, max_cycles * 1000.0 / ms4);
    }

    // ================================================================
    // Benchmark 5: evalTick (fused) + read 6 wires
    // ================================================================
    double ms5 = 0;
    if (eval_tick) {
        printf("\n=== Benchmark 5: Fused evalTick + read 6 output wires ===\n");
        reset(ctx);
        for (uint32_t i = 0; i < mem_size; i++) {
            set_mem(ctx, 0, i, firmware[i]);
        }
        t0 = std::chrono::high_resolution_clock::now();
        uint64_t uart_count5 = 0;
        for (uint64_t c = 0; c < max_cycles; c++) {
            eval_tick(ctx);
            uint64_t vals[6];
            for (int j = 0; j < 6; j++) {
                vals[j] = get_wire(ctx, output_idx[j]);
            }
            if (vals[1] != 0) uart_count5++;
            if (c % 100000 == 0) {
                printf("  cycle %llu: PC=0x%08llx\n", c, vals[0]);
            }
        }
        t1 = std::chrono::high_resolution_clock::now();
        ms5 = std::chrono::duration<double, std::milli>(t1 - t0).count();
        printf("  %llu cycles in %.1f ms (%.0f cycles/sec), %llu UART words\n",
               max_cycles, ms5, max_cycles * 1000.0 / ms5, uart_count5);
    }

    // ================================================================
    // Summary
    // ================================================================
    printf("\n=== Summary (%llu cycles) ===\n", max_cycles);
    printf("  Pure eval+tick:        %.1f ms  (%7.0f cycles/sec)\n", ms1, max_cycles*1000.0/ms1);
    printf("  eval+tick+1 wire:      %.1f ms  (%7.0f cycles/sec)\n", ms2, max_cycles*1000.0/ms2);
    printf("  eval+tick+6 wires:     %.1f ms  (%7.0f cycles/sec)\n", ms3, max_cycles*1000.0/ms3);
    if (eval_tick) {
        printf("  Fused evalTick:        %.1f ms  (%7.0f cycles/sec)\n", ms4, max_cycles*1000.0/ms4);
        printf("  Fused evalTick+6 wire: %.1f ms  (%7.0f cycles/sec)\n", ms5, max_cycles*1000.0/ms5);
        printf("  Speedup (pure):        %.2fx\n", ms1 / ms4);
        printf("  Speedup (6 wires):     %.2fx\n", ms3 / ms5);
    }
    printf("  Overhead per wire read: %.1f%%\n", (ms3 - ms1) / ms1 * 100.0);

    destroy(ctx);
    dlclose(lib);
    return 0;
}
