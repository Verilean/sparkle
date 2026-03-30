/*
 * Multi-Core JIT Runner — N-thread parallel simulation
 *
 * Runs N sim_core instances on N threads with barrier sync per cycle.
 * Shared bus data is exchanged atomically between cycles.
 *
 * Build: g++ -O2 -std=c++17 -shared -fPIC -o multicore_runner.so multicore_runner.cpp -lpthread
 * Usage: linked with Sparkle-generated JIT .so
 */

#include <cstdio>
#include <cstdint>
#include <cstring>
#include <thread>
#include <atomic>
#include <chrono>
#include <vector>
#include <barrier>
#include <dlfcn.h>

// JIT function pointers (per-core instance)
struct CoreVtable {
    void* ctx;
    void  (*eval_tick)(void*);
    void  (*eval)(void*);
    void  (*tick)(void*);
    void  (*reset)(void*);
    void  (*set_input)(void*, uint32_t, uint64_t);
    uint64_t (*get_output)(void*, uint32_t);
};

struct MulticoreResult {
    uint64_t total_cycles;
    double elapsed_ms;
    double mcycles_per_sec;
    int success;
};

extern "C" {

/*
 * Run N cores in parallel for `cycles` cycles with barrier sync.
 *
 * Each core runs evalTick() independently, then barrier syncs.
 * Shared bus: each core's output[1] (serial_source_data) is OR'd
 * and fed back as input[0] (serial_sink_data) to all cores.
 */
MulticoreResult multicore_run(
    void* jit_lib,           // dlopen'd JIT .so handle
    int n_cores,
    uint64_t cycles,
    int batch_size           // cycles between barrier syncs (1 = every cycle)
) {
    MulticoreResult result = {};

    // Resolve JIT functions
    auto jit_create = (void*(*)())dlsym(jit_lib, "jit_create");
    auto jit_destroy = (void(*)(void*))dlsym(jit_lib, "jit_destroy");
    auto jit_reset = (void(*)(void*))dlsym(jit_lib, "jit_reset");
    auto jit_eval_tick = (void(*)(void*))dlsym(jit_lib, "jit_eval_tick");
    auto jit_eval = (void(*)(void*))dlsym(jit_lib, "jit_eval");
    auto jit_tick = (void(*)(void*))dlsym(jit_lib, "jit_tick");
    auto jit_set_input = (void(*)(void*, uint32_t, uint64_t))dlsym(jit_lib, "jit_set_input");
    auto jit_get_output = (uint64_t(*)(void*, uint32_t))dlsym(jit_lib, "jit_get_output");

    if (!jit_create || !jit_eval_tick || !jit_set_input || !jit_get_output) {
        fprintf(stderr, "multicore_run: missing JIT symbols\n");
        result.success = 0;
        return result;
    }

    // Create N core instances
    std::vector<void*> cores(n_cores);
    for (int i = 0; i < n_cores; i++) {
        cores[i] = jit_create();
        jit_reset(cores[i]);
        // serial_source_ready = 1 (input[2] for sim_core, or varies by wrapper)
        jit_set_input(cores[i], 2, 1);
    }

    // Shared bus data (atomic for cross-thread visibility)
    std::atomic<uint8_t> bus_data{0};

    // Barrier for cycle sync
    std::barrier sync_barrier(n_cores);

    // Per-thread work
    auto worker = [&](int core_id) {
        void* ctx = cores[core_id];
        for (uint64_t c = 0; c < cycles; c += batch_size) {
            uint64_t batch_end = std::min(c + (uint64_t)batch_size, cycles);

            for (uint64_t bc = c; bc < batch_end; bc++) {
                // Read shared bus data from previous cycle
                uint8_t bd = bus_data.load(std::memory_order_relaxed);
                jit_set_input(ctx, 0, bd);  // serial_sink_data = bus_data
                jit_set_input(ctx, 1, bd ? 1 : 0);  // serial_sink_valid = (bus_data != 0)

                // Run one cycle
                jit_eval_tick(ctx);
            }

            // Contribute to shared bus: OR all cores' output
            uint8_t my_output = (uint8_t)jit_get_output(ctx, 1);  // serial_source_data

            // Barrier: wait for all cores to finish this batch
            sync_barrier.arrive_and_wait();

            // Core 0 aggregates bus data
            if (core_id == 0) {
                uint8_t aggregated = 0;
                for (int i = 0; i < n_cores; i++) {
                    aggregated |= (uint8_t)jit_get_output(cores[i], 1);
                }
                bus_data.store(aggregated, std::memory_order_relaxed);
            }

            // Second barrier: ensure bus_data is updated before next batch
            sync_barrier.arrive_and_wait();
        }
    };

    // Launch threads and measure
    auto t0 = std::chrono::high_resolution_clock::now();

    std::vector<std::thread> threads;
    for (int i = 0; i < n_cores; i++) {
        threads.emplace_back(worker, i);
    }
    for (auto& t : threads) {
        t.join();
    }

    auto t1 = std::chrono::high_resolution_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();

    // Cleanup
    for (int i = 0; i < n_cores; i++) {
        jit_destroy(cores[i]);
    }

    result.total_cycles = cycles * n_cores;  // total core-cycles
    result.elapsed_ms = ms;
    result.mcycles_per_sec = (double)(cycles) / ms / 1000.0;  // per-core cycles/sec
    result.success = 1;
    return result;
}

} // extern "C"
