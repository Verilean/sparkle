/*
 * CDC Multi-Domain JIT Runner
 *
 * Runs two JIT simulation instances (clock domains) on separate threads,
 * connected by the lock-free SPSC queue. Designed to be compiled as a
 * shared library and loaded via dlopen from sparkle_jit.c.
 *
 * Architecture:
 *   sparkle_jit.c  --(dlopen)--> cdc_runner.so
 *                                   |
 *                        +----------+----------+
 *                        |                     |
 *                   Thread A (Producer)   Thread B (Consumer)
 *                   evalTick + push       pop + set_input + evalTick
 *                        |                     |
 *                        +---- SPSC Queue -----+
 */

#pragma once

#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * JIT function pointer table — mirrors JITHandle from sparkle_jit.c.
 * Passed from the C side so cdc_runner can drive the simulation.
 */
typedef struct {
    void* ctx;
    void  (*eval_tick)(void*);
    void  (*set_input)(void*, uint32_t, uint64_t);
    uint64_t (*get_output)(void*, uint32_t);
    void* (*snapshot)(void*);
    void  (*restore)(void*, void*);
    void  (*free_snapshot)(void*);
} CDCJITVtable;

/*
 * Result struct returned by cdc_run.
 */
typedef struct {
    uint64_t messages_sent;
    uint64_t messages_received;
    uint64_t rollback_count;
    double   elapsed_ms;
    int      success;           /* 1 = ok, 0 = error */
} CDCRunResult;

/*
 * cdc_run — Run two JIT domains connected via SPSC queue.
 *
 * Thread A (producer): runs handle_a->eval_tick() for cycles_a cycles.
 *   Every send_interval cycles, reads get_output(out_port_a) and pushes
 *   the value + timestamp into the SPSC queue.
 *
 * Thread B (consumer): runs handle_b->eval_tick() for cycles_b cycles.
 *   Each cycle, tries to pop from the queue. If a message is available,
 *   sets it via set_input(in_port_b). Uses CDCConsumer for rollback
 *   detection with periodic snapshots.
 *
 * Parameters:
 *   handle_a      — JIT vtable for domain A (producer)
 *   handle_b      — JIT vtable for domain B (consumer)
 *   cycles_a      — number of eval_tick cycles to run for domain A
 *   cycles_b      — number of eval_tick cycles to run for domain B
 *   out_port_a    — output port index to read from domain A
 *   in_port_b     — input port index to write to domain B
 *   send_interval — how often (in A-cycles) to send a message (0 = every cycle)
 *   snapshot_interval — how often (in B-messages) to take a snapshot (0 = disabled)
 */
CDCRunResult cdc_run(
    CDCJITVtable* handle_a,
    CDCJITVtable* handle_b,
    uint64_t cycles_a,
    uint64_t cycles_b,
    uint32_t out_port_a,
    uint32_t in_port_b,
    uint32_t send_interval,
    uint32_t snapshot_interval
);

#ifdef __cplusplus
}
#endif
