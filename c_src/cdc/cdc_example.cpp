/*
 * CDC Multi-Clock Simulation Example
 *
 * Demonstrates Time-Warping between two clock domains:
 *   - Domain A: 100MHz (period = 10ns) — fast producer
 *   - Domain B:  50MHz (period = 20ns) — slow consumer
 *
 * Domain A runs a simple counter and sends its value to Domain B
 * via the lock-free SPSC queue. Domain B receives the values and
 * detects if any timestamp inversion occurs (triggering rollback).
 *
 * Each domain runs on its own thread, advancing its local simulation
 * clock independently — this is "Time-Warping" (speculative execution).
 *
 * Build:  make cdc_example
 * Run:    ./cdc_example
 */

#include "spsc_queue.hpp"
#include "cdc_rollback.hpp"

#include <thread>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <vector>

using namespace sparkle::cdc;

/* ========================================================================
 * Simulated Hardware State
 * ======================================================================== */

/* Domain A: 100MHz counter that sends its value every N cycles */
struct DomainAState {
    uint64_t cycle;         /* current simulation cycle */
    uint64_t counter;       /* 8-bit counter register */
    uint64_t time_ps;       /* simulated time in picoseconds */
};

/* Domain B: 50MHz receiver that accumulates values from Domain A */
struct DomainBState {
    uint64_t cycle;
    uint64_t accumulator;   /* sum of received values */
    uint64_t receive_count; /* how many messages received */
    uint64_t time_ps;
};

static constexpr uint64_t DOMAIN_A_PERIOD_PS = 10'000;  /* 10ns = 100MHz */
static constexpr uint64_t DOMAIN_B_PERIOD_PS = 20'000;  /* 20ns =  50MHz */
static constexpr size_t   QUEUE_CAPACITY     = 1024;
static constexpr uint64_t SIM_CYCLES_A       = 200'000; /* Domain A runs 200K cycles */
static constexpr uint64_t SEND_INTERVAL      = 2;       /* Send every 2 A-cycles (= every B-cycle) */

/* ========================================================================
 * Domain A Thread — Fast Clock Producer
 * ======================================================================== */

static void domain_a_thread(
    SPSCQueue<CDCMessage, QUEUE_CAPACITY>& queue,
    std::atomic<bool>& done)
{
    DomainAState state = {0, 0, 0};

    for (uint64_t cyc = 0; cyc < SIM_CYCLES_A; cyc++) {
        /* === Eval: combinational logic === */
        uint64_t next_counter = (state.counter + 1) & 0xFF;

        /* === CDC Send: every SEND_INTERVAL cycles, push to queue === */
        if (cyc % SEND_INTERVAL == 0) {
            CDCMessage msg;
            msg.timestamp = state.time_ps;       /* current A-domain time */
            msg.payload   = state.counter;        /* hardware value to send */
            msg.signal_id = 0;                    /* signal: counter output */
            msg.flags     = 0;

            while (!queue.try_push(msg)) {
                /* Backpressure: queue full, spin until consumer catches up.
                   In a real Time-Warping sim, this would be a yield point. */
            }
        }

        /* === Tick: advance registers === */
        state.counter = next_counter;
        state.cycle   = cyc + 1;
        state.time_ps += DOMAIN_A_PERIOD_PS;
    }

    done.store(true, std::memory_order_release);
}

/* ========================================================================
 * Domain B Thread — Slow Clock Consumer
 * ======================================================================== */

static void domain_b_thread(
    SPSCQueue<CDCMessage, QUEUE_CAPACITY>& queue,
    std::atomic<bool>& producer_done,
    DomainBState& final_state,
    uint64_t& rollback_count,
    bool inject_inversion)
{
    DomainBState state = {0, 0, 0, 0};

    /* Snapshot support for rollback */
    auto take_snap = [&]() -> void* {
        return new DomainBState(state);
    };
    auto restore_snap = [&](void* s) {
        state = *static_cast<DomainBState*>(s);
    };
    auto free_snap = [](void* s) {
        delete static_cast<DomainBState*>(s);
    };
    auto get_ts = [](const CDCMessage& m) -> uint64_t {
        return m.timestamp;
    };

    CDCConsumer<CDCMessage, QUEUE_CAPACITY> consumer(
        queue, get_ts, take_snap, restore_snap, free_snap);

    /* Take initial snapshot */
    consumer.take_snapshot();

    bool inversion_injected = false;

    while (true) {
        CDCMessage msg;

        if (consumer.consume(msg)) {
            /* === Hardware logic: accumulate received values === */
            state.accumulator += msg.payload;
            state.receive_count++;
            state.time_ps = msg.timestamp;
            state.cycle++;

            /* Take periodic snapshots (every 1000 messages) */
            if (state.receive_count % 1000 == 0) {
                consumer.take_snapshot();
            }

            /* Optionally inject a fake inversion for demonstration */
            if (inject_inversion && !inversion_injected &&
                state.receive_count == 50'000) {
                /* Manually push a message with a past timestamp
                   to trigger rollback on next consume */
                CDCMessage bad_msg;
                bad_msg.timestamp = 1000;  /* way in the past */
                bad_msg.payload   = 0;
                bad_msg.signal_id = 0;
                bad_msg.flags     = 0;
                /* Push directly to queue (producer is still running) */
                while (!queue.try_push(bad_msg)) {}
                inversion_injected = true;
            }

            if (consumer.check_rollback()) {
                consumer.clear_rollback();
                /* In a real sim, we'd re-simulate from snapshot time.
                   Here we just note it happened and continue. */
            }
        } else {
            /* Queue empty — check if producer is done */
            if (producer_done.load(std::memory_order_acquire) &&
                queue.size_approx() == 0) {
                break;
            }
        }
    }

    final_state = state;
    rollback_count = consumer.rollback_count();
}

/* ========================================================================
 * Main — Run the multi-clock simulation
 * ======================================================================== */

int main() {
    printf("╔══════════════════════════════════════════════════╗\n");
    printf("║   Sparkle CDC Multi-Clock Simulation Example    ║\n");
    printf("╠══════════════════════════════════════════════════╣\n");
    printf("║  Domain A: 100MHz (10ns period) — Producer      ║\n");
    printf("║  Domain B:  50MHz (20ns period) — Consumer      ║\n");
    printf("║  Queue: SPSC lock-free, %4zu entries            ║\n", QUEUE_CAPACITY);
    printf("║  Simulation: %luK cycles (Domain A)            ║\n", SIM_CYCLES_A / 1000);
    printf("╚══════════════════════════════════════════════════╝\n\n");

    /* ---- Run 1: Normal operation (no rollback) ---- */
    {
        printf("--- Run 1: Normal Multi-Clock Simulation ---\n");

        SPSCQueue<CDCMessage, QUEUE_CAPACITY> queue;
        std::atomic<bool> done{false};
        DomainBState final_b = {};
        uint64_t rollbacks = 0;

        auto t_start = std::chrono::high_resolution_clock::now();

        std::thread ta(domain_a_thread, std::ref(queue), std::ref(done));
        std::thread tb(domain_b_thread, std::ref(queue), std::ref(done),
                       std::ref(final_b), std::ref(rollbacks), false);

        ta.join();
        tb.join();

        auto t_end = std::chrono::high_resolution_clock::now();
        double ms = std::chrono::duration<double, std::milli>(t_end - t_start).count();

        uint64_t expected_msgs = SIM_CYCLES_A / SEND_INTERVAL;

        printf("  Domain A: %lu cycles, final time = %lu ps (%.3f us)\n",
               SIM_CYCLES_A, SIM_CYCLES_A * DOMAIN_A_PERIOD_PS,
               SIM_CYCLES_A * DOMAIN_A_PERIOD_PS / 1e6);
        printf("  Domain B: %lu messages received (expected %lu)\n",
               final_b.receive_count, expected_msgs);
        printf("  Domain B: accumulator = %lu\n", final_b.accumulator);
        printf("  Rollbacks: %lu\n", rollbacks);
        printf("  Wall time: %.2f ms\n", ms);
        printf("  Throughput: %.2f M msg/sec\n",
               final_b.receive_count / (ms / 1000.0) / 1e6);
        printf("  Result: %s\n\n",
               (final_b.receive_count == expected_msgs && rollbacks == 0)
               ? "PASS" : "FAIL");
    }

    /* ---- Run 2: With timestamp inversion (rollback triggered) ---- */
    {
        printf("--- Run 2: Simulation with Timestamp Inversion ---\n");
        printf("  (Injecting past-timestamp message at message #50000)\n");

        SPSCQueue<CDCMessage, QUEUE_CAPACITY> queue;
        std::atomic<bool> done{false};
        DomainBState final_b = {};
        uint64_t rollbacks = 0;

        auto t_start = std::chrono::high_resolution_clock::now();

        std::thread ta(domain_a_thread, std::ref(queue), std::ref(done));
        std::thread tb(domain_b_thread, std::ref(queue), std::ref(done),
                       std::ref(final_b), std::ref(rollbacks), true);

        ta.join();
        tb.join();

        auto t_end = std::chrono::high_resolution_clock::now();
        double ms = std::chrono::duration<double, std::milli>(t_end - t_start).count();

        printf("  Domain B: %lu messages received\n", final_b.receive_count);
        printf("  Rollbacks: %lu (expected 1)\n", rollbacks);
        printf("  Wall time: %.2f ms\n", ms);
        printf("  Result: %s\n\n", (rollbacks == 1) ? "PASS" : "FAIL");
    }

    return 0;
}
