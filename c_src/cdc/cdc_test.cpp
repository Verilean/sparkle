/*
 * CDC Lock-Free Queue — Correctness Tests & Benchmark
 *
 * Phase 1: SPSC queue correctness (10M messages, 0 loss, 0 inversion)
 *          + throughput benchmark (ops/sec)
 * Phase 2: Rollback detection on timestamp inversion with snapshot restore
 *
 * Build:  make
 * Run:    ./cdc_test
 */

#include "spsc_queue.hpp"
#include "cdc_rollback.hpp"

#include <thread>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cassert>

using namespace sparkle::cdc;

static constexpr size_t kQueueCapacity = 1024; /* 2^10 */
static constexpr size_t kNumMessages   = 10'000'000;

/* ========================================================================
 * Phase 1: SPSC Queue Correctness + Benchmark
 * ======================================================================== */

static bool test_phase1_correctness() {
    printf("=== Phase 1: Correctness Test (10M messages) ===\n");

    SPSCQueue<CDCMessage, kQueueCapacity> queue;

    uint64_t consumer_count = 0;
    uint64_t last_timestamp = 0;
    bool ordering_ok = true;
    bool payload_ok  = true;

    std::thread producer([&queue]() {
        for (uint64_t i = 0; i < kNumMessages; i++) {
            CDCMessage msg;
            msg.timestamp = i + 1;          /* monotonically increasing */
            msg.payload   = i * 42 + 7;     /* deterministic payload */
            msg.signal_id = static_cast<uint32_t>(i & 0xFF);
            msg.flags     = 0;

            while (!queue.try_push(msg)) {
                /* Spin until slot available */
            }
        }
    });

    std::thread consumer([&]() {
        while (consumer_count < kNumMessages) {
            CDCMessage msg;
            if (queue.try_pop(msg)) {
                /* Check ordering: each timestamp must be >= previous */
                if (msg.timestamp < last_timestamp) {
                    ordering_ok = false;
                }
                last_timestamp = msg.timestamp;

                /* Check payload integrity */
                uint64_t expected_seq = msg.timestamp - 1;
                uint64_t expected_payload = expected_seq * 42 + 7;
                if (msg.payload != expected_payload) {
                    payload_ok = false;
                }

                consumer_count++;
            }
        }
    });

    producer.join();
    consumer.join();

    bool pass = true;

    printf("  Messages received: %lu / %lu", consumer_count, kNumMessages);
    if (consumer_count != kNumMessages) { printf(" FAIL"); pass = false; }
    else { printf(" OK"); }
    printf("\n");

    printf("  Ordering (no inversion): %s\n", ordering_ok ? "OK" : "FAIL");
    if (!ordering_ok) pass = false;

    printf("  Payload integrity: %s\n", payload_ok ? "OK" : "FAIL");
    if (!payload_ok) pass = false;

    printf("  Queue empty after test: %s\n",
           queue.size_approx() == 0 ? "OK" : "FAIL");
    if (queue.size_approx() != 0) pass = false;

    printf("  Phase 1 Correctness: %s\n\n", pass ? "PASS" : "FAIL");
    return pass;
}

static bool test_phase1_benchmark() {
    printf("=== Phase 1: Benchmark (10M messages) ===\n");

    SPSCQueue<CDCMessage, kQueueCapacity> queue;

    auto start = std::chrono::high_resolution_clock::now();

    std::thread producer([&queue]() {
        for (uint64_t i = 0; i < kNumMessages; i++) {
            CDCMessage msg;
            msg.timestamp = i + 1;
            msg.payload   = i;
            msg.signal_id = 0;
            msg.flags     = 0;
            while (!queue.try_push(msg)) { /* spin */ }
        }
    });

    uint64_t count = 0;
    std::thread consumer([&]() {
        CDCMessage msg;
        while (count < kNumMessages) {
            if (queue.try_pop(msg)) {
                count++;
            }
        }
    });

    producer.join();
    consumer.join();

    auto end = std::chrono::high_resolution_clock::now();
    double elapsed_ms = std::chrono::duration<double, std::milli>(end - start).count();
    double ops_per_sec = static_cast<double>(kNumMessages) / (elapsed_ms / 1000.0);

    printf("  Elapsed: %.2f ms\n", elapsed_ms);
    printf("  Throughput: %.2f M ops/sec\n", ops_per_sec / 1e6);
    printf("  Queue capacity: %zu\n", kQueueCapacity);
    printf("  CDCMessage size: %zu bytes\n", sizeof(CDCMessage));
    printf("  SPSCQueue size: %zu bytes\n\n",
           sizeof(SPSCQueue<CDCMessage, kQueueCapacity>));

    return true;
}

/* ========================================================================
 * Phase 2: Rollback Detection & State Restoration
 * ======================================================================== */

/* Mock simulation state for testing rollback */
struct MockSimState {
    uint64_t register_a;
    uint64_t register_b;
    uint64_t cycle_count;
};

static bool test_phase2_rollback() {
    printf("=== Phase 2: Rollback Detection Test ===\n");

    SPSCQueue<CDCMessage, kQueueCapacity> queue;

    /* Mock simulation state */
    MockSimState sim_state = {0, 0, 0};

    auto take_snap = [&]() -> void* {
        auto* snap = new MockSimState(sim_state);
        return snap;
    };
    auto restore_snap = [&](void* snap) {
        sim_state = *static_cast<MockSimState*>(snap);
    };
    auto free_snap = [](void* snap) {
        delete static_cast<MockSimState*>(snap);
    };
    auto get_ts = [](const CDCMessage& msg) -> uint64_t {
        return msg.timestamp;
    };

    CDCConsumer<CDCMessage, kQueueCapacity> consumer(
        queue, get_ts, take_snap, restore_snap, free_snap);

    bool pass = true;

    /* Step 1: Push 5 normal messages with increasing timestamps */
    for (uint64_t i = 1; i <= 5; i++) {
        CDCMessage msg{i * 100, i * 10, 0, 0};
        assert(queue.try_push(msg));
    }

    /* Step 2: Consume 3 messages, take snapshot after 3rd */
    for (int i = 0; i < 3; i++) {
        CDCMessage msg;
        assert(consumer.consume(msg));
        sim_state.register_a = msg.payload;
        sim_state.cycle_count++;
    }

    /* Snapshot state: register_a=30, cycle_count=3 */
    consumer.take_snapshot();
    MockSimState state_at_snapshot = sim_state;

    printf("  State at snapshot: reg_a=%lu, cycles=%lu\n",
           state_at_snapshot.register_a, state_at_snapshot.cycle_count);

    /* Step 3: Consume 2 more messages (advance state beyond snapshot) */
    for (int i = 0; i < 2; i++) {
        CDCMessage msg;
        assert(consumer.consume(msg));
        sim_state.register_a = msg.payload;
        sim_state.cycle_count++;
    }

    printf("  State after advancing: reg_a=%lu, cycles=%lu\n",
           sim_state.register_a, sim_state.cycle_count);

    /* Verify no rollback yet */
    printf("  Rollback before injection: %s\n",
           !consumer.check_rollback() ? "OK (none)" : "FAIL");
    if (consumer.check_rollback()) pass = false;

    /* Step 4: Inject a message with PAST timestamp (timestamp inversion!) */
    CDCMessage bad_msg{50, 999, 0, 0};  /* timestamp=50 < local_time=500 */
    assert(queue.try_push(bad_msg));

    CDCMessage received;
    assert(consumer.consume(received));

    /* Step 5: Verify rollback was triggered */
    printf("  Rollback detected: %s\n",
           consumer.check_rollback() ? "OK (yes)" : "FAIL");
    if (!consumer.check_rollback()) pass = false;

    printf("  Rollback count: %lu\n", consumer.rollback_count());
    if (consumer.rollback_count() != 1) {
        printf("  Expected rollback_count=1, got %lu FAIL\n",
               consumer.rollback_count());
        pass = false;
    }

    /* Step 6: Verify simulation state was restored to snapshot */
    printf("  State after rollback: reg_a=%lu, cycles=%lu\n",
           sim_state.register_a, sim_state.cycle_count);
    if (sim_state.register_a != state_at_snapshot.register_a ||
        sim_state.cycle_count != state_at_snapshot.cycle_count) {
        printf("  State restoration FAIL (expected reg_a=%lu, cycles=%lu)\n",
               state_at_snapshot.register_a, state_at_snapshot.cycle_count);
        pass = false;
    } else {
        printf("  State restoration: OK\n");
    }

    /* Step 7: Verify consumer local_time was updated to message timestamp */
    printf("  Consumer local_time: %lu (expected 50)\n", consumer.local_time());
    if (consumer.local_time() != 50) pass = false;

    /* Step 8: Verify queue still works after rollback (indices not rolled back) */
    consumer.clear_rollback();

    CDCMessage post_rollback_msg{600, 123, 0, 0};
    assert(queue.try_push(post_rollback_msg));

    CDCMessage post_msg;
    assert(consumer.consume(post_msg));
    printf("  Post-rollback consume: payload=%lu %s\n",
           post_msg.payload, post_msg.payload == 123 ? "OK" : "FAIL");
    if (post_msg.payload != 123) pass = false;

    printf("  Post-rollback rollback flag: %s\n",
           !consumer.check_rollback() ? "OK (cleared)" : "FAIL");
    if (consumer.check_rollback()) pass = false;

    printf("  Phase 2 Rollback: %s\n\n", pass ? "PASS" : "FAIL");
    return pass;
}

static bool test_phase2_multithreaded_rollback() {
    printf("=== Phase 2: Multi-threaded Rollback Test ===\n");

    SPSCQueue<CDCMessage, kQueueCapacity> queue;
    MockSimState sim_state = {0, 0, 0};

    auto take_snap = [&]() -> void* { return new MockSimState(sim_state); };
    auto restore_snap = [&](void* s) { sim_state = *static_cast<MockSimState*>(s); };
    auto free_snap = [](void* s) { delete static_cast<MockSimState*>(s); };
    auto get_ts = [](const CDCMessage& m) -> uint64_t { return m.timestamp; };

    CDCConsumer<CDCMessage, kQueueCapacity> consumer(
        queue, get_ts, take_snap, restore_snap, free_snap);

    static constexpr size_t kMsgCount = 1'000'000;
    static constexpr size_t kInversionAt = 500'000;

    std::thread producer([&queue]() {
        for (uint64_t i = 0; i < kMsgCount; i++) {
            CDCMessage msg;
            if (i == kInversionAt) {
                /* Inject timestamp inversion */
                msg.timestamp = 1; /* way in the past */
            } else {
                msg.timestamp = i + 1;
            }
            msg.payload = i;
            msg.signal_id = 0;
            msg.flags = 0;
            while (!queue.try_push(msg)) { /* spin */ }
        }
    });

    uint64_t consumed = 0;
    bool snapshot_taken = false;

    std::thread consumer_thread([&]() {
        CDCMessage msg;
        while (consumed < kMsgCount) {
            if (consumer.consume(msg)) {
                sim_state.register_a = msg.payload;
                sim_state.cycle_count++;
                consumed++;

                /* Take snapshot early so rollback has something to restore */
                if (consumed == 100 && !snapshot_taken) {
                    consumer.take_snapshot();
                    snapshot_taken = true;
                }
            }
        }
    });

    producer.join();
    consumer_thread.join();

    bool pass = true;

    printf("  Messages consumed: %lu / %lu", consumed, kMsgCount);
    if (consumed != kMsgCount) { printf(" FAIL"); pass = false; }
    else { printf(" OK"); }
    printf("\n");

    printf("  Rollback detected: %s\n",
           consumer.check_rollback() ? "OK (yes)" : "FAIL");
    if (!consumer.check_rollback()) pass = false;

    printf("  Rollback count: %lu (expected 1)\n", consumer.rollback_count());
    if (consumer.rollback_count() != 1) pass = false;

    printf("  Phase 2 Multi-threaded: %s\n\n", pass ? "PASS" : "FAIL");
    return pass;
}

/* ========================================================================
 * Main
 * ======================================================================== */

int main() {
    printf("Sparkle CDC Lock-Free Queue Tests\n");
    printf("==================================\n\n");

    bool all_pass = true;

    all_pass &= test_phase1_correctness();
    all_pass &= test_phase1_benchmark();
    all_pass &= test_phase2_rollback();
    all_pass &= test_phase2_multithreaded_rollback();

    printf("==================================\n");
    printf("Overall: %s\n", all_pass ? "ALL PASS" : "SOME FAILED");

    return all_pass ? 0 : 1;
}
