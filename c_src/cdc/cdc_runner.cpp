/*
 * CDC Multi-Domain JIT Runner — Implementation
 *
 * Compiled as a shared library (cdc_runner.so / cdc_runner.dylib)
 * and loaded via dlopen from sparkle_jit.c.
 *
 * Build: make cdc_runner.so  (or cdc_runner.dylib on macOS)
 */

#include "cdc_runner.hpp"
#include "spsc_queue.hpp"
#include "cdc_rollback.hpp"

#include <thread>
#include <atomic>
#include <chrono>
#include <cstdio>

using namespace sparkle::cdc;

static constexpr size_t kQueueCapacity = 1024;

extern "C" {

CDCRunResult cdc_run(
    CDCJITVtable* vt_a,
    CDCJITVtable* vt_b,
    uint64_t cycles_a,
    uint64_t cycles_b,
    uint32_t out_port_a,
    uint32_t in_port_b,
    uint32_t send_interval,
    uint32_t snapshot_interval)
{
    CDCRunResult result = {};

    if (!vt_a || !vt_b || !vt_a->ctx || !vt_b->ctx) {
        fprintf(stderr, "CDC: null vtable or context\n");
        result.success = 0;
        return result;
    }

    if (send_interval == 0) send_interval = 1;
    if (snapshot_interval == 0) snapshot_interval = 1000;

    fprintf(stderr, "CDC: starting (A: %lu cyc, B: %lu cyc, interval=%u)\n",
            (unsigned long)cycles_a, (unsigned long)cycles_b, send_interval);

    SPSCQueue<CDCMessage, kQueueCapacity> queue;
    std::atomic<bool> producer_done{false};
    std::atomic<bool> consumer_done{false};

    std::atomic<uint64_t> sent{0};
    std::atomic<uint64_t> received{0};
    std::atomic<uint64_t> rollbacks{0};

    auto t_start = std::chrono::high_resolution_clock::now();

    /* ---- Thread A: Producer (fast clock domain) ---- */
    std::thread thread_a([&]() {
        uint64_t msg_count = 0;

        for (uint64_t cyc = 0; cyc < cycles_a; cyc++) {
            vt_a->eval_tick(vt_a->ctx);

            if ((cyc + 1) % send_interval == 0) {
                CDCMessage msg;
                msg.timestamp = cyc + 1;
                msg.payload   = vt_a->get_output
                    ? vt_a->get_output(vt_a->ctx, out_port_a) : 0;
                msg.signal_id = out_port_a;
                msg.flags     = 0;

                /* Try to push; abort if consumer is done */
                while (!queue.try_push(msg)) {
                    if (consumer_done.load(std::memory_order_acquire)) {
                        goto producer_exit;
                    }
                }
                msg_count++;
            }
        }

    producer_exit:
        fprintf(stderr, "CDC Thread A: done (%lu msgs sent)\n",
                (unsigned long)msg_count);
        sent.store(msg_count, std::memory_order_release);
        producer_done.store(true, std::memory_order_release);
    });

    /* ---- Thread B: Consumer (slow clock domain) ---- */
    std::thread thread_b([&]() {
        uint64_t msg_count = 0;
        uint64_t rb_count = 0;

        auto take_snap = [&]() -> void* {
            if (vt_b->snapshot)
                return vt_b->snapshot(vt_b->ctx);
            return nullptr;
        };
        auto restore_snap = [&](void* snap) {
            if (vt_b->restore && snap)
                vt_b->restore(vt_b->ctx, snap);
        };
        auto free_snap = [&](void* snap) {
            if (vt_b->free_snapshot && snap)
                vt_b->free_snapshot(snap);
        };
        auto get_ts = [](const CDCMessage& m) -> uint64_t {
            return m.timestamp;
        };

        CDCConsumer<CDCMessage, kQueueCapacity> consumer(
            queue, get_ts, take_snap, restore_snap, free_snap);

        consumer.take_snapshot();

        for (uint64_t cyc = 0; cyc < cycles_b; cyc++) {
            /* Non-blocking pop */
            CDCMessage msg;
            if (consumer.consume(msg)) {
                if (vt_b->set_input) {
                    vt_b->set_input(vt_b->ctx, in_port_b, msg.payload);
                }
                msg_count++;

                if (consumer.check_rollback()) {
                    rb_count++;
                    consumer.clear_rollback();
                    if (vt_b->set_input) {
                        vt_b->set_input(vt_b->ctx, in_port_b, msg.payload);
                    }
                }

                if (msg_count % snapshot_interval == 0) {
                    consumer.take_snapshot();
                }
            }

            vt_b->eval_tick(vt_b->ctx);
        }

        /* Drain remaining messages after main loop */
        CDCMessage drain;
        while (consumer.consume(drain)) {
            if (vt_b->set_input) {
                vt_b->set_input(vt_b->ctx, in_port_b, drain.payload);
            }
            msg_count++;
            if (consumer.check_rollback()) {
                rb_count++;
                consumer.clear_rollback();
            }
        }

        fprintf(stderr, "CDC Thread B: done (%lu msgs recv, %lu rollbacks)\n",
                (unsigned long)msg_count, (unsigned long)rb_count);
        received.store(msg_count, std::memory_order_release);
        rollbacks.store(rb_count, std::memory_order_release);

        /* Signal producer that consumer is finished */
        consumer_done.store(true, std::memory_order_release);
    });

    thread_a.join();
    thread_b.join();

    auto t_end = std::chrono::high_resolution_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t_end - t_start).count();

    result.messages_sent     = sent.load();
    result.messages_received = received.load();
    result.rollback_count    = rollbacks.load();
    result.elapsed_ms        = ms;
    result.success           = 1;

    fprintf(stderr, "CDC: done in %.2f ms (sent=%lu, recv=%lu, rb=%lu)\n",
            ms, (unsigned long)result.messages_sent,
            (unsigned long)result.messages_received,
            (unsigned long)result.rollback_count);

    return result;
}

} /* extern "C" */
