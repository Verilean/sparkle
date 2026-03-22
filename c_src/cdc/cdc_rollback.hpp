/*
 * CDC Rollback Mechanism for Time-Warping Simulation
 *
 * Wraps the SPSC queue consumer side with timestamp inversion detection
 * and snapshot-based state restoration. When a message arrives with a
 * timestamp earlier than the consumer's local time, the consumer:
 *   1. Sets the atomic rollback flag
 *   2. Restores simulation state from the most recent snapshot
 *   3. Updates local_time to the message's timestamp
 *   4. Continues consuming — queue indices are NEVER rolled back
 *
 * The queue's read/write indices are architecturally separate from
 * simulation state, ensuring rollback cannot break inter-thread sync.
 */

#pragma once

#include "spsc_queue.hpp"
#include <functional>

namespace sparkle::cdc {

/*
 * CDCConsumer<T, Capacity>
 *
 * Consumer-side wrapper with rollback detection.
 * Snapshot functions are injected via constructor to decouple from JIT.
 */
template <typename T, size_t Capacity>
class CDCConsumer {
public:
    using Queue = SPSCQueue<T, Capacity>;
    using SnapshotTakeFn   = std::function<void*()>;
    using SnapshotRestoreFn = std::function<void(void*)>;
    using SnapshotFreeFn   = std::function<void(void*)>;
    using TimestampExtractFn = std::function<uint64_t(const T&)>;

    CDCConsumer(Queue& queue,
                TimestampExtractFn get_timestamp,
                SnapshotTakeFn take_snapshot,
                SnapshotRestoreFn restore_snapshot,
                SnapshotFreeFn free_snapshot)
        : queue_(queue)
        , get_timestamp_(std::move(get_timestamp))
        , take_snapshot_(std::move(take_snapshot))
        , restore_snapshot_(std::move(restore_snapshot))
        , free_snapshot_(std::move(free_snapshot))
    {}

    ~CDCConsumer() {
        if (snapshot_ && free_snapshot_) {
            free_snapshot_(snapshot_);
        }
    }

    /* Non-copyable */
    CDCConsumer(const CDCConsumer&) = delete;
    CDCConsumer& operator=(const CDCConsumer&) = delete;

    /*
     * Take a snapshot of the current simulation state.
     * Should be called periodically by the consumer thread.
     */
    void take_snapshot() {
        if (snapshot_ && free_snapshot_) {
            free_snapshot_(snapshot_);
        }
        snapshot_ = take_snapshot_();
        snapshot_time_ = local_time_;
    }

    /*
     * Consume one message from the queue.
     *
     * Returns true if a message was consumed. If a timestamp inversion
     * is detected (msg.timestamp < local_time_), the rollback flag is
     * set and simulation state is restored from the latest snapshot.
     *
     * The queue read index always advances — it is never rolled back.
     */
    bool consume(T& item) {
        if (!queue_.try_pop(item)) {
            return false;
        }

        uint64_t msg_time = get_timestamp_(item);

        if (msg_time < local_time_) {
            /* Timestamp inversion detected — trigger rollback */
            rollback_flag_.store(true, std::memory_order_release);
            rollback_count_++;

            if (snapshot_ && restore_snapshot_) {
                restore_snapshot_(snapshot_);
            }

            local_time_ = msg_time;
        } else {
            local_time_ = msg_time;
        }

        return true;
    }

    /* Check and clear rollback flag (called by producer or monitor) */
    bool check_rollback() {
        return rollback_flag_.load(std::memory_order_acquire);
    }

    void clear_rollback() {
        rollback_flag_.store(false, std::memory_order_release);
    }

    uint64_t local_time() const { return local_time_; }
    uint64_t rollback_count() const { return rollback_count_; }
    bool has_snapshot() const { return snapshot_ != nullptr; }

private:
    Queue& queue_;
    TimestampExtractFn get_timestamp_;
    SnapshotTakeFn take_snapshot_;
    SnapshotRestoreFn restore_snapshot_;
    SnapshotFreeFn free_snapshot_;

    alignas(64) std::atomic<bool> rollback_flag_{false};
    uint64_t local_time_{0};
    uint64_t rollback_count_{0};
    void* snapshot_{nullptr};
    uint64_t snapshot_time_{0};
};

} /* namespace sparkle::cdc */
