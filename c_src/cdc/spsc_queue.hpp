/*
 * Lock-Free SPSC Queue for Clock Domain Crossing
 *
 * Single-Producer Single-Consumer ring-buffer queue optimized for ARM64
 * weak memory ordering. Used by Sparkle's Time-Warping simulation to
 * pass timestamped messages between clock domain threads without mutexes.
 *
 * Design constraints (ARM64 / Apple M4 Max):
 *   - Precise memory ordering: release/acquire/relaxed (no seq_cst)
 *   - False sharing prevention: producer and consumer indices on separate cache lines
 *   - Power-of-2 capacity with bitwise AND wrap-around
 */

#pragma once

#include <atomic>
#include <array>
#include <cstdint>
#include <cstddef>
#include <type_traits>

namespace sparkle::cdc {

/* Message payload for CDC transfers */
struct CDCMessage {
    uint64_t timestamp;   /* Future timestamp from source clock domain */
    uint64_t payload;     /* Hardware signal value (up to 64-bit) */
    uint32_t signal_id;   /* Which signal this message refers to */
    uint32_t flags;       /* Reserved (rollback marker, etc.) */
};

/*
 * SPSCQueue<T, Capacity>
 *
 * Lock-free single-producer single-consumer ring buffer.
 * Capacity must be a power of 2. Indices are monotonically increasing
 * uint64_t values; wrap-around uses bitwise AND with (Capacity - 1).
 *
 * Cache line layout (each section on its own 64-byte line):
 *   [Producer]  write_idx_ (atomic) + cached_read_idx_ (local)
 *   [Consumer]  read_idx_  (atomic) + cached_write_idx_ (local)
 *   [Buffer]    array<T, Capacity>
 */
template <typename T, size_t Capacity>
class SPSCQueue {
    static_assert((Capacity & (Capacity - 1)) == 0,
                  "Capacity must be a power of 2");
    static_assert(Capacity >= 2, "Capacity must be at least 2");

    static constexpr size_t kMask = Capacity - 1;

    /* ---- Producer cache line ---- */
    alignas(64) std::atomic<uint64_t> write_idx_{0};
    uint64_t cached_read_idx_{0};
    char pad_producer_[64 - sizeof(std::atomic<uint64_t>) - sizeof(uint64_t)];

    /* ---- Consumer cache line ---- */
    alignas(64) std::atomic<uint64_t> read_idx_{0};
    uint64_t cached_write_idx_{0};
    char pad_consumer_[64 - sizeof(std::atomic<uint64_t>) - sizeof(uint64_t)];

    /* ---- Buffer ---- */
    alignas(64) std::array<T, Capacity> buffer_;

public:
    SPSCQueue() = default;

    /* Non-copyable, non-movable */
    SPSCQueue(const SPSCQueue&) = delete;
    SPSCQueue& operator=(const SPSCQueue&) = delete;
    SPSCQueue(SPSCQueue&&) = delete;
    SPSCQueue& operator=(SPSCQueue&&) = delete;

    /*
     * try_push — called ONLY by the producer thread.
     *
     * Returns true if the element was enqueued, false if the queue is full.
     *
     * Memory ordering:
     *   - Read cached_read_idx_ (thread-local, no atomic needed)
     *   - On cache miss, refresh from read_idx_ with relaxed load
     *   - Write element to buffer (no ordering needed — not yet visible)
     *   - Publish new write_idx_ with release store (makes element visible)
     */
    bool try_push(const T& item) {
        const uint64_t w = write_idx_.load(std::memory_order_relaxed);
        const uint64_t next_w = w + 1;

        /* Check if full using cached read index */
        if (next_w - cached_read_idx_ > Capacity) {
            /* Refresh cached read index */
            cached_read_idx_ = read_idx_.load(std::memory_order_relaxed);
            if (next_w - cached_read_idx_ > Capacity) {
                return false; /* Queue is full */
            }
        }

        buffer_[w & kMask] = item;

        /* Release: publishes the written element to the consumer */
        write_idx_.store(next_w, std::memory_order_release);
        return true;
    }

    /*
     * try_pop — called ONLY by the consumer thread.
     *
     * Returns true if an element was dequeued into `item`, false if empty.
     *
     * Memory ordering:
     *   - Read cached_write_idx_ (thread-local)
     *   - On cache miss, refresh from write_idx_ with acquire load
     *     (acquire: ensures we see the element the producer wrote)
     *   - Read element from buffer
     *   - Publish new read_idx_ with release store (frees the slot)
     */
    bool try_pop(T& item) {
        const uint64_t r = read_idx_.load(std::memory_order_relaxed);

        /* Check if empty using cached write index */
        if (r == cached_write_idx_) {
            /* Refresh cached write index */
            cached_write_idx_ = write_idx_.load(std::memory_order_acquire);
            if (r == cached_write_idx_) {
                return false; /* Queue is empty */
            }
        }

        item = buffer_[r & kMask];

        /* Release: frees the slot for the producer */
        read_idx_.store(r + 1, std::memory_order_release);
        return true;
    }

    /* Approximate size (racy but useful for diagnostics) */
    size_t size_approx() const {
        uint64_t w = write_idx_.load(std::memory_order_relaxed);
        uint64_t r = read_idx_.load(std::memory_order_relaxed);
        return static_cast<size_t>(w - r);
    }

    static constexpr size_t capacity() { return Capacity; }
};

} /* namespace sparkle::cdc */
