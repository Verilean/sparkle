# Clock Domain Crossing (CDC)
## Clock Domain Crossing (CDC) — Lock-Free Multi-Clock Simulation

Sparkle includes a **lock-free CDC infrastructure** for Time-Warping simulation across multiple clock domains. Each domain runs on its own thread, connected by a high-performance SPSC queue — no mutexes required.

### Architecture

```
Lean (JIT.runCDC)
  ▼
sparkle_jit.c ──dlopen──▶ cdc_runner.so (C++20)
                              │
                   ┌──────────┴──────────┐
              Thread A (100MHz)    Thread B (50MHz)
              eval_tick + push     pop + set_input + eval_tick
                   └─── SPSC Queue ───┘
```

### Key Features

- **Lock-free SPSC queue** (`c_src/cdc/spsc_queue.hpp`): ARM64-optimized, 210M ops/sec, false-sharing prevention
- **Rollback mechanism** (`c_src/cdc/cdc_rollback.hpp`): Detects timestamp inversions, restores snapshots — queue indices never rolled back
- **12 formal proofs** (`Sparkle/Verification/CDCProps.lean`): SPSC safety, rollback guarantee, queue index isolation — all proven, no `sorry`
- **JIT integration**: `JIT.runCDC` runs two domains on separate threads from Lean via dlopen bridge

### Multi-Clock E2E Test

```bash
# Build and run
make -C c_src/cdc           # build cdc_runner.so
lake exe cdc-multi-clock-test
# ╔══════════════════════════════════════════════════╗
# ║   Sparkle CDC Multi-Clock JIT Simulation Test   ║
# ╠══════════════════════════════════════════════════╣
# ║  DomainA: 8-bit counter  (100MHz, 200K cycles)  ║
# ║  DomainB: accumulator    ( 50MHz, 100K cycles)  ║
# ╚══════════════════════════════════════════════════╝
#   Messages sent:     76421
#   Messages received: 75397
#   Rollbacks:         0
# *** CDC Multi-Clock Test: PASS ***
```

---
