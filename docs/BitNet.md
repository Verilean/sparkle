# BitNet b1.58 ASIC Inference Engine
## Killer App: BitNet b1.58 ASIC Inference Engine

Sparkle ships with a **complete, formally verified BitNet b1.58 accelerator** — a production-grade ternary-weight neural network inference core targeting ASIC synthesis, written entirely in the Signal DSL. This is the world's first formally verified LLM inference hardware generated from a theorem prover.

### What It Does

Pure Signal DSL functions compose into a **complete BitNet SoC** — simulate directly or synthesize to SystemVerilog:

```lean
import IP.BitNet.SoC.Top

open Sparkle.Core.Signal
open Sparkle.IP.BitNet.SoC

-- Build a 2-layer, 4-dimension BitNet SoC as a Signal function
let cfg : SoCConfig := { archMode := .HardwiredUnrolled, nLayers := 2, dim := 4, ffnDim := 4 }
let x : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x10000)  -- 1.0 Q16.16
let result := bitNetSoCSignal cfg layerWeights layerScales x

-- Simulate: evaluate at any timestep
IO.println s!"Output at t=0: {result.atTime 0}"
```

### Dual-Architecture: Choose Your Trade-off

| | HardwiredUnrolled | TimeMultiplexed |
|---|:---:|:---:|
| **Area** | 202,566 cells | **99,020 cells** |
| **Latency** | **1 cycle** (combinational) | 12 cycles (1 per layer) |
| **Throughput** | **Maximum** | 1/12 of HW |
| **Source Lines** | 19,042 | **1,909** |
| **Use Case** | Ultra-low-latency | Area-constrained |

*Yosys 0.62 technology-independent synthesis. See `hw/synth/PPA_Report.md` for full breakdown.*

### 60+ Formally Verified Theorems

Every arithmetic operation in the RTL datapath is backed by machine-checked proofs:

```lean
-- Proves ReLU²(2.0) = 4.0 in Q16.16 fixed-point (checked by Lean kernel)
theorem relu_sq_two :
    reluSquared (BitVec.ofNat 32 0x20000) = BitVec.ofNat 32 0x40000 := by
  native_decide

-- Proves 48-bit × 32-bit scale product fits in 80 bits (no overflow)
theorem scale_prod_fits_80 : (2^47 - 1) * (2^31 - 1) < (2^79 : Nat) := by
  native_decide
```

**Proof categories:** Scale multiply (5), ReLU² (6), Residual add (6), Element multiply (6), Bit-width sufficiency (7), INT8 dot product (15), Attention bit-width (7), Softmax (8), Fixed-point spec (5).

### Architecture Overview

```
x[dim] ──► BitLinear(gate) ──► Scale ──► ReLU² ──┐
        ├─► BitLinear(up)   ──► Scale ────────────┤─► ElemMul ──► ResidualAdd ──► y[dim]
        └─► BitLinear(down) ──► Scale ◄───────────┘                    ↑
                                                                  x[dim] ─┘
```

- **Ternary weights**: {-1, 0, +1} encoded as 2-bit `i2_s` (zero-weight pruning eliminates ~35% of MACs)
- **Fixed-point datapath**: Q16.16 activations, 48-bit accumulators, Q8.24 scale factors
- **Binary adder tree**: Automatic bit-width propagation with configurable pipeline registers
- **LUT-based softmax**: 256-entry exp/reciprocal lookup tables as mux trees
- **Full attention pipeline**: QKV projection, INT8 dot product, softmax, score-V multiply, multi-head

### Golden Value Validation

RTL spec functions are validated against real model data from bitnet.cpp (16 tests):

```
=== RTL Golden Value Validation ===
  [PASS] Q16.16 round-trip       (cosine: 0.9999+)
  [PASS] reluSquared              (cosine: 0.999+)
  [PASS] elemMul                  (cosine: 0.999+)
  [PASS] residualAdd              (cosine: 0.9999+)
  [PASS] fixedPointScale          (cosine: 0.9999+)
  [PASS] quantizeToInt8           (exact match)
  [PASS] FFN forward pass         (cosine: 0.999+)
  [PASS] Attention score pipeline (exact match)
  [PASS] Softmax + weighted V sum
ALL TESTS PASSED
```

---

## Linux Driver (`/dev/bitnet0`) — Level 1a

The Sparkle RV32IMA SoC exposes a Level 1a BitNet MMIO peripheral at
`0x40000000–0x4000000F`. The Linux kernel can drive it through the
in-tree `sparkle-bitnet` platform driver (source: `linux-patches/`).
Userspace gets a `/dev/bitnet0` character device with this surface:

| Operation | Effect |
|-----------|--------|
| `write(fd, &u32, 4)` | Latch a Q16.16 activation into `0x40000004` |
| `read(fd, &u32, 4)`  | Read the combinational result from `0x40000008` |
| `ioctl(fd, BITNET_IOC_INFER, &u32)` | Atomic write+read pair (mutex-guarded) |
| `cat /sys/class/misc/bitnet0/status` | Read the v1a status register (always 0 in v1a) |

`BITNET_IOC_INFER` is defined in
`linux-patches/sparkle-bitnet.h` (UAPI header — copied to
`include/uapi/linux/sparkle-bitnet.h` by `apply.sh`).

### Why a built-in driver, not `.ko`

`firmware/opensbi/setup.sh` configures the kernel with
`CONFIG_MODULES=n` to fit the 32 MB DRAM budget. The
`sparkle-bitnet` driver therefore lives in `drivers/misc/`,
controlled by `CONFIG_SPARKLE_BITNET=y`. Updating the driver
requires a kernel rebuild (`rm /tmp/linux/arch/riscv/boot/Image &&
bash firmware/opensbi/setup.sh`).

### v1a scope (no DMA, no IRQ)

The peripheral is a **scalar** combinational accelerator — one 32-bit
Q16.16 word in, one 32-bit word out, settled the same cycle. There is
no internal state, no IRQ line, and no buffer. Multi-token loops are
driven entirely from userspace by repeating `write` / `read`. DMA and
IRQ are deliberately out of scope; they will be added when the
peripheral grows to Level 1b (sequential FSM, weight ROM, dim=2048,
24 layers). At that point, a `sparkle,bitnet-v1b` driver will sit
alongside the v1a one.

### Building + running

Prerequisite: enter the nix shell so the cross-toolchain
(`riscv64-unknown-linux-gnu-gcc`, `riscv32-none-elf-gcc`, `dtc`,
`cpio`) is on PATH. The repo's `shell.nix` includes everything
needed.

```bash
nix-shell

# 1. Build OpenSBI + the userspace test cpio + the Linux 6.6 image
#    with the sparkle-bitnet driver patched in. ~30 min on first run,
#    seconds on incremental rebuilds.
cd firmware/opensbi && bash setup.sh && cd ../..

# 2. Regenerate the JIT C++ for the SoC (only if you changed Lean
#    sources under IP/RV32 or IP/BitNet).
lake build IP.RV32.SoCVerilog

# 3. Boot Linux on the JIT runner; asserts on UART markers
#    "sparkle-bitnet … registered" and "BITNET PASS".
lake exe bitnet-linux-test
```

The end-to-end test (Layer 2 in the verification plan) reuses the same
8 golden vectors as `Tests/Integration/BitNetSoCTest.lean`:

```
in=0x00010000  out=0x00410000
in=0x00020000  out=0x02020000
in=0x00030000  out=0x06C30000
in=0x00040000  out=0x10040000
in=0x00080000  out=0x80080000
in=0x00000100  out=0x00000100
in=0x12345678  out=0x5AD1BC9A
in=0x00000000  out=0x00000000
```

If the Lean RTL spec, the bare-metal `bitnet_smoke/` smoke test, and
`/dev/bitnet0` ever produce different outputs for the same input, the
bug is in the integration glue (driver, DTS, MMIO routing) — not in
the BitNet pipeline itself.

### Userspace usage example

```c
#include <fcntl.h>
#include <stdint.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <linux/sparkle-bitnet.h>

int main(void) {
    int fd = open("/dev/bitnet0", O_RDWR);
    uint32_t v;

    /* Method 1: write/read pair. */
    v = 0x00010000u;            /* Q16.16 = 1.0 */
    write(fd, &v, 4);
    read(fd, &v, 4);
    printf("BitNet(1.0) = 0x%08x\n", v);

    /* Method 2: atomic ioctl (mutex-guarded against other openers). */
    v = 0x00020000u;
    ioctl(fd, BITNET_IOC_INFER, &v);
    printf("BitNet(2.0) = 0x%08x\n", v);

    close(fd);
}
```

For 1000-token inference loops just call `write`/`read` (or `ioctl
INFER`) 1000 times — each call moves 4 bytes across the kernel
boundary, well below the cost of a syscall, and with no IRQ wait.

---

## Bug investigation: 9d0704e "out = input" symptom

The `boot.S` self-test in commit `9d0704e` initially reported the
BitNet peripheral returning the input value instead of `ffn(input)`.
A formal LTL-based investigation was done to localize the bug.

**Result**: the Sparkle SoC is **correct**. All four LTL premises
(input-side cycle-N+1 update, K-cycle preservation, combinational
FFN output, MMIO read-mux decode) hold in the runtime trace. The
original symptom was a probe / firmware-side observation artifact.

See [`BitNet_LTL_Investigation.md`](BitNet_LTL_Investigation.md)
for the full postmortem, including the 4-premise framework, the
proof catalog, the probe-bug discovery, and the empirical
acceptance test.

---
