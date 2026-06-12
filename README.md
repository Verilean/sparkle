# Sparkle HDL

[![Build](https://github.com/Verilean/sparkle/actions/workflows/build.yml/badge.svg)](https://github.com/Verilean/sparkle/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**Write hardware in Lean 4. Prove it correct. Generate Verilog.**

A type-safe hardware description language that brings dependent types and
theorem proving to hardware design.

**Quick Start:** the multi-chapter [tutorial](docs/tutorial/) walks
from "hello counter" through Verilog generation, proofs, and FPGA
bring-up.  Run it in Docker, in your browser via xeus-lean's
JupyterLite, or read the rendered notebooks directly on GitHub.
For the full Signal DSL syntax, see
[docs/reference/SignalDSL_Syntax.md](docs/reference/SignalDSL_Syntax.md).

**Try it in the browser:** Sparkle plugs into
[xeus-lean](https://github.com/Verilean/xeus-lean)'s WASM kernel
via the [`EXTRA_WASM_DIRS`](https://github.com/Verilean/xeus-lean#extending-the-kernel-with-your-own-lean-lib)
extension point.  See [`tools/wasm/`](tools/wasm/) for the
staging-builder script.  `#synthesizeVerilog`, `#showVerilog`, and
pure `Signal.atTime` simulation all work under WASM; the native JIT
path (`Sparkle.Core.JIT.compileAndLoad`) is stubbed and only
available from a native `lake exe` build.

## The Sparkle Way: Verification-Driven Design

1. **Write a pure Lean spec** — define behaviour as pure functions.
2. **Prove properties** — safety, liveness, fairness via Lean's theorem prover.
3. **Implement via Signal DSL** — express the same logic using `Signal`
   combinators.
4. **Generate Verilog** — `#synthesizeVerilog` / `#writeVerilogDesign` emit
   SystemVerilog.

See [docs/reference/Verification_Framework.md](docs/reference/Verification_Framework.md) for
patterns and a worked Round-Robin Arbiter example (10 formal proofs).

## IP Catalog

Sparkle ships with production-grade IP cores — each with pure Lean specs,
formal proofs, and synthesizable Signal DSL implementations.

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**BitNet b1.58**](docs/ip-catalog/BitNet.md) | Formally verified LLM inference accelerator. Ternary weights, Q16.16 datapath, dual architecture (1-cycle vs 12-cycle) | 60+ theorems | Full | 202K / 99K cells |
| [**YOLOv8n-WorldV2**](docs/ip-catalog/YOLOv8.md) | Open-vocabulary object detection. INT4/INT8 quantized, 15 modules, CLIP text embeddings | Golden validation | Full | Backbone + Neck + Head |
| [**RV32IMA SoC**](docs/ip-catalog/RV32.md) | RISC-V CPU — boots Linux 6.6.0. 4-stage pipeline, Sv32 MMU, UART, CLINT. JIT at 14.2M cyc/s (1.63x Verilator). 102 formal proofs | 102 theorems | Full | 122 registers |
| [**AXI4-Lite Bus**](docs/ip-catalog/RV32.md) | Verified AXI4-Lite slave/master. Protocol compliance (valid persistence, deadlock-free), synthesizable | 14 theorems | Full | 23 sim tests |
| [**SV→Sparkle Transpiler**](docs/ip-catalog/RV32.md#sv-transpiler) | Parse Verilog → JIT simulation. LiteX SoC at 18.1M cyc/s (1.72x Verilator). Verified reverse synthesis (2.14x speedup, zero sorry). 8-core parallel 11.9x Verilator. Timer oracle 9,900x. `OracleReduction` type class, 44 tests | 20+ theorems | JIT | 44 tests |
| [**H.264 Codec**](docs/ip-catalog/H264.md) | Baseline Profile encoder + decoder. Hardware MP4 muxer produces playable files. 14 modules | 15+ theorems | Full | 709-byte MP4 output |
| [**CDC Infrastructure**](docs/architecture/CDC.md) | Lock-free multi-clock simulation. SPSC queue (210M ops/sec), rollback, 8-core parallel runner (3.87x speedup). JIT.runCDC | 12 theorems | C++ | N-thread parallel |

---

## Why Sparkle?

```lean
-- Write this in Lean...
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.circuit do
    let count ← Signal.reg 0#8
    count <~ count + 1#8
    return count

#synthesizeVerilog counter
```

```systemverilog
// ...and get this Verilog
module counter (
    input  logic clk,
    input  logic rst,
    output logic [7:0] out
);
    logic [7:0] count;

    always_ff @(posedge clk) begin
        if (rst)
            count <= 8'h00;
        else
            count <= count + 8'h01;
    end

    assign out = count;
endmodule
```

**Three powerful ideas in one language:**

1. **Simulate** — cycle-accurate functional simulation with pure Lean functions.
2. **Synthesize** — automatic compilation to clean, synthesizable SystemVerilog.
3. **Verify** — formal correctness proofs using Lean's theorem prover.

## The Sparkle Advantage: Logical AND Physical Safety

Chisel + FIRRTL solve many *logical* hardware bugs (latches, comb loops) but
leave you fighting timing-closure with external linters. Sparkle gives you
both out of the box:

- **Logical Safety** — `Signal` enforces a strict DAG for combinational logic;
  feedback is only possible through explicit `Signal.register` /
  `Signal.loop`. Pattern-match exhaustiveness catches unhandled cases at
  compile time. Unintended latches are impossible by construction.
- **Physical / Timing Safety** — a built-in DRC pass (inspired by the STARC
  guidelines) enforces registered outputs so Static Timing Analysis is
  predictable and critical paths don't cross module boundaries.
- **Readable Verilog** — Sparkle's IR keeps a 1:1 structural correspondence
  with your Lean code. When the DRC flags a timing issue you can actually
  read the generated SV to fix it.

## Quick Start

```bash
git clone https://github.com/Verilean/sparkle.git
cd sparkle
lake build                                # ~5 min first time
lake env lean --run Examples/Counter.lean # smoke-test
```

A minimal register chain:

```lean
import Sparkle
open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- Three-cycle delay line, polymorphic over clock domains.
def registerChain {dom : DomainConfig}
    (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let d1 := Signal.register 0#8 input
  let d2 := Signal.register 0#8 d1
  Signal.register 0#8 d2

#synthesizeVerilog registerChain
```

For the full tour — VCD waveforms, JIT simulation, formal equivalence
commands, clock-domain crossings, and the synthesizable subset of Lean —
work through [`docs/tutorial/`](docs/tutorial/).

## Key Features

- **Cycle-accurate simulation** — the same semantics as the emitted Verilog,
  runnable from Lean with `#eval` and `sample`.
- **Automatic Verilog generation** — `#synthesizeVerilog` handles clocks,
  resets, register inference, bit-width checking, and feedback-loop
  resolution.
- **Formal verification ready** — `bv_decide` + `simp` + `Temporal.lean`
  (LTL) for safety/liveness/fairness proofs directly against Signal code.
- **One-line equivalence checks** — `#verify_eq`, `#verify_eq_at`,
  `#verify_eq_git` auto-generate theorems and discharge them with
  `bv_decide`. See `docs/tutorial/notebooks/ch07-equivalence.ipynb`.
- **Signal DSL with imperative feel** — `Signal.circuit` macro gives you
  `<~` register assignment without losing the functional semantics.
- **Vector / array types** — `HWVector α n` with compile-time-checked
  indexing for register files.
- **Memory primitives** — `Signal.memory` generates synchronous-write /
  registered-read BRAM-style RAMs.
- **Technology library support** — `primitiveModule` wraps vendor cells
  (SRAMs, PLLs, transceivers) into the type system.
- **JIT simulation** — `sim!` / `#sim` compile to native C++ via dlopen
  for 10–100× faster simulation than the Lean interpreter.
- **CDC-aware multi-domain simulation** — `runSim` auto-selects the fastest
  backend (single-domain or lock-free SPSC queue between threads).
- **Temporal logic** — LTL operators (`always`, `eventually`, `next`,
  `Until`) with induction principles, enabling cycle-skipping optimisation.

Each feature is exercised in the tutorial or one of the IPs; see the
links in the IP Catalog above.

## Examples

```bash
# Core simulation + Verilog generation
lake env lean --run Examples/Counter.lean
lake env lean --run Examples/LoopSynthesis.lean
lake env lean --run Examples/SimpleMemory.lean

# The 16-bit Sparkle-16 CPU (ALU / RegisterFile / Core / ISA proofs)
lake env lean --run Examples/Sparkle16/Core.lean
lake env lean --run Examples/Sparkle16/ISAProofTests.lean

# Clock-domain crossing demo
lake env lean --run Examples/CDC/MultiClockSim.lean

# RV32IMA SoC, BitNet, YOLOv8, H.264 — run via the test suite
lake test

# Verilator: build the SoC and boot firmware
cd verilator && make build && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000
```

Each IP has a dedicated getting-started recipe in its own doc
([BitNet](docs/ip-catalog/BitNet.md), [RV32](docs/ip-catalog/RV32.md), [H264](docs/ip-catalog/H264.md),
[YOLOv8](docs/ip-catalog/YOLOv8.md), [CDC](docs/architecture/CDC.md)).

## Documentation

Generate the full API reference locally with doc-gen4:

```bash
lake -R -Kenv=dev build Sparkle:docs
open .lake/build/doc/index.html
```

Pointers to the hand-written docs:

- **Getting started / writing synthesizable code**
  - [docs/tutorial/](docs/tutorial/) — multi-chapter beginner course
  - [docs/reference/SignalDSL_Syntax.md](docs/reference/SignalDSL_Syntax.md) — full DSL reference
  - [docs/reference/Troubleshooting_Synthesis.md](docs/reference/Troubleshooting_Synthesis.md)
- **Verification**
  - [docs/reference/Verification_Framework.md](docs/reference/Verification_Framework.md) — VDD patterns
  - [Examples/TemporalLogicExample.md](Examples/TemporalLogicExample.md) — LTL usage
- **IP-specific docs**
  - [docs/ip-catalog/BitNet.md](docs/ip-catalog/BitNet.md) · [docs/ip-catalog/YOLOv8.md](docs/ip-catalog/YOLOv8.md)
  - [docs/ip-catalog/RV32.md](docs/ip-catalog/RV32.md) · [docs/ip-catalog/H264.md](docs/ip-catalog/H264.md)
  - [docs/architecture/CDC.md](docs/architecture/CDC.md)
- **Project meta**
  - [docs/CHANGELOG.md](docs/CHANGELOG.md) — release history
  - [docs/architecture/STATUS.md](docs/architecture/STATUS.md) — current capability matrix
  - [docs/known-issues/KnownIssues.md](docs/known-issues/KnownIssues.md)
  - [docs/known-issues/BENCHMARK.md](docs/known-issues/BENCHMARK.md)

## How It Works

```
┌──────────────────┐
│  Lean Signal DSL │   ===, &&&, |||, hw_cond, Coe
└──────┬───────────┘
       │
       ├──────────────┬──────────────────┬───────────────────┐
       ▼              ▼                  ▼                   ▼
┌─────────────┐ ┌────────────┐  ┌──────────────┐ ┌──────────────────┐
│ Simulation  │ │ JIT (FFI)  │  │  Verilator   │ │#synthesizeVerilog│
│  .atTime t  │ │ C++ dlopen │  │ .sv → C++    │ │  Lean → IR → DRC │
│  ~5K cyc/s  │ │ ~13.0M c/s │  │ ~11.1M c/s   │ │  → SystemVerilog │
│             │ │+oracle:1B+ │  │              │ │                  │
└─────────────┘ └────────────┘  └──────────────┘ └──────────────────┘
```

**Core abstractions:**

1. **Domain** — clock domain configuration (period, edge, reset).
2. **Signal** — stream-based hardware values, `Signal d α ≈ Nat → α`.
3. **BitPack** — type class for hardware serialisation.
4. **Module / Circuit** — IR for netlists.
5. **Compiler** — automatic Lean → IR translation via metaprogramming.

Type-safety example:

```lean
-- This won't compile — bit-width mismatch is a compile-time error.
def broken {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.register (0#16) (Signal.pure 0#16)  -- Error: expected BitVec 8

def fixed {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let wide : Signal dom (BitVec 16) := Signal.register 0#16 (Signal.pure 0#16)
  wide.map (BitVec.extractLsb' 0 8 ·)  -- ✓ explicit truncation
```

## Known Limitations

See [docs/reference/Troubleshooting_Synthesis.md](docs/reference/Troubleshooting_Synthesis.md)
and [docs/known-issues/KnownIssues.md](docs/known-issues/KnownIssues.md) for the current list of:

- Imperative syntax limitations (`<~` inside conditionals).
- Pattern matching on tuples in synthesizable contexts.
- `if`-then-else vs `Signal.mux` in Signal contexts.
- `Signal.loop` feedback rules.
- `bv_decide` hanging inside `lake build` on Lean 4.28 (interactive only).

## Testing

```bash
lake test
```

Runs Signal simulation, Verilog generation, vector / memory ops, temporal
logic, CPU ISA proofs, BitNet golden-value validation, RV32 firmware,
H.264 pipelines, YOLOv8 primitives, CDC queue stress, and the Verilator
co-simulation layer.

## Comparison with Other HDLs

| Feature | Sparkle | Clash | Chisel | Verilog |
|---------|---------|-------|--------|---------|
| Language | Lean 4 | Haskell | Scala | Verilog |
| Type System | Dependent Types | Strong | Strong | Weak |
| Simulation | Built-in | Built-in | Built-in | External tools |
| Formal Verification | **Native (Lean)** | External | External | None |
| Logical Safety (no latches / comb loops) | **By construction** | Partial | Via FIRRTL | None |
| Physical / Timing Safety (DRC) | **Built-in** | None | None | SpyGlass ($$$) |
| Generated Verilog Readability | **1:1 structural** | Readable | Obfuscated (FIRRTL) | N/A |
| Learning curve | High | High | Medium | Low |
| Proof integration | **Seamless** | Separate | Separate | N/A |

## Project Structure

```
sparkle/
├── Sparkle/      # Core library (Signal DSL, IR, Compiler, Backend, Verification)
├── IP/           # Verified IP cores (BitNet, YOLOv8, RV32, Drone, Humanoid, Video, Bus)
├── Examples/     # Runnable demos (Counter, Sparkle16 CPU, CDC, LoopSynthesis, …)
├── Tests/        # LSpec test suites for everything above
├── Tools/        # SVParser, verilog! / sim! macros, Signal DSL helpers
├── verilator/    # Verilator co-simulation backend for the RV32IMA SoC
├── firmware/     # RV32 firmware + OpenSBI + Linux device tree
├── c_src/        # C FFI libraries (loop memoization, JIT dlopen)
├── scripts/      # Tutorial syntax check + golden-value generators
├── docs/         # Hand-written docs (Tutorial, per-IP, KnownIssues, BENCHMARK)
└── lakefile.lean # Build configuration
```

## Contributing

Sparkle is an educational project demonstrating functional hardware
description, dependent types for hardware, theorem proving for
verification, and compiler construction / metaprogramming.

Contributions welcome — good first areas:

- Verified standard IP (parameterised FIFO, N-way arbiter, TileLink / AXI4
  interconnect) with formal proofs.
- FPGA tape-out flow examples.
- Additional IR optimisation passes.
- More tutorials and worked examples.

## Roadmap

Completed phases live in [docs/CHANGELOG.md](docs/CHANGELOG.md).

**Next up:**

- **Verified Standard IP — Parameterised FIFO** — generic depth / width FIFO.
- **Verified Standard IP — N-way Arbiter** — generalise the 2-client
  round-robin arbiter to N clients.
- **Verified Standard IP — TileLink / AXI4 Interconnect** — full AXI4
  (bursts, IDs) and TileLink.
- **GPGPU / Vector Core** — apply the VDD framework to highly concurrent,
  memory-bound accelerator architectures.
- **FPGA Tape-out Flow** — end-to-end examples deploying Sparkle-generated
  Linux SoCs to physical FPGAs.

## Author

**Junji Hashimoto** — Twitter / X: [@junjihashimoto3](https://x.com/junjihashimoto3)

## License

Apache License 2.0 — see [LICENSE](LICENSE).

## Acknowledgments

- Inspired by [Clash HDL](https://clash-lang.org/)
- Built with [Lean 4](https://lean-lang.org/)
