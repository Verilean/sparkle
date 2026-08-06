# Sparkle HDL

[![Build](https://github.com/Verilean/sparkle/actions/workflows/build.yml/badge.svg)](https://github.com/Verilean/sparkle/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**Write hardware in Lean 4. Prove it correct. Generate Verilog.**

A type-safe hardware description language that brings dependent types and
theorem proving to hardware design.

**Live docs & benchmarks:** the project publishes three hosted pages at
[verilean.github.io/sparkle](https://verilean.github.io/sparkle/):

- 📘 [**Tutorial (JupyterLite)**](https://verilean.github.io/sparkle/tutorial/) —
  the multi-chapter beginner course, runnable in-browser via xeus-lean.
  *(Known issue: some environments fail to boot the Lean kernel or load Sparkle;
  when that happens, read the rendered notebooks under
  [`docs/tutorial/Notebooks/`](docs/tutorial/Notebooks/) or use the
  Docker path in [Quick Start](#quick-start) below.)*
- 🔎 [**API reference (doc-gen4)**](https://verilean.github.io/sparkle/api/) —
  fully cross-linked documentation for every public definition, generated
  from the source with `lake build Sparkle:docs`.
- 📈 **Benchmarks** — CI-driven history of the RV32 JIT vs Verilator numbers:
  [RV32 SoC](https://verilean.github.io/sparkle/dev/rv32-bench/) ·
  [LiteX PicoRV32](https://verilean.github.io/sparkle/dev/litex-bench/) ·
  [Multi-core (8-thread)](https://verilean.github.io/sparkle/dev/multicore-bench/)

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

### Compute accelerators & CPUs

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**BitNet b1.58**](docs/ip-catalog/BitNet.md) | Formally verified LLM inference accelerator. Ternary weights, Q16.16 datapath, dual architecture (1-cycle vs 12-cycle). Standalone [FPGA fit + LTL investigation](docs/ip-catalog/BitNet_FPGA_Status.md) | 60+ theorems | Full | 202K / 99K cells |
| [**YOLOv8n-WorldV2**](docs/ip-catalog/YOLOv8.md) | Open-vocabulary object detection. INT4/INT8 quantized, 15 modules, CLIP text embeddings | Golden validation | Full | Backbone + Neck + Head |
| [**RV32IMA SoC**](docs/ip-catalog/RV32.md) | RISC-V CPU — boots Linux 6.6.0. 4-stage pipeline, Sv32 MMU, UART, CLINT. JIT at 14.2M cyc/s (1.63x Verilator). 102 formal proofs | 102 theorems | Full | 122 registers |
| [**SV→Sparkle Transpiler**](docs/ip-catalog/RV32.md#sv-transpiler) | Parse Verilog → JIT simulation. LiteX SoC at 18.1M cyc/s (1.72x Verilator). Verified reverse synthesis (2.14x speedup, zero sorry). 8-core parallel 11.9x Verilator. Timer oracle 9,900x. `OracleReduction` type class, 44 tests | 20+ theorems | JIT | 44 tests |

### [Networking stack](docs/ip-catalog/Networking.md) (new — PR #66)

Full UART → SLIP → IPv4 → TCP → HTTP round-trip, live on Tang Nano 50K.
`lake exe usb-webserver-jit-test` runs a GET request end-to-end in seconds.
See [`docs/ip-catalog/Networking.md`](docs/ip-catalog/Networking.md) for
the full layer-stack breakdown, bring-up notes, and sim entry points.

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**UART / SLIP**](IP/Net/UART.lean) | 8-N-1 UART RX/TX (configurable `bitDiv`) + RFC 1055 SLIP framer/deframer. Bring-up doc for Tang Nano 50K | — | Full | LUT 2% |
| [**IPv4 / ARP / ICMP**](IP/Net/IPv4.lean) | RFC 791 IPv4 parser + emitter, ARP requester + responder, ICMP echo. Byte-exact against reference | 5+ theorems | Full | iverilog round-trip |
| [**TCP**](IP/Net/TCP.lean) | Header + connection state machine + loopback. Includes retransmit / dup-ACK path | 3 theorems | Full | Cycle-accurate sim |
| [**HTTP/1.0**](IP/Net/HTTP.lean) | Emitter + parser + iverilog loopback (`gotRequest` at cycle 48 in sim) | — | Full | GET/POST |
| [**USB Web server**](IP/Net/UsbWebServer.lean) | End-to-end pipeline (UART→SLIP→IPv4→TCP→HTTP and back).  Emits `HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!` on any `GET` | — | Full | Tang Nano 50K, LUT 2%, BRAM 0% |
| [**memcached ASCII server**](IP/Net/MemcachedServer.lean) | Tier-1 (`get` / `set` / `add` / `delete`, key ≤ 8 B / value ≤ 16 B), BRAM-backed KV store + byte-stream FSM. Byte-exact against Lean reference oracle | 2 theorems | Full | LUT 1% / BRAM 25% / Fmax ≈ 57 MHz |
| [**Ethernet framing**](IP/Net/Ethernet.lean) | MAC framer + RX / TX header extract + payload streaming.  DMAC / SMAC / EtherType recovery cycle-accurate | — | Full | iverilog round-trip |
| [**CRC32**](IP/Net/CRC32.lean) | Bit-serial IEEE 802.3 CRC-32 engine.  Reference vs HW parity checked in `crc32-jit-test` | — | Full | 1 byte / cycle |

### Control & estimation (new — PR #109)

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**Control suite**](docs/ip-catalog/Control.md) | PID (anti-windup), LQR, IIR biquads at swept precisions, steady-state Kalman + H∞ (same RTL, different constants), time-varying Kalman with on-chip Riccati + width-generic Q divider | ℝ Lyapunov / ISS / dissipation certificates transported to fixed point (Mathlib sidecar `proofs/`, zero `sorry`) | Full (+ iverilog & JIT co-sim) | Tutorial [Ch 12](docs/tutorial/md/Ch12_ControlPrecision.md) |

The stability story: design over ℝ, prove `V(x⁺) ≤ ρ·V(x)` with Mathlib,
treat quantization as a bounded disturbance (ISS), and get an unbounded
kernel-checked ultimate bound on the *integer* datapath — plus the
counterexample (a naively quantized resonator whose emitted Verilog sustains
a period-6 limit cycle).  Precision selection is a theorem
(`Vbound f = c/4^f`; 13 fractional bits is exactly the threshold for the demo
budget).  The ℝ⇒Float falsification front-end (`retypelab/`, via
[retype](https://github.com/Verilean/retype)) kills wrong certificate
candidates in milliseconds before any `nlinarith` time is spent.

### Bus & interconnect

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**AXI4-Lite Bus**](docs/ip-catalog/RV32.md) | Verified AXI4-Lite slave/master. Protocol compliance (valid persistence, deadlock-free), synthesizable | 14 theorems | Full | 23 sim tests |
| [**AXI4 Full**](IP/Bus/AXI4/) | Multi-beat burst read/write + interleaving | — | Full | tested against RV32 SoC |
| [**PCIe TLP**](IP/Bus/PCIe.lean) | Header emit + parse (Memory Read/Write, config space) + HFT loopback structural check | — | Full | 12-byte TLP round-trip |
| [**CAN / CAN-FD / CANopen / DroneCAN**](IP/Bus/CAN.lean) | Automotive bus stack (bit-stuffing, CRC, arbitration, error frames).  DroneCAN HW node included | — | Full | serial-bus / avionics-bus tests |
| [**LIN / I²C / SPI**](IP/Bus/LIN.lean) | Master + slave HW for the common embedded serial protocols | — | Full | `serial-bus-test` |
| [**SBUS / CRSF**](IP/Bus/SBUS.lean) | Radio-control receiver protocols (drone control links) | — | Full | drone bring-up |
| [**MIL-STD-1553B**](IP/Bus/MIL1553.lean) | Avionics dual-redundant bus (Manchester encode/decode, RT/BC/BM) | — | Full | `avionics-bus-test` |

### Crypto & wallets

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**AES / AES-GCM / GHASH**](IP/Crypto/AES.lean) | AES-128/192/256 + GCM AEAD + hardware GHASH.  Byte-exact against NIST test vectors | — | Full | `ghash-hw-test`, hardware GF(2¹²⁸) |
| [**SHA-256 / SHA-512 / Keccak-256**](IP/Crypto/SHA256.lean) | Byte-exact hash primitives + HW pipeline (SHA-256) | — | Sim + HW SHA-256 | NIST vectors |
| [**Ed25519 / X25519**](IP/Crypto/Ed25519Sign.lean) | Ed25519 sign/verify + X25519 scalar mult (RFC 7748). Field theorems | 5+ theorems | Sim + **HW signer** | RFC 8032 vectors |
| [**P-256 / secp256k1 ECDSA**](IP/Crypto/P256ECDSA.lean) | NIST P-256 + secp256k1 ECDSA (Bitcoin/Ethereum curve) | — | Sim + **HW signer** | wycheproof |
| [**HW signers (secp256k1 / BLS12-381 / Ed25519)**](IP/Crypto/Secp256k1ECDSAHW.lean) | Security-focused HW **signing** datapaths — key never leaves the chip.  Bit-serial field mul → projective/extended point-op → scalar-mul ladder → sign FSM; Fp381 Montgomery mul (blst `mul_mont_384` analogue).  Hash/nonce are host inputs | — | Full (sim + `#synthesizeVerilog`) | secp256k1 matches SEC1/RFC-6979 vector; BLS G2 sign; Ed25519 RFC 8032 |
| [**ECDSA signing demo (Tang Nano 50K)**](docs/ip-catalog/EcdsaSignDemo.md) | Flashable top-level: send `d‖k‖z` (96 B) over UART, get `r‖s` (64 B) back.  Full closed-loop secp256k1 signer + UART.  ≈ 67 ms/sign @ 27 MHz | — | Full (`#synthesizeVerilog`) | Tang Nano 50K; dataflow matches SEC1/RFC-6979 |
| [**Policy-enforcing signer (Tang Nano 50K)**](docs/ip-catalog/PolicySignDemo.md) | Security device: hashes the tx **on-chip** (Keccak-256 sponge), checks recipient/amount against an **on-chip policy** sliced from the same bytes, signs **only if policy passes** — else returns a reject byte.  Key never leaves the chip AND a compromised host can't sign attacker-chosen tx | — | Full (`#synthesizeVerilog` + iverilog) | Tang Nano 50K; dataflow matches Keccak-256 / SEC1 / policy |
| [**RSA-PSS**](IP/Crypto/RSAPSS.lean) | RSA signature verify (PKCS #1 v2.2 PSS) | — | Sim | webPKI test set |
| [**HKDF**](IP/Crypto/HKDF.lean) | RFC 5869 HKDF extract + expand (SHA-256 backend) | — | Sim | TLS 1.3 dep |
| [**Ethereum wallet stack**](IP/Crypto/EthWallet.lean) | BIP-32 / BIP-39 seed + HD wallet, RLP encoder, EIP-1559 tx, ERC-20 ABI | — | Sim | Byte-exact vs reference clients |

### Security (TLS 1.3)

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**TLS 1.3**](IP/TLS/Client.lean) | Full TLS 1.3 client + server (record layer, handshake, key schedule, X.509 verify).  AES-128-GCM + Ed25519 cipher suite | 3 theorems | Sim | Interop vs OpenSSL fixtures |
| [**HTTPS demo**](IP/Net/HFTOverTLS.lean) | HFT-over-TLS transport (TCP + TLS + custom framing) | — | Sim | Loopback demo |

### Zero-knowledge

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**Merkle tree / polynomial commitment**](IP/Crypto/Merkle.lean) | Merkle-tree opening + polynomial evaluation with 8 honest openings round-trip | — | Sim | `polynomial-test`, `merkle-test` |
| [**Mini-STARK verifier**](IP/Crypto/MiniSTARK.lean) | STARK proof verify (Goldilocks field, FRI, low-degree extension) | — | Sim | 8-opening verifier |
| [**Goldilocks field**](IP/Crypto/Goldilocks.lean) | p = 2⁶⁴ − 2³² + 1 field arithmetic | — | Sim | STARK dep |

### Video

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**H.264 Codec**](docs/ip-catalog/H264.md) | Baseline Profile encoder + decoder. Hardware MP4 muxer produces playable files. CAVLC now byte-exact vs Lean reference for all 4×4 blocks (fixed in PR #66) | 15+ theorems | Full | 709-byte MP4 output |

### Verified infrastructure

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| [**CDC Infrastructure**](docs/architecture/CDC.md) | Lock-free multi-clock simulation. SPSC queue (210M ops/sec), rollback, 8-core parallel runner (3.87x on 8 cores).  Since PR #66, dispatches through the JIT vtable — no more per-symbol dlsym (`Issue #70`) | 12 theorems | C | N-thread parallel |
| [**Drone SoC (bring-up)**](docs/ip-catalog/Drone_SoC_Status.md) | Multi-IP drone/humanoid SoC status pages (DroneCAN + SBUS + CRSF wired to RV32) | | Status page | — |
| [**Humanoid SoC (bring-up)**](docs/ip-catalog/Humanoid_SoC_Status.md) | Sensor / actuator bus fabric for humanoid platform | | Status page | — |

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

**Prerequisites:** a **glibc ≥ 2.34** Linux (Ubuntu 22.04+,
Debian 12+, Fedora 35+), macOS, or WSL2.  Older systems
(e.g. Ubuntu 20.04, glibc 2.31) fail during `lake build` with

```
.../bin/cadical: /lib/x86_64-linux-gnu/libc.so.6: version `GLIBC_2.34' not found
```

— `cadical` is the SAT solver bundled with the Lean 4.28
toolchain (used by `bv_decide` / `omega`), and it is linked
against glibc 2.34.  This is a Lean-toolchain requirement, not a
Sparkle one; upgrade the OS (or use the Docker path in the
tutorial) if you hit it.

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

- **Hosted (built by CI, always up-to-date with `main`):**
  - 📘 [Tutorial (JupyterLite)](https://verilean.github.io/sparkle/tutorial/) —
    in-browser, xeus-lean kernel.  *(Boot issues on some machines — see
    "Live docs & benchmarks" at the top of this README for the fallback.)*
  - 🔎 [API reference](https://verilean.github.io/sparkle/api/) —
    doc-gen4 site covering every public definition.
  - 📈 Benchmarks —
    [RV32 SoC](https://verilean.github.io/sparkle/dev/rv32-bench/),
    [LiteX PicoRV32](https://verilean.github.io/sparkle/dev/litex-bench/),
    [Multi-core 8-thread](https://verilean.github.io/sparkle/dev/multicore-bench/).
- **Generate the API reference locally with doc-gen4:**


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

### Hitting an unhelpful `#synthesizeVerilog` error?

The IR elaborator's error surface is still rough.  Two messages in
particular bury the real cause:

```
Cannot synthesise <name>: not inlinable and not a hardware module
Sub-module synthesis failed for <name> (tagged @[hardware_module])
```

Both are emitted from `Sparkle/Compiler/Elab.lean:handleDefinitionUnfold`
where an inner `MetaM` exception is swallowed by a `catch _`.  When
this hits you, follow this workflow:

1. **Look at the error in context.**  If `<name>` is one of
   `Sparkle.Core.runCircuitH`, `Bind.bind`, `Pure.pure`,
   `Sparkle.Core.Signal.bundle*`, the elaborator's `unfoldDefinition?`
   peeled the surface `def` but choked on something inside your DSL
   body (typeclass projection, an Applicative lift, a multi-arg
   lambda).  See
   [`docs/reference/Troubleshooting_Synthesis.md`](docs/reference/Troubleshooting_Synthesis.md)
   §"Synthesis Compiler Patterns" for the patterns the elaborator
   *does* accept — common rewrites are listed in §"Fix patterns".

2. **Get the real inner error.**  Temporarily change the two
   `catch _ =>` clauses near `Sparkle/Compiler/Elab.lean:1620` and
   `:1631` to `catch e => ... e.toMessageData.toString` so the
   inner `throwError` propagates into the outer message.  Most
   "not inlinable" failures resolve to something specific like a
   missing pattern-match arm, an unhandled operator, or a
   `BitVec.zeroExtend`-style call the IR doesn't speak.  Revert
   the change before committing — leaving raw `MessageData` in
   the user-facing error breaks the existing test fixtures.

3. **Found a new pattern that fails?**  Add a one-liner to
   [`docs/reference/Troubleshooting_Synthesis.md`](docs/reference/Troubleshooting_Synthesis.md)
   under the appropriate "NOT supported" / "Fix patterns" bullet
   so the next contributor sees it before they re-derive the
   problem.  Two recent examples of the kind of entry to add are
   "multi-arg user-defined function via `f <$> a <*> b`" (rewrite
   the body to use Signal-native operators directly) and
   "`(fun v => 0#m ++ v ++ 0#n)`" (split into a chain of `++`).

4. **If the elaborator itself should learn this case**, file a
   followup under `docs/known-issues/TODO.md` §"Compiler / IR"
   so the rough surface can be filed down rather than papered
   over.  The shipped error today is the cap on how fast a new
   contributor can debug their first synthesisable circuit, so
   work that reduces it is high-leverage.

The `Sparkle/IP/Net/CRC32.lean` development is a worked example:
the byte-feed engine first failed with the generic "Sub-module
synthesis failed" message, the inner error revealed
`Cannot synthesise runCircuitH`, and the fix turned out to be
rewriting `crc32Step <$> crc <*> byte` (a user-defined 2-arg
function lifted through Applicative) as a Signal-native chain
of `^^^`/`&&&`/`>>>`/`++`/`-`.

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
- Golden-reference cycle-accurate simulation via
  [Verilator](https://www.veripool.org/verilator/) — used both
  as the CI co-sim reference and as the "if the JIT disagrees,
  the JIT is wrong" arbiter throughout the test suite.
- In-browser Lean via [xeus-lean](https://github.com/xeus/xeus-lean)
  and [JupyterLite](https://jupyterlite.readthedocs.io/) —
  powers the hosted tutorial notebooks.
- Verilog toolchain integration via
  [iverilog](https://steveicarus.github.io/iverilog/) (round-trip
  checks) and [Yosys](https://yosyshq.net/yosys/) (used in
  Ch 8 of the tutorial for equivalence checking / FPGA fit).

## Community

- **Discord**: [https://discord.gg/94Xueve8WD](https://discord.gg/94Xueve8WD)
  — design discussion, weekly progress threads, beginner Q&A.
