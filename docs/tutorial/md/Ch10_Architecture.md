
# Chapter 10 — Sparkle Architecture

The previous nine chapters used Sparkle from the outside —
writing designs, synthesising, proving.  This chapter looks
at the **insides**: how a Lean source file becomes
SystemVerilog, when to choose JIT simulation versus
Verilator, where to extend the compiler, and the cheat-sheet
of macros / commands you'll reach for in real work.

It's a tour, not a tutorial — no exercises, just orientation.

```lean
import Sparkle
import Display

namespace Notebooks.Ch10

```
## 10.1 The compilation pipeline

```
  .lean source (Signal DSL)
         │
         │  Sparkle/Compiler/Elab.lean
         │  (Lean metaprogramming → IR)
         ▼
   Signal IR  (Sparkle/IR/AST.lean)
         │
         ├──→ Sparkle/Backend/Verilog.lean → SystemVerilog (Yosys, Vivado, ...)
         ├──→ Sparkle/Backend/CppSim.lean  → C++ JIT (Verilator-class speed)
         └──→ Sparkle/Compiler/DRC.lean    → Design Rule Check (timing safety)
```

All three backends share the same IR.  Adding a fourth
backend (e.g. PTX, OpenCL, Vivado HLS) means a new file in
`Sparkle/Backend/`, no upstream-IR changes.

### What `Signal dom α` actually is

A `Signal dom α` is, semantically, a `Nat → α` — a stream of
per-cycle values.  Operationally it's a thin wrapper around a
closure or a memo table; the compiler decides which.  The
type carries a `dom : DomainConfig` parameter so signals
from different clock domains can't be accidentally mixed
(CDC safety at the type level).

## 10.2 JIT vs Verilator vs synthesis — when to use each

| Use case                          | Pick                | Speed     | Pre-reqs            |
|-----------------------------------|---------------------|-----------|---------------------|
| Quick `#eval` on a 1k-cycle trace | `Signal.sample`     | µs/cycle  | nothing             |
| Million-cycle simulation          | `Signal.loopMemo`   | ns/cycle  | nothing             |
| Long simulation in C++ JIT        | `Sparkle.Backend.CppSim` | C-class | g++ on PATH       |
| Cycle-accurate trace + waveforms  | Verilator pipeline  | C-class   | Verilator on PATH   |
| Real silicon                      | Yosys + nextpnr     | offline   | toolchain (Ch 8/9)  |

Rule of thumb: **author with `circuit do`, debug with
`.sample`, scale with `loopMemo`, ship with Verilog**.  The
JIT path is for when you need real-time-ish simulation (RV32
SoC running Linux runs at ~14M cycles/s on the JIT — fast
enough that booting Linux is feasible inside CI).

## 10.3 Reset and clock conventions

Sparkle's generated SystemVerilog has a single clock (`clk`)
and an active-high reset (`rst`).  The reset is either
**synchronous** or **asynchronous** depending on the
register's owning `DomainConfig.resetKind`:

```text
-- .synchronous (the standard domains: defaultDomain / domain50MHz / domain200MHz)
always_ff @(posedge clk) begin
  if (rst) <output> <= <init>;
  else     <output> <= <next>;
end

-- .asynchronous (write `{ ..., resetKind := .asynchronous }`)
always_ff @(posedge clk or posedge rst) begin
  if (rst) <output> <= <init>;
  else     <output> <= <next>;
end
```

The kind is wired through the IR: `Stmt.register` carries
`(reset : String × ResetKind)`, the elaborator reads
`Reset dom`'s `dom.resetKind` and stamps it onto the IR, and
`Sparkle/Backend/Verilog.lean` switches the sensitivity list
on the kind.  No global flag — the choice is per-register, set
by the domain.

Why the synchronous default?  It matches what most ASIC flows
expect (synchronous reset = fewer timing-arc surprises), is
easy to retime, and DC- / Yosys-friendly.  Async is available
when the FPGA primitive (e.g. iCE40 `SB_DFFR`) wants it
directly.

There is no multi-clock support in the generated Verilog
itself — every module uses the single `clk` port.  Sparkle's
**CDC module** (§10.3b above; `docs/architecture/CDC.md`)
handles cross-domain communication at *simulation* time via
the lock-free SPSC runtime, not via multi-clock RTL.

## 10.3b CDC — lock-free multi-clock simulation

§10.3 said Sparkle's *generated Verilog* is single-clock.  But
real chips often have several clocks — a 100 MHz CPU talking to
a 50 MHz peripheral, an audio domain, an FPGA-board PLL.
Sparkle's **simulator** handles that today with a small
lock-free runtime; this section explains how, why it works, and
where the trade-offs live.

The user-facing entry point is `JIT.runCDC`:

```text
def JIT.runCDC
    (handleA  handleB  : JITHandle)
    (cyclesA  cyclesB  : UInt64)
    (outPortA : UInt32) (inPortB : UInt32)
    : IO (UInt64 × UInt64 × UInt64)
    -- = (messagesSent, messagesReceived, rollbacks)
```

Each handle is a JIT-built simulator (Ch 8b §8b.3).  `runCDC`
spawns *two* threads — one per domain — connected by a
single-producer single-consumer queue.

### How it works in one diagram

```text
        Thread A (e.g. 100 MHz)              Thread B (e.g. 50 MHz)
        ┌─────────────────────┐              ┌─────────────────────┐
        │  jit_eval_tick      │              │  pop CDCMessage     │
        │  read outPortA      │              │  if msg.ts < localT │
        │  push {ts,payload}  │   SPSC queue │     restore(snap)   │
        │     to queue        │ ───────────▶ │     localT = msg.ts │
        │  ts += 1            │              │  jit_set_input      │
        │                     │              │  jit_eval_tick      │
        └─────────────────────┘              └─────────────────────┘
              producer                              consumer
              (no locks)                            (no locks)
```

Two ideas make this fast and correct simultaneously:

1.  **The queue itself is lock-free** —
    `c_src/cdc/spsc_queue.hpp`, ARM64-tuned, ~210 M ops/sec.
    The producer holds `write_idx`, the consumer holds
    `read_idx`; each lives on its own cache line so the two
    cores don't ping-pong false-sharing traffic.
2.  **Only the *consumer's* simulation state ever rolls back**
    — never the queue.  When a message arrives with a
    timestamp earlier than the consumer's local clock, the
    consumer restores the most recent snapshot, replays from
    that point with the late message, and continues popping.
    The producer is unaffected — and crucially, the queue's
    `read_idx` / `write_idx` keep advancing monotonically.

### Why "no locks" is safe — the SPSC invariant

A general MPMC (multi-producer, multi-consumer) queue needs
mutexes or compare-and-swap loops.  An **SPSC** queue (one
producer thread, one consumer thread) doesn't, because:

- The producer is the *only* writer of `write_idx`.  An atomic
  release-store is enough to publish a new message.
- The consumer is the *only* writer of `read_idx`.  An atomic
  release-store is enough to publish that a slot is free.
- Each side reads the other's index with an atomic
  acquire-load — that pairs with the release on the other side
  and gives a happens-before edge through the C++20 memory
  model.

`Sparkle/Verification/CDCProps.lean` has 12 formal proofs
covering exactly these properties — `spsc_no_overflow`,
`spsc_no_underflow`, `push_preserves_nonempty`,
`rollback_guarantee`, `consume_preserves_write_idx`, etc.  No
`sorry`s.  The Lean proofs model the abstract state machine
(`writeIdx : Nat`, `readIdx : Nat`, monotone advancement); the
C++ implementation matches that model bit-for-bit, modulo the
power-of-two ring-buffer wrap.

### Why rollback is bounded

Time-warping looks dangerous — what if a thread keeps
rolling back forever?  Two structural reasons it doesn't:

- **Each rollback strictly advances `local_time` toward the
  message's timestamp.**  After rollback, the consumer's clock
  matches what the producer thought was already published, so
  the next pop can only land at or after that point.
- **The queue's read/write indices never roll back.**  Even if
  the consumer's *simulation* state rewinds, the inter-thread
  pointers don't, so the producer's view of "how full is the
  queue" stays monotone — the producer never re-sends old data.

Combined, the consumer's `local_time` rises monotonically over
the long run; rollback events shorten individual cycles but
can't stop forward progress.  In the multi-clock test
(`lake exe cdc-multi-clock-test`) a 100 MHz / 50 MHz pair runs
~75 K messages with **0 rollbacks** because the producer's
timestamps are emitted in order and the consumer is the
slower side — there's nothing to invert.  Rollbacks only
trigger when domains run truly concurrently *and* a transient
schedules order them out of sequence.

### Where the trade-offs are

| Strength                                              | Cost                                                   |
|-------------------------------------------------------|--------------------------------------------------------|
| ~10⁸-class queue throughput; no kernel mutex hops      | One queue per *direction* — N×N mesh for N domains    |
| Simulation state rolls back; queue indices don't      | Snapshots cost memory (one full register/RAM image)   |
| Each domain runs full-speed JIT independently         | Producer outpaces consumer → queue-full back-pressure |
| 12 formal proofs (`Sparkle.Verification.CDCProps`)    | Proofs model the abstract queue, not the C++ atomics  |
| Single-producer / single-consumer  ⇒ atomics suffice  | Multi-producer per direction needs a different queue  |

Two practical guidelines fall out of this:

- **Pair the slower domain as the consumer when you can.**
  That naturally keeps timestamps in order and rollbacks at
  zero (the multi-clock test demonstrates this).
- **Snapshots are cheap when state is small (a 256-word
  scratchpad), expensive when state is huge (a 16 MiB cache).**
  For very large designs, place CDC boundaries before the cache,
  not after.

### Where to read more

- `docs/architecture/CDC.md` — concise architecture summary
- `c_src/cdc/spsc_queue.hpp` — the queue (146 lines, heavily
  commented)
- `c_src/cdc/cdc_rollback.hpp` — the consumer wrapper (132 lines)
- `Sparkle/Verification/CDCProps.lean` — the 12 proofs

## 10.4 Where to extend Sparkle

- **New combinator**: add a `def` in `Sparkle/Core/Signal.lean`
  that builds out of existing `Signal.map` / `Signal.register` /
  `Signal.loop`.  No backend change required.
- **New tactic / proof helper**: add to `Sparkle/Tactics/`.
- **New backend**: add a file under `Sparkle/Backend/`.  Your
  backend consumes the `Signal IR` (`Sparkle/IR/AST.lean`) and
  emits whatever you want.  The Verilog and C++-JIT backends
  are short; copy one as a template.
- **New IP**: add a `lean_lib` and `IP/<YourIP>/` directory,
  following the BitNet / RV32 / YOLOv8 / Drone / Humanoid
  precedents in `IP/`.

## 10.5 Reference card — top macros and commands

| Form                           | Purpose                                        |
|--------------------------------|------------------------------------------------|
| `circuit do { ... }`    | Imperative-style HDL with `<~` register assignment |
| `Signal.loop (fun s => ...)`   | Dataflow-style HDL with explicit recurrence    |
| `Signal.register init next`    | A single flip-flop                             |
| `Signal.mux cond a b`          | A multiplexer (use this, never `if-then-else`) |
| `declare_signal_state Foo`     | Generate a named record I/O type with accessors|
| `Foo.mk (field := sig)`        | Construct the named record                     |
| `Signal.lit dom v`             | Lift a constant when type inference can't reach it |
| `Signal.sample n`              | Sample the first `n` cycles as a list          |
| `#synthesizeVerilog name`      | Generate SystemVerilog for `name`              |
| `#synthesizeVerilogDesign name`| Same, plus design-rule check + report          |
| `#verify_eq sigA sigB n`       | Compare two signals over `n` cycles            |
| `#verify_eq_at sigA sigB t`    | Compare at one specific cycle                  |
| `#verify_eq_git sigA sigB ref n`| Compare against a committed reference trace    |
| `bv_decide`                    | Tactic: SAT-style proof of bit-vector goals    |
| `decide` / `native_decide`     | Tactic: exhaustive enumeration of small types  |

Full details:
`docs/reference/SignalDSL_Syntax.md`,
`docs/reference/Verification_Framework.md`,
`docs/reference/Troubleshooting_Synthesis.md`.

## 10.5b Notebook helper commands

Inside JupyterLab the xeus-lean kernel adds a handful of
notebook-only commands.  The Sparkle tutorial chapters use them
sparingly so the same source builds under headless `lake build`
— the `Display` shim provides parsing-only stubs so each command
is syntactically valid even when its real behaviour is absent.

| Command                                    | Kernel behaviour                          | Shim behaviour                |
|--------------------------------------------|-------------------------------------------|--------------------------------|
| `#mermaid "flowchart LR; A --> B"`         | renders Mermaid SVG                       | emits a `<div class="mermaid">` payload (HTML viewers render it) |
| `#help_x`                                  | lists every kernel-only command           | prints a one-liner pointer    |
| `#findDecl "kw1" "kw2" 0 20`               | substring-search the active environment   | echoes the search args        |
| `#listNs Sparkle.Core.Signal`              | tree of declarations under a namespace    | prints `(#listNs shim: ...)`  |
| `#sig Sparkle.Signal.register`             | pretty-prints a declaration's type        | suggests `#check`             |
| `#bash "ls -1 docs/tutorial"`              | runs `bash -c` and inlines stdout/stderr  | hard no-op                    |

The `Display.*` rendering helpers (`Display.waveform`,
`Display.boolWave`, `Display.verilog`, `Display.blockDiagram`,
`Display.writeWdb`, `Display.waveformFromWdb`) follow the same
two-tier pattern: real implementations under xeus-lean, MIME-
emitting shims under `lake build`.

```lean
#help_x
#listNs Sparkle.Core.Signal
```

You can use these commands freely while exploring the codebase
in JupyterLab; the chapter Markdown sources stay buildable even
when the kernel isn't available.

## 10.6 Where to go from here

The course covers the foundation.  Real Sparkle work happens
in the IP repos and the architecture docs:

- **`docs/ip-catalog/RV32.md`** — a full RISC-V SoC, complete
  with Linux boot.  Read it as a worked example of every
  chapter applied at scale.
- **`docs/ip-catalog/BitNet.md`** — a 1.58-bit transformer
  accelerator, with FPGA results.
- **`docs/architecture/STATUS.md`** — append-only
  development log (current status, benchmarks, completed
  phases).
- **`docs/architecture/CDC.md`** — multi-clock-domain story.
- **`docs/architecture/JIT_FFI_Plan.md`** — how the C++ JIT
  integrates with Lean.

Welcome to Sparkle.  Have fun.

end Notebooks.Ch10
