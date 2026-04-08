# Sparkle Tutorial

A step-by-step guide from "Hello World" to formal verification.

## Prerequisites

```bash
git clone https://github.com/Verilean/sparkle
cd sparkle
lake build   # ~5 min first time
```

---

## Step 1: Define Hardware (Signal DSL)

Create `tutorial.lean`:

```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- An 8-bit counter with enable
def counter8 (en : Signal Domain (BitVec 1)) : Signal Domain (BitVec 8) :=
  Signal.loop fun count =>
    let next := Signal.mux (en === 1) (count + 1) count
    (Signal.register 0#8 next, next)

-- Simulate for 10 cycles (en=1 always)
#eval do
  let values := (counter8 (Signal.pure 1#1)).sample 10
  IO.println s!"Counter: {values}"
  -- Counter: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
```

```bash
lake env lean tutorial.lean
```

---

## Step 2: Generate Verilog

Add this line to see the generated SystemVerilog:

```lean
#synthesizeVerilog counter8
```

Output:

```systemverilog
module counter8 (
    input  logic clk,
    input  logic rst,
    input  logic [0:0] en,
    output logic [7:0] out
);
    logic [7:0] count;
    always_ff @(posedge clk) begin
        if (rst) count <= 8'h00;
        else     count <= en ? (count + 8'h01) : count;
    end
    assign out = count;
endmodule
```

---

## Step 3: Generate VCD Waveform

View signals in GTKWave:

```lean
import Sparkle
import Sparkle.Backend.VCD

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Backend.VCD

def counter8 (en : Signal Domain (BitVec 1)) : Signal Domain (BitVec 8) :=
  Signal.loop fun count =>
    let next := Signal.mux (en === 1) (count + 1) count
    (Signal.register 0#8 next, next)

def main : IO Unit := do
  let en := Signal.pure 1#1
  let count := counter8 en

  -- Create VCD writer and add signals
  let writer := VCDWriter.new "counter8"
    |>.addVar "en" 1
    |>.addVar "count" 8

  -- Sample signals
  let enTrace := sampleBitVecSignal en
    (writer.variables[0]!.identifier) 20
  let countTrace := sampleBitVecSignal count
    (writer.variables[1]!.identifier) 20

  -- Write VCD file
  let vcd := generateVCD writer (enTrace ++ countTrace)
  writeVCDFile "counter8.vcd" vcd
```

```bash
lake env lean --run tutorial_vcd.lean
gtkwave counter8.vcd   # open in waveform viewer
```

---

## Step 4: JIT Simulation (Verilog → Fast Sim)

For large designs or existing Verilog, use JIT compilation for maximum speed:

```lean
import Tools.SVParser.SimMacro

-- sim! parses the Verilog and auto-generates the following under
-- `hello_counter.Sim`:
--
--   SimInput        — typed input record (clock and reset are hidden;
--                     use `sim.reset` to pulse reset instead)
--   SimOutput       — typed output record
--   Simulator       — { handle : JITHandle } with step/read/reset/destroy
--   load            — compile + load in one step
--   toEndpoint      — wrap for runSim (Step 6)
sim! "
module hello_counter (
    input clk,
    input rst,
    output [7:0] count
);
    reg [7:0] count_reg;
    assign count = count_reg;
    always @(posedge clk) begin
        if (rst) count_reg <= 8'h00;
        else count_reg <= count_reg + 8'h01;
    end
endmodule
"

open hello_counter.Sim

def main : IO Unit := do
  let sim ← load              -- compile JIT C++ and load
  sim.reset                   -- pulse hardware reset (handled by JIT)
  for i in [:10] do
    sim.step {}               -- SimInput is empty (no user-driven inputs)
    let out ← sim.read
    IO.println s!"  cycle {i}: count = {out.count}"
  sim.destroy
```

No port definitions needed — `sim!` extracts them from the Verilog.
A typo like `out.cont` is caught at compile time.

**Clock and reset are hidden from `SimInput`.** Drive them with
`sim.reset` (for the initial reset pulse) rather than passing `rst` as
a field — this matches how hardware works and keeps the typed surface
clean. If a module has user inputs beyond clock/reset, those show up as
required fields in `SimInput`.

### Running many cycles with `runSim`

For larger simulations, prefer `runSim` over hand-rolled loops. It
automatically picks the fastest backend (Step 6 explains multi-domain):

```lean
import Sparkle.Core.SimParallel
open Sparkle.Core.SimParallel

def main : IO Unit := do
  let sim ← hello_counter.Sim.load
  sim.reset
  let stats ← runSim [sim.toEndpoint] (cycles := 1_000_000)
  let out ← sim.read
  IO.println s!"Ran {stats.cyclesRun} cycles, final count = {out.count}"
  sim.destroy
```

### JIT from Signal DSL

Use `#sim` for Signal DSL definitions:

```lean
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

def myAdder (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  a + b

#sim myAdder   -- auto-generates myAdder.Sim.*

open myAdder.Sim

def main : IO Unit := do
  let sim ← load
  sim.reset
  sim.step { a := 3, b := 5 }
  let out ← sim.read
  IO.println s!"3 + 5 = {out.out}"   -- 8
  sim.destroy
```

---

## Step 5: Formal Verification

Prove properties about your hardware — bugs caught at compile time, not simulation.

### 5.1 Prove Properties of Verilog

`verilog!` parses Verilog and generates Lean definitions (`State`, `Input`, `nextState`).
You prove theorems against these definitions.

```lean
import Tools.SVParser.Macro

-- Parse at compile time → generates counter8_en.Verify.{State, Input, nextState}
verilog! "
module counter8_en (
    input clk, input rst, input en,
    output [7:0] count
);
    reg [7:0] count_reg;
    assign count = count_reg;
    always @(posedge clk) begin
        if (rst) count_reg <= 0;
        else if (en) count_reg <= count_reg + 1;
    end
endmodule
"

open counter8_en.Verify

-- Theorem 1: Reset clears the counter
theorem reset_clears (s : State) (i : Input) :
    i.rst = 1 → (nextState s i).count_reg = 0 := by
  intro h; simp [nextState, h]

-- Theorem 2: Counter holds when disabled
theorem holds_when_disabled (s : State) :
    nextState s { rst := 0, en := 0 } = s := by
  simp [nextState]

-- Theorem 3: Counter increments when enabled
theorem increments (s : State) :
    (nextState s { rst := 0, en := 1 }).count_reg = s.count_reg + 1 := by
  simp [nextState]
```

If you change the Verilog (e.g., `+ 1` → `+ 2`), the proofs **instantly fail** — no simulation needed.

### 5.2 Auto-Proved Assertions

Add `assert()` in your Verilog — `verilog!` auto-generates and auto-proves them:

```verilog
always @(posedge clk) begin
    if (rst) count_reg <= 0;
    else if (en) count_reg <= count_reg + 1;

    // Auto-generated theorem, proved by bv_decide:
    assert(rst ? (count_reg == 0) : 1);
end
```

The assertion becomes a Lean theorem proved automatically by `bv_decide`.
If the assertion is wrong, you get a compile-time error.

### 5.3 Prove Properties of Signal DSL

For hardware written in Signal DSL, use `simp` and `bv_decide`:

```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

def myAnd (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  a &&& b

-- AND with zero is zero
theorem and_zero (a : Signal Domain (BitVec 8)) (t : Nat) :
    (myAnd a (Signal.pure 0#8)).val t = 0#8 := by
  simp [myAnd, Signal.val]
```

---

## Step 6: Running Simulations with `runSim`

Sparkle provides a single high-level runner, `runSim`, that automatically
picks the fastest backend for your simulation. You pass it the endpoints
you have and it dispatches to:

- **Single-threaded `evalTick` loop** — when you have 1 endpoint and no
  connections. Fastest for single-domain simulations (~18 M cyc/s on LiteX).
- **Multi-threaded CDC queue** (`JIT.runCDC`) — when you have 2 endpoints
  joined by 1 connection. Fastest for multi-clock domain simulations
  (**11.9 × Verilator** on 8-core LiteX benchmarks).

You should not need to pick manually: just pass the endpoints and `runSim`
does the right thing.

### Single-domain

```lean
import Sparkle.Core.SimParallel
open Sparkle.Core.SimParallel

sim! "module counter (input clk, input rst, output [31:0] count); ... endmodule"

def main : IO Unit := do
  let sim ← counter.Sim.load
  sim.reset
  let stats ← runSim [sim.toEndpoint] (cycles := 1_000_000)
  IO.println s!"Ran {stats.cyclesRun} cycles"
```

### Multi-domain (CDC)

```lean
sim! "module producer (input clk, input rst, output [31:0] data_out); ... endmodule"
sim! "module consumer (input clk, input rst, input [31:0] data_in); ... endmodule"

def main : IO Unit := do
  let p ← producer.Sim.load
  let c ← consumer.Sim.load
  p.reset; c.reset
  let stats ← runSim
    [p.toEndpoint, c.toEndpoint]
    (connections := [("data_out", "data_in")])
    (cycles := 1_000_000)
  IO.println s!"sent={stats.messagesSent} recv={stats.messagesReceived}"
```

Connections are specified as `(producerOutputName, consumerInputName)`
string pairs. `runSim` looks up the port indices at runtime via the
`outputPortIndexByName` / `inputPortIndexByName` tables generated by
`sim!` / `generateSimWrappers`, so typos and missing names fail with a
clear error listing the available ports.

### Manual overrides

`runSim` is a thin dispatcher on top of two explicit runners you can call
directly if you want to force a backend (benchmarking, debugging,
avoiding thread overhead on a single-domain sim):

| Runner | When to use |
|---|---|
| `runSingleSim ep cycles` | Single-threaded, bit-identical to a manual `evalTick` loop. |
| `runMultiDomainSim prod cons conn prodCycles consCycles` | Multi-threaded CDC with separate per-domain cycle budgets. |

Most users should never need these. If you find `runSim`'s choice
suboptimal, please file an issue — the dispatcher is only a few lines
and can be improved.

### Current limitations

- **Single connection per pair**: the underlying `JIT.runCDC` transfers
  one output→input pair. Multi-connection support is tracked in
  `docs/KnownIssues.md` Issue 3.1.
- **Two endpoints max**: three or more domains is not yet supported
  (Issue 3.2).

See `Examples/CDC/MultiClockSim.lean` for a working end-to-end example
and `Tests/Sim/SimRunnerTest.lean` for the 27-test regression suite
(equivalence, auto-select, port-name errors, index alignment, stress).

---

## Step 7: What's Next

| Topic | Where |
|-------|-------|
| **Signal DSL syntax** | `docs/SignalDSL_Syntax.md` |
| **Verification patterns** | `docs/Verification_Framework.md` |
| **IP catalog** (RV32I CPU, AXI4-Lite, H.264, BitNet) | `README.md` |
| **Benchmark** (Sparkle JIT vs Verilator) | `docs/BENCHMARK.md` |
| **Reverse synthesis** (proof-driven FSM optimization) | `Sparkle/Core/OracleSpec.lean` |

---

## Summary: The Sparkle Pipeline

```
  Signal DSL          Verilog (.v)
      │                    │
      ▼                    ▼
  #synthesizeVerilog    sim! / verilog!
      │                    │
      ▼                    ▼
  Verilog output     Parse → Sparkle IR
      │                    │
      ├── VCD waveform     ├── JIT C++ → .so → fast simulation
      │                    │                      │
      └── Formal proofs    ├── OracleReduction     ├── runSim (auto)
          (bv_decide)      │   (proof-driven opt)  │   ├─ runSingleSim
                           │                      │   └─ runMultiDomainSim
                           │                      │      (CDC queue)
                           └──────────────────────┘
```
