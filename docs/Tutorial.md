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

-- sim! parses the Verilog and auto-generates:
--   hello_counter.Sim.SimInput   { rst : BitVec 1 }
--   hello_counter.Sim.SimOutput  { count : BitVec 8 }
--   hello_counter.Sim.Simulator  with step/read/reset/destroy
--   hello_counter.Sim.load       (compile + load in one step)
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
  let sim ← load           -- compile JIT C++ and load
  sim.reset
  for _ in [:3] do
    sim.step { rst := 1 }  -- hold reset
  for i in [:10] do
    sim.step { rst := 0 }  -- run
    let out ← sim.read
    IO.println s!"  cycle {i}: count = {out.count}"
  sim.destroy
```

No port definitions needed — `sim!` extracts them from the Verilog.
A typo like `out.cont` is caught at compile time.

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

## Step 6: Multi-Domain Parallel Simulation (Preview)

Sparkle supports multi-clock-domain simulation with lock-free CDC queues.
Currently available as a low-level API; a `sim_parallel!` macro is planned.

### Current API (low-level)

```lean
import Sparkle.Core.JIT

-- Load two JIT-compiled domains
let prodHandle ← JIT.compileAndLoad "producer_jit.cpp"
let consHandle ← JIT.compileAndLoad "consumer_jit.cpp"

-- Run in parallel: producer's output port 0 → consumer's input port 0
-- Returns (messagesSent, messagesReceived, rollbackCount)
let (sent, recv, rollbacks) ←
  JIT.runCDC prodHandle consHandle 1000000 0 0
```

This achieves **11.9x vs Verilator** on 8-core LiteX SoC benchmarks.

### Planned: `sim_parallel!` (TODO)

```lean
-- Goal: type-safe parallel simulation from sim! definitions
sim! "module producer (...) ..."
sim! "module consumer (...) ..."

-- Connect output → input by name, run in parallel
let result ← simParallel
  (producer := producer.Sim)
  (consumer := consumer.Sim)
  (connections := [("data_out", "data_in")])
  (cycles := 1000000)
```

See `Examples/CDC/MultiClockSim.lean` for a working multi-domain example.

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
      └── Formal proofs    ├── OracleReduction     ├── sim_parallel! (planned)
          (bv_decide)      │   (proof-driven opt)  │   (multi-domain CDC)
                           │                      │
                           └──────────────────────┘
```
