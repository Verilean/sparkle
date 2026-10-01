
# Chapter 8d — Transaction-level testbenches, and UVM from the same test

Chapter 8b drove a circuit one clock cycle at a time: set the inputs,
`step`, read the outputs.  That is fine for a counter.  It stops being
fine as soon as the circuit has a **handshake**: the test has to hold
`valid` until `ready`, remember what it sent, wait an unknown number
of cycles for each answer, and it should do all of that again with
gaps in the input and a slow consumer on the output — the conditions
under which handshake bugs actually show up.

This chapter moves the test up one level.  You write

* **what goes in** — a list of transactions,
* **what must come out** — a list computed by an ordinary Lean function,

and a small library (`Sparkle.Verification.Tlm`) does the cycle-level
work: drivers, monitors, pacing, protocol checks, timeouts, scoreboard.
The last section writes the same test out as a SystemVerilog **UVM**
testbench, for teams whose sign-off flow is UVM.

| Piece        | What it is                                                       |
|--------------|------------------------------------------------------------------|
| `SourcePort` | how to drive one ready/valid stream INTO the design              |
| `SinkPort`   | how to observe one ready/valid stream OUT OF the design          |
| `Pace`       | in which cycles a driver offers data / a monitor is ready        |
| `Bench`      | the clock loop; owns the drivers and monitors, collects errors   |
| `runStream`  | one call: send a list, compare what arrives with a list          |
| `Endpoint`   | blocking `put` / `get`; the same test runs on RTL and on a model |
| `Uvm.emit`   | the same test as a UVM testbench (`.sv`)                         |

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitDo
import Sparkle.Verification.Tlm
import Sparkle.Verification.TlmUvm

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Sim
open Sparkle.Verification.Tlm

namespace Notebooks.Ch08d

```

## 8d.1 The design: a one-entry stage with ready/valid on both sides

The stage takes a 32-bit `x`, and offers `3·x + 1` on its output one
cycle later.  It holds one result.  It can take a new input when it is
empty, or when its result is being taken in the same cycle:

    inReady = ¬full ∨ outReady

```lean
/-- Output: `inReady ++ outValid ++ outData` (1 + 1 + 32 bits). -/
def scaleStage (inValid : Signal defaultDomain Bool) (inData : Signal defaultDomain (BitVec 32))
    (outReady : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 34) :=
  circuit do
    let full ← Signal.reg false
    let data ← Signal.reg 0#32
    let fullS := (full : Signal defaultDomain Bool)
    let dataS := (data : Signal defaultDomain (BitVec 32))
    let inReady := Signal.mux fullS outReady (Signal.pure true)
    let accept := inValid &&& inReady
    full <~ Signal.mux accept (Signal.pure true) (Signal.mux outReady (Signal.pure false) fullS)
    data <~ Signal.mux accept (inData * 3#32 + 1#32) dataS
    return (Signal.mux inReady (Signal.pure 1#1) (Signal.pure 0#1)) ++
           ((Signal.mux fullS (Signal.pure 1#1) (Signal.pure 0#1)) ++ dataS)

#sim scaleStage
#synthesizeVerilog scaleStage

```

`#sim` gives us the typed simulator from Chapter 8b:
`scaleStage.Sim.SimInput` with one field per input (`_gen_inValid`,
`_gen_inData`, `_gen_outReady`) and `scaleStage.Sim.SimOutput` with the
34-bit `out`.

## 8d.2 Port maps — the only design-specific testbench code

A port map says which signals form a stream.  For a stream into the
design: how to put a transaction (or nothing) on the inputs, and where
to read `ready`.  For a stream out of the design: how to set `ready`,
and how to read `valid` together with the payload.

```lean
def stageIn : SourcePort scaleStage.Sim.SimInput scaleStage.Sim.SimOutput (BitVec 32) where
  name := "in"
  drive i x := { i with _gen_inValid := if x.isSome then 1 else 0, _gen_inData := x.getD 0 }
  ready o := o.out.getLsbD 33

def stageOut : SinkPort scaleStage.Sim.SimInput scaleStage.Sim.SimOutput (BitVec 32) where
  name := "out"
  setReady i r := { i with _gen_outReady := if r then 1 else 0 }
  valid o := if o.out.getLsbD 32 then some (o.out.extractLsb' 0 32) else none

```

The payload type is yours.  Here it is `BitVec 32`; for a bus it would
be a structure (address, data, strobe) packed and unpacked in these
four functions.  Nothing else in the test mentions bit positions.

## 8d.3 The test: a list in, a list out

The reference is a plain function on lists.  No clock, no handshake.

```lean
def items : List (BitVec 32) := (List.range 24).map fun k => BitVec.ofNat 32 (k * 1000003 + 7)

def model (xs : List (BitVec 32)) : List (BitVec 32) := xs.map (· * 3#32 + 1#32)

#eval do
  let sim ← scaleStage.Sim.load
  let (report, latency) ← runStream sim default stageIn stageOut items (model items)
  Sim.destroy sim
  IO.println s!"ok = {report.ok}, {report.cycles} cycles, latency {latency.foldl min 1000}..{latency.foldl max 0}"

```

```text
ok = true, 29 cycles, latency 1..1
```

`runStream` sends every item, waits until the expected number of
results has arrived (or reports a timeout), runs a few more cycles to
catch results nobody asked for, and compares.  `latency` is, per
transaction, the number of cycles between its input handshake and its
output handshake.

## 8d.4 Pacing: gaps in the input, back-pressure on the output

With the defaults the driver offers data every cycle and the monitor is
always ready.  That is the easy case; a handshake that is wrong usually
still passes it.  `Pace` changes when each side is willing to act:

| `Pace`                    | active in                                   |
|---------------------------|---------------------------------------------|
| `.always`                 | every cycle                                 |
| `.every 3`                | cycles 0, 3, 6, …                           |
| `.pattern [false, true]`  | the repeating pattern                       |
| `.random seed percent`    | about `percent` % of cycles, reproducibly   |

`.random` is a fixed hash of the seed and the cycle number: the same
test gives the same run every time, on every machine.

```lean
def paces : List (String × Pace × Pace) :=
  [ ("no gaps, no back-pressure", .always, .always)
  , ("input gaps", .random 1 40, .always)
  , ("back-pressure", .always, .every 3)
  , ("both, random", .random 2 60, .random 3 50) ]

#eval do
  for (label, inPace, outPace) in paces do
    let sim ← scaleStage.Sim.load
    let (report, latency) ← runStream sim default stageIn stageOut items (model items) inPace outPace
    Sim.destroy sim
    IO.println s!"{label}: ok = {report.ok}, {report.cycles} cycles, latency up to {latency.foldl max 0}"

```

```text
no gaps, no back-pressure: ok = true, 29 cycles, latency up to 1
input gaps: ok = true, 66 cycles, latency up to 1
back-pressure: ok = true, 77 cycles, latency up to 3
both, random: ok = true, 52 cycles, latency up to 5
```

Same 24 results every time; only the cycle count and the latency move.

## 8d.5 A bug that only back-pressure finds

Here is the same stage with one line "simplified": it is always ready.
A new input now overwrites a result that is still waiting to be taken.

```lean
/-- BROKEN on purpose: drops data when the consumer stalls. -/
def leakyStage (inValid : Signal defaultDomain Bool) (inData : Signal defaultDomain (BitVec 32))
    (outReady : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 34) :=
  circuit do
    let full ← Signal.reg false
    let data ← Signal.reg 0#32
    let fullS := (full : Signal defaultDomain Bool)
    let dataS := (data : Signal defaultDomain (BitVec 32))
    full <~ Signal.mux inValid (Signal.pure true) (Signal.mux outReady (Signal.pure false) fullS)
    data <~ Signal.mux inValid (inData * 3#32 + 1#32) dataS
    return (Signal.pure 1#1 : Signal defaultDomain (BitVec 1)) ++
           ((Signal.mux fullS (Signal.pure 1#1) (Signal.pure 0#1)) ++ dataS)

#sim leakyStage

def leakyIn : SourcePort leakyStage.Sim.SimInput leakyStage.Sim.SimOutput (BitVec 32) where
  name := "in"
  drive i x := { i with _gen_inValid := if x.isSome then 1 else 0, _gen_inData := x.getD 0 }
  ready o := o.out.getLsbD 33

def leakyOut : SinkPort leakyStage.Sim.SimInput leakyStage.Sim.SimOutput (BitVec 32) where
  name := "out"
  setReady i r := { i with _gen_outReady := if r then 1 else 0 }
  valid o := if o.out.getLsbD 32 then some (o.out.extractLsb' 0 32) else none

#eval do
  let sim ← leakyStage.Sim.load
  let (report, _) ← runStream sim default leakyIn leakyOut items (model items)
  Sim.destroy sim
  IO.println s!"never stalled:      ok = {report.ok}"
  let sim ← leakyStage.Sim.load
  let (report, _) ← runStream sim default leakyIn leakyOut items (model items) .always (.every 3)
    (maxCycles := 400)
  Sim.destroy sim
  IO.println s!"consumer 1 in 3:    ok = {report.ok}, {report.errors.length} errors, for example"
  for e in report.errors.take 1 ++ report.errors.drop (report.errors.length - 3) do
    IO.println s!"  {e}"

```

```text
never stalled:      ok = true
consumer 1 in 3:    ok = false, 19 errors, for example
  cycle 2: out: the payload changed while valid was waiting for ready
  timeout after 400 cycles waiting for 24 transactions on out
  out: transaction 0 is some 0x005b8da8#32, expected some 0x00000016#32
  out: 8 transactions, expected 24
```

The first run passes — a test without back-pressure does not see this
bug at all.  The second reports three kinds of error, each from a
different part of the bench:

* **the monitor** — a ready/valid source must keep its payload
  unchanged from the cycle it raises `valid` until the handshake.  The
  monitor checks this on every stream out of the design, and also that
  `valid` is not withdrawn before the handshake;
* **the clock loop** — the expected number of results never arrives, so
  `runUntil` gives up after `maxCycles` and says what it was waiting
  for.  A hung handshake is an error message, not a hung test;
* **the scoreboard** — the first transaction that differs from the
  model, and the two lengths if they differ.

## 8d.6 The bench by hand

`runStream` is a dozen lines over the pieces below.  Use them directly
when a design has more than one stream in or out, or when the test has
to react to what it sees.

```lean
#eval do
  let sim ← scaleStage.Sim.load
  let b ← Bench.new sim (default : scaleStage.Sim.SimInput) (maxCycles := 500)
  let d ← b.addDriver stageIn (.random 5 70)     -- add one per input stream
  let m ← b.addMonitor stageOut (.every 2)       -- add one per output stream
  d.sendAll items
  let _ ← b.runUntil (m.count items.length) "all results"
  b.check "out" (← m.items) (model items)
  let report ← b.report
  let sent ← d.log
  let received ← m.log
  Sim.destroy sim
  IO.println s!"ok = {report.ok} after {report.cycles} cycles"
  IO.println s!"first handshakes in : {List.map Prod.fst (sent.take 3)}"
  IO.println s!"first handshakes out: {List.map Prod.fst (received.take 3)}"

```

```text
ok = true after 57 cycles
first handshakes in : [1, 2, 4]
first handshakes out: [2, 4, 6]
```

`d.log` and `m.log` are lists of `(cycle, transaction)` — the cycle in
which each handshake happened.  `b.error "…"` adds your own check to
the report; `b.run n` clocks `n` cycles; `b.cycle` is the current cycle.

## 8d.7 One test sequence, on the RTL and on a model

An `Endpoint` hides the clock completely: `put` returns when the design
has accepted the transaction, `get` returns the next result.  A test
written against `Endpoint` does not know whether there is RTL behind it.

```lean
def sequence (ep : Endpoint (BitVec 32) (BitVec 32)) : IO (List (Option (BitVec 32))) := do
  let _ ← ep.put 5#32
  let _ ← ep.put 6#32
  let a ← ep.get
  let _ ← ep.put 7#32
  let b ← ep.get
  let c ← ep.get
  return [a, b, c]

#eval do
  -- on the RTL
  let sim ← scaleStage.Sim.load
  let b ← Bench.new sim (default : scaleStage.Sim.SimInput)
  let d ← b.addDriver stageIn
  let m ← b.addMonitor stageOut
  let rtl ← sequence (Endpoint.ofRtl b d m)
  Sim.destroy sim
  -- on an untimed model: state → request → (state', responses)
  let ref ← sequence (← Endpoint.ofModel (fun (_ : Unit) (x : BitVec 32) => ((), [x * 3#32 + 1#32])) ())
  let show_ (xs : List (Option (BitVec 32))) : List (Option Nat) := List.map (Option.map BitVec.toNat) xs
  IO.println s!"rtl   = {show_ rtl}"
  IO.println s!"model = {show_ ref}"
  IO.println s!"equal = {rtl == ref}"

```

```text
rtl   = [(some 16), (some 19), (some 22)]
model = [(some 16), (some 19), (some 22)]
equal = true
```

This is the useful half of what SystemC TLM is used for: write the
test (or the software that talks to the block) against the model
first, then run it unchanged on the RTL when the RTL exists.

## 8d.8 The same bench on Verilator

`scaleStage.Sim.loadVerilator` (Chapter 8b) builds the emitted Verilog
with Verilator and returns a handle with the same ABI as the JIT.  The
typed simulator is just a wrapper around a handle, so the whole bench
runs on Verilator by swapping the handle:

```text
let v ← scaleStage.Sim.loadVerilator
let sim : scaleStage.Sim.Simulator := { handle := v.handle }
let (report, latency) ← runStream sim default stageIn stageOut items (model items)
```

Both backends show an output in the same cycle, so `d.log` and `m.log`
are identical between them — `Tests/TlmTest.lean` checks exactly that
(every handshake, same cycle, on the FIFO and on the stage).  This is a
check of the *emitted Verilog* by a simulator Sparkle did not write.

## 8d.9 Export: the same test as a UVM testbench

For a UVM flow, describe the streams once more — this time in terms of
the Verilog ports — and hand over the same two lists.

```lean
open Sparkle.Verification.Tlm in
def stageUvm : Uvm.Bench :=
  { name := "stage_tb"
    dutModule := "Notebooks_Ch08d_scaleStage"
    dutOutputs := [("out", 34)]
    streams :=
      [ { name := "in", width := 32, toDut := true
          valid := "_gen_inValid", data := "_gen_inData", ready := "out[33]" }
      , { name := "res", width := 32, toDut := false
          valid := "out[32]", data := "out[31:0]", ready := "_gen_outReady" } ]
    stimulus := [("in", items.map (·.toNat))]
    expected := [("res", (model items).map (·.toNat))]
    readyPercent := 60 }

#eval do
  let tb := Uvm.emit stageUvm
  IO.FS.createDirAll ".lake/build/gen/uvm"
  IO.FS.writeFile ".lake/build/gen/uvm/ch08d_stage_tb.sv" tb
  IO.println s!"{tb.length} characters, {(tb.splitOn "\n").length} lines"
  for l in (tb.splitOn "\n").filter (fun (l : String) => (l.splitOn "  class ").length > 1) do
    IO.println l

```

```text
10831 characters, 306 lines
  class in_item extends uvm_sequence_item;
  class in_monitor extends uvm_monitor;
  class res_item extends uvm_sequence_item;
  class res_monitor extends uvm_monitor;
  class in_seq extends uvm_sequence #(in_item);
  class in_driver extends uvm_driver #(in_item);
  class res_responder extends uvm_component;
  class res_scoreboard extends uvm_scoreboard;
  class stage_tb_env extends uvm_env;
  class stage_tb_test extends uvm_test;
```

For a stream into the design, `valid` and `data` are the names of DUT
input ports and `ready` is a SystemVerilog expression over the DUT
outputs; for a stream out of the design it is the other way round.

What is generated:

| For                      | Generated                                                     |
|--------------------------|---------------------------------------------------------------|
| every stream             | `interface <s>_if`, `<s>_item`, `<s>_monitor` (analysis port) |
| a stream into the DUT    | `<s>_seq` (the stimulus list), `<s>_driver`, a `uvm_sequencer`|
| a stream out of the DUT  | `<s>_responder` (drives `ready`, `readyPercent` % of cycles), `<s>_scoreboard` (the expected list) |
| the bench                | `<name>_env`, `<name>_test`, `module <name>_top` (clock, reset, DUT, `run_test`) |

The expected results are computed in Lean, by `model`, and written into
the test as literals — the scoreboard needs no SystemVerilog reference
model, and the UVM run and the Lean run check the same thing.

To run it you need a SystemVerilog simulator with a UVM library.  With
Verilator 5 and Accellera's `uvm-core`:

```text
git clone https://github.com/accellera-official/uvm-core
UVM=$PWD/uvm-core

verilator --binary --timing -j 4 --Mdir obj \
  -Wno-fatal -Wno-lint -Wno-style +define+UVM_NO_DPI \
  +incdir+$UVM/src $UVM/src/uvm_pkg.sv \
  .lake/build/gen/sim/scaleStage.sv \
  .lake/build/gen/uvm/ch08d_stage_tb.sv \
  --top-module stage_tb_top
./obj/Vstage_tb_top
```

The run ends with a line per scoreboard and the UVM summary:

```text
UVM_INFO .../ch08d_stage_tb.sv(172) @ 480000: uvm_test_top.env.res_sb [SB] SCOREBOARD PASS res: 24 transactions matched
...
UVM_WARNING :    2
UVM_ERROR :    0
UVM_FATAL :    0
```

(The two warnings are uvm-core's own notices about `UVM_NO_DPI`.)

The repository runs this for three benches — the library FIFO, the
stage, and the stage that drops data (which must FAIL in UVM too):

```text
SPARKLE_UVM_HOME=$UVM lake exe tlm-uvm-test
```

Compiling the UVM library takes Verilator about a minute per bench, so
this is a separate executable and not part of `lake test`; without
`SPARKLE_UVM_HOME` it only writes the testbenches.

## 8d.10 Limits — read before relying on it

* **Protocol.**  One protocol: ready/valid, one payload per stream.
  AXI, with its five channels and bursts, is five streams plus rules
  between them; those rules are not written.
* **UVM export.**  The generated testbench is *directed*: the stimulus
  is the list from Lean, in order.  There is no constrained-random
  generation, no functional coverage, no register model.  Payloads are
  plain bit vectors up to the stream width.
* **Simulators.**  The generated UVM was run with Verilator 5.052 and
  uvm-core only.  No commercial simulator was available to try; the
  code uses no clocking blocks or DPI, to stay portable, but that is
  untested.
* **Timing.**  The Lean bench and the UVM bench agree on *what* is
  transferred, not on the cycle numbers: their pacing generators are
  different.  Cycle-exact agreement is what §8d.8 gives, between the
  JIT and Verilator.
* **Models.**  `Endpoint.ofModel` is untimed.  There is no
  approximately-timed or loosely-timed modelling, and no way to mix a
  model of one block with the RTL of another in one simulation.

## Exercises

1. Give `scaleStage` a second entry (a two-deep buffer).  Which of the
   tests above still pass unchanged?  What happens to the latencies in
   §8d.4?
2. Write a stage that withdraws `valid` after two cycles without a
   handshake, and make the monitor report it.
3. `paces` never stalls the consumer for more than two cycles.  Add a
   pacing that does (`.pattern`), and check `leakyStage` and
   `scaleStage` with it.
4. Change one element of `expected` in `stageUvm`, regenerate, run, and
   find the scoreboard message in the UVM log.

```lean
end Notebooks.Ch08d
```
