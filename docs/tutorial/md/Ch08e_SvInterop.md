
# Chapter 8e — Working with SystemVerilog: existing designs, AXI transactions, UVM

Chapter 8d tested Sparkle designs with a small ready/valid layer of our
own.  This chapter is about the other people in the room: designs that
are already written in SystemVerilog, and verification engineers who
already think in **transactions** — and mean something specific by it.

Three things, all aimed at interoperability:

1. **Load an existing SystemVerilog design** and get its ports by name
   (`Sv.Dut`).
2. **Test it with protocol transactions** — AXI4-Lite reads and writes,
   AXI4-Stream frames — through agents with the structure and the names an
   SV engineer knows.
3. **Go the other way**: give a Sparkle design the port names SV expects,
   instantiate it from an SV top, and generate a **UVM environment** for
   it from the same definitions.

## 8e.1 "Transaction", as SystemVerilog users mean it

Not our invention.  The vocabulary comes from the documents SV
verification engineers learn from, and this layer follows them:

| source | what it fixes |
|---|---|
| **UVM User's Guide** (Accellera, 1.2), ch. 3 "Developing Reusable Verification Components" | a *data item* (transaction) is a record of the protocol's fields; a *driver* turns items into pin activity; a *monitor* turns pins back into items and publishes them on an *analysis port*; a *scoreboard* subscribes; an *agent* bundles them per interface |
| UVM User's Guide, ch. 2 "Transaction-Level Modeling" | blocking put/get, analysis ports; the TLM-2 generic payload: command, address, data, byte enables, response |
| **cocotbext-axi** | the same idea driven from a host language (Python there, Lean here): `AxiLiteBus.from_prefix`, `AxiLiteMaster.read/write`, `AxiStreamSource.send`, `AxiStreamSink.recv`, `AxiStreamFrame`, `AxiLiteRam` |
| **AMBA AXI / AXI4-Stream specifications** | the handshake rules: once VALID is high it stays high, payload unchanged, until READY |

So a transaction is **one protocol operation as a record** — "write
0xDEADBEEF to 0x00 with byte enables 0xF, response OKAY", "a frame of 13
bytes" — not a cycle and not a pin.

| UVM | cocotbext-axi | here |
|---|---|---|
| sequence item | `AxiStreamFrame` | `AxiLiteTxn`, `AxiStreamFrame` |
| virtual interface | `AxiLiteBus.from_prefix(dut, "s_axil")` | `AxiLiteBus.fromPrefix dut.pins "s_axil"` |
| driver + sequencer | `AxiLiteMaster`, `AxiStreamSource` | `AxiLiteMaster`, `AxiStreamSource` |
| monitor + analysis port | `AxiStreamMonitor` | `AxiLiteMonitor`, `AxiStreamMonitor` → `AnalysisPort` |
| responder / slave model | `AxiStreamSink`, `AxiLiteRam` | `AxiStreamSink`, `AxiLiteRam` |
| scoreboard | user code | `AxiLiteMonitor.memoryScoreboard`, list comparison |
| back-pressure | `set_pause_generator` | `Pace` (Chapter 8d) |

```lean
import Sparkle
import Sparkle.Core.SimSv
import Sparkle.Verification.TlmAxi
import Sparkle.Verification.TlmAxiUvm

open Sparkle.Core.Sim
open Sparkle.Verification.Tlm

namespace Notebooks.Ch08e

```

The cells below need `verilator` on the PATH and run from the repository
root; without it they print a notice and do nothing.

## 8e.2 Loading a design that is not ours

`Examples/SvInterop/rtl/axil_regs.sv` is an AXI4-Lite register block in
ordinary SystemVerilog: `always_ff`, a clock called `aclk`, an active-low
`aresetn`, four registers, a read-only ID word, SLVERR for anything else.
Nothing in it knows about Sparkle.

```lean
def regs : Sv.Config :=
  { sources := ["Examples/SvInterop/rtl/axil_regs.sv"], top := "axil_regs"
    clock := "aclk", reset := some "aresetn", resetActiveHigh := false }

#eval do
  if !(← Sv.available) then
    IO.println "verilator not found — skipped"
  else
    let dut ← Sv.Dut.load regs
    IO.println s!"{dut.inputs.size} inputs, {dut.outputs.size} outputs"
    for p in dut.inputs.toList.take 3 do IO.println s!"  input  {p.name} [{p.width}]"
    for p in dut.outputs.toList.take 3 do IO.println s!"  output {p.name} [{p.width}]"
    Sim.destroy dut

```

```text
11 inputs, 9 outputs
  input  s_axil_awaddr [8]
  input  s_axil_awprot [3]
  input  s_axil_awvalid [1]
  output s_axil_awready [1]
  output s_axil_wready [1]
  output s_axil_bresp [2]
```

The port list was not typed in.  `Sv.Dut.load` runs Verilator on the
sources, reads the ports — names, directions, widths, parameters already
resolved — from the model it generates, and builds a simulator with the
same interface as the JIT (Chapter 8b).  Clock and reset are driven for
you; their names and the reset polarity are configuration.  A wrong name
is an error that lists the ports the design does have.

## 8e.3 AXI4-Lite: reads and writes

Bind the bus by its prefix, attach a master agent, and speak in accesses:

```lean
#eval do
  if !(← Sv.available) then
    IO.println "verilator not found — skipped"
  else
    let dut ← Sv.Dut.load regs
    let b ← Bench.new dut dut.idle (maxCycles := 2000)
    let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
    let m ← AxiLiteMaster.new b bus { b := .every 3 }     -- slow to accept responses
    let mon ← AxiLiteMonitor.new b bus                    -- passive: watches the pins
    let _ ← AxiLiteMonitor.memoryScoreboard b mon 4       -- subscribes to the monitor
    -- a sequence
    let _ ← m.writeWord 0x00 0xDEADBEEF none
    let _ ← m.writeWord 0x00 0x0000AA00 (some 0b0010)     -- one byte lane
    let (d, _) ← m.readWord 0x00
    let _ ← m.write 0x05 #[0x11, 0x22, 0x33, 0x44, 0x55]  -- bytes, unaligned, two words
    let (bytes, _) ← m.read 0x04 8
    let (_, resp) ← m.readWord 0x40                       -- nothing there
    IO.println s!"0x00 = {hex d};  bytes at 0x04 = {bytes};  read of 0x40: {resp}"
    IO.println "what the monitor saw:"
    for t in ← mon.items do IO.println s!"  {t}"
    IO.println s!"scoreboard / protocol errors: {(← b.report).errors}"
    Sim.destroy dut

```

```text
0x00 = 0xdeadaaef;  bytes at 0x04 = #[0, 17, 34, 51, 68, 85, 0, 0];  read of 0x40: SLVERR
what the monitor saw:
  WRITE 0x0 := 0xdeadbeef strb 0xf
  WRITE 0x0 := 0xaa00 strb 0x2
  READ 0x0 = 0xdeadaaef
  WRITE 0x4 := 0x33221100 strb 0xe
  WRITE 0x8 := 0x5544 strb 0x3
  READ 0x4 = 0x33221100
  READ 0x8 = 0x5544
  READ 0x40 = 0x0 (SLVERR)
scoreboard / protocol errors: [cycle 21: scoreboard: READ 0x40 = 0x0 (SLVERR)]
```

(The five-byte write at 0x05 became two bus accesses: three bytes of the
word at 0x04 with byte enables 0xE, two of the word at 0x08 with 0x3.)

Reading it against §8e.1:

* `AxiLiteBus.fromPrefix dut.pins "s_axil"` finds `s_axil_awaddr`,
  `s_axil_wdata`, … on the design.  Optional signals (`awprot`, `wstrb`,
  `bresp`, …) are used if they exist.
* `AxiLiteMaster` is driver + sequencer: `writeWord` puts an address on
  AW and data on W, and returns when B has answered.  `write` / `read`
  take bytes at any address and split them into bus words with byte
  enables.
* `AxiLiteMonitor` drives nothing.  It watches the five channels and
  writes one `AxiLiteTxn` per completed access to its `AnalysisPort` —
  the list printed above.  It also checks the handshake rules.
* The scoreboard is a subscriber: it remembers what was written and
  checks every byte read back.  The SLVERR access is the one thing it
  reports.

### The scoreboard earning its keep

The same file built with `HONOR_WSTRB = 0` ignores the byte enables — the
kind of bug a directed read-back of whole words never sees:

```lean
#eval do
  if !(← Sv.available) then
    IO.println "verilator not found — skipped"
  else
    let dut ← Sv.Dut.load { regs with params := [("HONOR_WSTRB", 0)] }
    let b ← Bench.new dut dut.idle (maxCycles := 2000)
    let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
    let m ← AxiLiteMaster.new b bus
    let mon ← AxiLiteMonitor.new b bus
    let _ ← AxiLiteMonitor.memoryScoreboard b mon 4
    let _ ← m.writeWord 0x04 0xCAFEF00D none
    let _ ← m.writeWord 0x04 0x000000EE (some 0b0001)
    let _ ← m.readWord 0x04
    for e in (← b.report).errors do IO.println e
    Sim.destroy dut

```

```text
cycle 7: scoreboard: READ 0x4 = 0xee: byte at 0x5 is 0x0, expected 0xf0
cycle 7: scoreboard: READ 0x4 = 0xee: byte at 0x6 is 0x0, expected 0xfe
cycle 7: scoreboard: READ 0x4 = 0xee: byte at 0x7 is 0x0, expected 0xca
```

## 8e.4 AXI4-Stream: frames

A stream transaction is a **frame**: the bytes between two `tlast`.  The
source packs bytes into transfers of whatever width the bus has (with
`tkeep` on a partial last one); the sink and the monitor unpack them.
That makes a width converter trivial to test — frames in, the same
frames out:

```text
let src ← AxiStreamSource.new b (← AxiStreamBus.fromPrefix dut.pins "s_axis") (.random 6 60)
let snk ← AxiStreamSink.new   b (← AxiStreamBus.fromPrefix dut.pins "m_axis") (.random 7 40)
for f in frames do src.send f
let got ← frames.mapM fun _ => snk.recv
```

`Tests/SvInteropTest.lean` runs exactly this on `axis_adapter` from
verilog-axis, 8 → 32 bits and 32 → 8 bits, nine frames of 1 to 16 bytes,
with gaps and back-pressure.

## 8e.5 A design that is the master: PicoRV32

When the design issues the accesses, the testbench is the slave.
`AxiLiteRam` is a memory behind an AXI4-Lite interface; PicoRV32's
`picorv32_axi` runs a program out of it:

```text
let dut ← Sv.Dut.load { sources := ["…/picorv32.v"], top := "picorv32_axi"
                        reset := some "resetn", resetActiveHigh := false }
let bus ← AxiLiteBus.fromPrefix dut.pins "mem_axi"
let ram ← AxiLiteRam.new b bus { ar := .random 9 70, r := .random 10 70 }
let mon ← AxiLiteMonitor.new b bus
ram.loadWords 0 program          -- sum 1..10, storing each partial sum
```

The monitor's transactions *are* the program's memory accesses: 54
instruction fetches, each returning the instruction at that address, and
eleven writes — the ten partial sums 1, 3, 6, … 55 to 0x100 and the total
to 0x104.  A CPU's bus trace, read as a list of records.

## 8e.6 The other direction: a Sparkle design in an SV world

Sparkle names inputs after the Lean binders (`_gen_inData`) and packs a
tuple result into one `out`.  To be instantiated from SystemVerilog, or
bound by prefix, a design needs the conventional names.
`Sparkle.Backend.SvWrapper` writes the thin module that renames:

```text
def axisScaleWrapper : SvWrapper.Wrapper :=
  { name := "axis_scale", inner := "Sparkle_Tests_SvInteropTest_axisScale"
    innerOutputs := [("out", 39)]
    inputs := [ ("s_axis_tdata", 32, "_gen_inData"), ("s_axis_tvalid", 1, "_gen_inValid"), … ]
    outputs := [ ("s_axis_tready", 1, "out_w[38]"), ("m_axis_tdata", 32, "out_w[31:0]"), … ] }
```

After that the Sparkle design is just another SystemVerilog module:

* loaded with `Sv.Dut.load` and tested with the same AXI4-Stream agents;
* instantiated from `Examples/SvInterop/rtl/sparkle_in_sv_top.sv` between
  two third-party width adapters — bytes in, bytes out, an ordinary SV
  file that does not know which of its three instances came from Lean.

## 8e.7 A UVM environment from the same definitions

For a team whose flow is UVM, generate the environment.  The bus shape
comes from the design's ports; the sequence is the one the Lean test
ran; the expected transactions are what the Lean monitor reported:

```lean
#eval do
  if !(← Sv.available) then
    IO.println "verilator not found — skipped"
  else
    let dut ← Sv.Dut.load regs
    let b ← Bench.new dut dut.idle (maxCycles := 2000)
    let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
    let m ← AxiLiteMaster.new b bus
    let mon ← AxiLiteMonitor.new b bus
    let seq : List AxiLiteTxn :=
      [ { write := true,  addr := 0x00, data := 0xDEADBEEF, strb := 0xF }
      , { write := true,  addr := 0x00, data := 0x0000AA00, strb := 0x2 }
      , { write := false, addr := 0x00, data := 0, strb := 0xF } ]
    m.run seq                                   -- the Lean run
    let bench := { Uvm.AxiBench.ofDut "regs_tb" regs dut with
                   axil := [("s_axil", seq, ← mon.items)] }
    match Uvm.emitAxi bench with
    | .error e => IO.println e
    | .ok tb =>
      IO.FS.createDirAll ".lake/build/gen/uvm"
      IO.FS.writeFile ".lake/build/gen/uvm/ch08e_regs_tb.sv" tb
      for l in (tb.splitOn "\n").filter (fun (l : String) => (l.splitOn "  class ").length > 1) do
        IO.println l
    Sim.destroy dut

```

```text
  class s_axil_item extends uvm_sequence_item;
  class s_axil_seq extends uvm_sequence #(s_axil_item);
  class s_axil_driver extends uvm_driver #(s_axil_item);
  class s_axil_monitor extends uvm_monitor;
  class s_axil_scoreboard extends uvm_scoreboard;
  class regs_tb_env extends uvm_env;
  class regs_tb_test extends uvm_test;
```

The classes are the ones of the UVM User's Guide's chapter 3: the item
has the protocol's fields (`write`, `addr`, `data`, `strb`, `resp`), the
driver is the `get_next_item` / `drive_item` / `item_done` loop, the
monitor has an analysis port, the scoreboard subscribes.

`SPARKLE_UVM_HOME=<uvm-core> lake exe tlm-uvm-test` compiles and runs
the generated environments with Verilator:

```text
[uvm] axil_regs_tb: clean run as expected (UVM_ERROR 0, scoreboard pass: true) ✓
[uvm] axil_regs_bug_tb: scoreboard errors as expected (UVM_ERROR 2, scoreboard pass: false) ✓
[uvm] axis_scale_tb: clean run as expected (UVM_ERROR 0, scoreboard pass: true) ✓
[uvm] axil_ram_tb: clean run as expected (UVM_ERROR 0, scoreboard pass: true) ✓
[uvm] axis_adapter_tb: clean run as expected (UVM_ERROR 0, scoreboard pass: true) ✓
```

Because the expected transactions come from the Lean run, the two
simulations of one test must agree transaction for transaction — and the
block that ignores `wstrb` fails in UVM against what the correct one did.

## 8e.8 Limits

* **Simulator.**  Existing designs are simulated by Verilator, so it has
  to be installed; whatever Verilator cannot compile cannot be loaded.
  One clock per design.
* **Ports.**  Flat ports only.  A design whose ports are of an SV
  `interface` type needs a wrapper with flat ports.
* **Protocols.**  AXI4-Lite and AXI4-Stream.  No AXI4 bursts or IDs, no
  APB.  `tid` / `tdest` / `tuser` are per frame (taken from the last
  transfer).
* **Stimulus.**  Directed: the sequence is a list.  No constrained-random
  generation and no functional coverage, in Lean or in the generated UVM.
* **UVM.**  Run with Verilator 5.052 and Accellera's uvm-core only; no
  commercial simulator was available.  No clocking blocks, no DPI, no
  register model.
* **Third-party designs** are fetched by `Examples/SvInterop/fetch.sh` at
  pinned commits and are not part of the repository; the tests that use
  them are skipped until it has been run.

## Exercises

1. Add a fifth register to `axil_regs.sv`.  Which checks in
   `Tests/SvInteropTest.lean` change, and which do not need to?
2. Bind `AxiLiteRam` to `axil_regs`.  Read the error message; explain it
   in terms of who drives `awvalid`.
3. Write a scoreboard for `axis_adapter` as an `AnalysisPort` subscriber:
   frames on `s_axis` and on `m_axis` must be equal, in order.
4. Make PicoRV32 compute something else, and predict the write
   transactions before you run it.

```lean
end Notebooks.Ch08e
```
