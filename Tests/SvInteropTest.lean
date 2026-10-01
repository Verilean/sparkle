/-
  SystemVerilog interoperability: designs that were NOT written in Sparkle,
  loaded with Verilator (`Sv.Dut`) and tested with transactions
  (`Sparkle/Verification/TlmAxi.lean`).

  Always (needs `verilator`):
    1. `Examples/SvInterop/rtl/axil_regs.sv` — an AXI4-Lite register block in
       ordinary SystemVerilog (`aclk`, active-low `aresetn`): word and
       byte-level reads and writes, SLVERR on a bad address, the monitor's
       transaction list, the memory scoreboard; and the same block built
       with HONOR_WSTRB=0, which the scoreboard must catch.
    2. Binding and loading errors: what the message says when a prefix, a
       role or a clock name is wrong.  The UVM environment generated for
       the register block (`Uvm.emitAxi`): bus shape taken from the
       design, sequence and expected transactions from the Lean run.
       (Running it: `lake exe tlm-uvm-test`.)
    3. The other direction: a design written in the Sparkle DSL, emitted as
       Verilog, wrapped with AXI4-Stream port names (`SvWrapper`), loaded
       like any other SystemVerilog and tested with the same agents.
  When `Examples/SvInterop/fetch.sh` has been run (third-party designs):
    4. verilog-axi `axil_ram` — reads and writes under five channel pacings.
    5. verilog-axis `axis_adapter`, 8 → 32 bits and 32 → 8 bits — frames
       survive the width change, under back-pressure.
    6. PicoRV32 (`picorv32_axi`, an AXI4-Lite MASTER) running a program out
       of an `AxiLiteRam`: its bus activity, as transactions, is the
       program's memory accesses.
    7. The Sparkle design instantiated from a SystemVerilog top between two
       third-party adapters: bytes in, bytes out.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitDo
import Sparkle.Core.SimSv
import Sparkle.Verification.TlmAxi
import Sparkle.Verification.TlmAxiUvm
import Sparkle.Backend.SvWrapper

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Sim
open Sparkle.Verification.Tlm

namespace Sparkle.Tests.SvInteropTest

def check (label : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then IO.println s!"  PASS {label}" else IO.println s!"  FAIL {label} {detail}"
  return ok

def thirdParty : String := "Examples/SvInterop/third_party"

/-- bytes `k, k+1, …` -/
def bytesFrom (k n : Nat) : Array UInt8 := (Array.range n).map fun j => ((k + j * 7) % 256).toUInt8

/-! ### A design written in Sparkle, for the SystemVerilog side to use -/

/-- One-entry AXI4-Stream stage computing `3·x + 1` on each 32-bit word;
    `tkeep` and `tlast` travel with the data.
    Output: `inReady ++ outValid ++ outLast ++ outKeep ++ outData` (39 bits). -/
def axisScale (inValid : Signal defaultDomain Bool) (inData : Signal defaultDomain (BitVec 32))
    (inKeep : Signal defaultDomain (BitVec 4)) (inLast : Signal defaultDomain Bool)
    (outReady : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 39) :=
  circuit do
    let full ← Signal.reg false
    let data ← Signal.reg 0#32
    let keep ← Signal.reg 0#4
    let last ← Signal.reg false
    let fullS := (full : Signal defaultDomain Bool)
    let dataS := (data : Signal defaultDomain (BitVec 32))
    let keepS := (keep : Signal defaultDomain (BitVec 4))
    let lastS := (last : Signal defaultDomain Bool)
    let inReady := Signal.mux fullS outReady (Signal.pure true)
    let accept := inValid &&& inReady
    full <~ Signal.mux accept (Signal.pure true) (Signal.mux outReady (Signal.pure false) fullS)
    data <~ Signal.mux accept (inData * 3#32 + 1#32) dataS
    keep <~ Signal.mux accept inKeep keepS
    last <~ Signal.mux accept inLast lastS
    return (Signal.mux inReady (Signal.pure 1#1) (Signal.pure 0#1)) ++
           ((Signal.mux fullS (Signal.pure 1#1) (Signal.pure 0#1)) ++
            ((Signal.mux lastS (Signal.pure 1#1) (Signal.pure 0#1)) ++ (keepS ++ dataS)))

section SynthesisChecks
#writeVerilogDesign axisScale ".lake/build/gen/sv/axis_scale_core.sv"
end SynthesisChecks

/-- The same design under the names an AXI4-Stream user expects. -/
def axisScaleWrapper : Sparkle.Backend.SvWrapper.Wrapper :=
  { name := "axis_scale", inner := "Sparkle_Tests_SvInteropTest_axisScale"
    innerOutputs := [("out", 39)]
    inputs := [ ("s_axis_tdata", 32, "_gen_inData"), ("s_axis_tkeep", 4, "_gen_inKeep")
              , ("s_axis_tvalid", 1, "_gen_inValid"), ("s_axis_tlast", 1, "_gen_inLast")
              , ("m_axis_tready", 1, "_gen_outReady") ]
    outputs := [ ("s_axis_tready", 1, "out_w[38]"), ("m_axis_tvalid", 1, "out_w[37]")
               , ("m_axis_tlast", 1, "out_w[36]"), ("m_axis_tkeep", 4, "out_w[35:32]")
               , ("m_axis_tdata", 32, "out_w[31:0]") ] }

def wrapperPath : String := ".lake/build/gen/sv/axis_scale.sv"

/-- What the stage does to a frame whose length is a multiple of 4 bytes:
    each little-endian 32-bit word becomes 3·w + 1. -/
def scaleFrame (f : AxiStreamFrame) : AxiStreamFrame :=
  { f with tdata := Id.run do
      let mut out : Array UInt8 := #[]
      for k in [0:f.tdata.size / 4] do
        let w := (List.range 4).foldl (fun acc j => acc + (f.tdata.getD (4 * k + j) 0).toNat <<< (8 * j)) 0
        let y := (3 * w + 1) % 4294967296
        for j in [0:4] do out := out.push ((y >>> (8 * j)) % 256).toUInt8
      return out }

def wordFrames : List AxiStreamFrame :=
  [4, 8, 4, 16, 12].zipIdx.map fun (len, k) => { tdata := bytesFrom (k * 29 + 5) len }

/-! ### 1. The in-repo register block -/

def regsConfig (honorStrb : Bool) : Sv.Config :=
  { sources := ["Examples/SvInterop/rtl/axil_regs.sv"], top := "axil_regs"
    clock := "aclk", reset := some "aresetn", resetActiveHigh := false
    params := [("HONOR_WSTRB", if honorStrb then 1 else 0)] }

def regsTest : IO Bool := do
  let mut ok := true
  let dut ← Sv.Dut.load (regsConfig true)
  ok := (← check s!"axil_regs: ports read from the design ({dut.inputs.size} inputs, {dut.outputs.size} outputs)"
    (dut.inputIndex? "s_axil_awaddr" |>.isSome) s!"{dut.portNames}") && ok
  let b ← Bench.new dut dut.idle (maxCycles := 2000)
  let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
  let m ← AxiLiteMaster.new b bus { aw := .every 3, b := .random 4 60, r := .every 2 }
  let mon ← AxiLiteMonitor.new b bus
  -- (no `unwritten` value: this is a register block, and 0x10 is not memory)
  let checked ← AxiLiteMonitor.memoryScoreboard b mon 4
  -- whole words
  let r0 ← m.writeWord 0x00 0xDEADBEEF none
  let r1 ← m.writeWord 0x0C 0x12345678 none
  let (d0, _) ← m.readWord 0x00
  let (d3, _) ← m.readWord 0x0C
  ok := (← check "axil_regs: write then read back two registers"
    (r0 == .okay && r1 == .okay && d0 == 0xDEADBEEF && d3 == 0x12345678) s!"{hex d0} {hex d3}") && ok
  -- one byte of a word: the others keep their value
  let _ ← m.writeWord 0x00 0x0000AA00 (some 0b0010)
  let (d0', _) ← m.readWord 0x00
  ok := (← check "axil_regs: a byte-enabled write changes one byte" (d0' == 0xDEADAAEF) (hex d0')) && ok
  -- bytes at an unaligned address, across two registers
  let _ ← m.write 0x05 #[0x11, 0x22, 0x33, 0x44, 0x55]
  let (bytes, _) ← m.read 0x04 8
  ok := (← check "axil_regs: byte-level write across two words, read back"
    (bytes == #[0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x00, 0x00]) s!"{bytes}") && ok
  -- the identification word, and a write to it
  let (ident, ri) ← m.readWord 0x10
  let rw ← m.writeWord 0x10 0 none
  let (_, rbad) ← m.readWord 0x40
  ok := (← check "axil_regs: ID readable; write to it and read of 0x40 answer SLVERR"
    (ident == 0x53504B4C && ri == .okay && rw == .slverr && rbad == .slverr)
    s!"{hex ident} {ri} {rw} {rbad}") && ok
  -- the design's own output pin follows register 0
  let o ← Sim.read dut
  ok := (← check "axil_regs: output pin reg0_o shows register 0"
    ((dut.pins.find "reg0_o").map (·.get dut.idle o) == some 0xDEADAAEF)) && ok
  -- what the monitor saw: one transaction per access, in completion order
  let txns ← mon.items
  let writes := txns.filter (·.write)
  ok := (← check s!"axil_regs: monitor reconstructed {txns.length} transactions ({writes.length} writes)"
    (txns.length == 13 && writes.length == 6 &&
     txns.head? == some { write := true, addr := 0x00, data := 0xDEADBEEF, strb := 0xF } &&
     writes[2]? == some { write := true, addr := 0x00, data := 0x0000AA00, strb := 0b0010 })
    s!"{txns.map toString}") && ok
  -- the scoreboard: the SLVERR accesses are its only complaints
  let errs := (← b.report).errors
  ok := (← check s!"axil_regs: scoreboard checked {← checked.get} bytes; only the 2 SLVERR accesses reported"
    ((← checked.get) ≥ 15 && errs.length == 2 && errs.all fun e => (e.splitOn "SLVERR").length > 1)
    s!"{errs}") && ok
  Sim.destroy dut
  -- the block that ignores wstrb
  let bad ← Sv.Dut.load (regsConfig false)
  let b ← Bench.new bad bad.idle (maxCycles := 2000)
  let bus ← AxiLiteBus.fromPrefix bad.pins "s_axil"
  let m ← AxiLiteMaster.new b bus
  let mon ← AxiLiteMonitor.new b bus
  let _ ← AxiLiteMonitor.memoryScoreboard b mon 4
  let _ ← m.writeWord 0x04 0xCAFEF00D none
  let _ ← m.writeWord 0x04 0x000000EE (some 0b0001)
  let _ ← m.readWord 0x04
  let errs := (← b.report).errors
  ok := (← check "axil_regs built with HONOR_WSTRB=0: the scoreboard reports the clobbered bytes"
    (errs.length == 3 && errs.all fun e => (e.splitOn "expected").length > 1) s!"{errs}") && ok
  Sim.destroy bad
  return ok

/-! ### 2. Scoreboard and binding errors -/

def bindingTest : IO Bool := do
  let mut ok := true
  let dut ← Sv.Dut.load (regsConfig true)
  let msg (act : IO Unit) : IO String := do
    try act; return "" catch e => return toString e
  let e1 ← msg (do let _ ← AxiLiteBus.fromPrefix dut.pins "m_axil")
  ok := (← check "binding: an unknown prefix names the design and lists its ports"
    ((e1.splitOn "has no signal 'm_axil_awaddr'").length > 1 && (e1.splitOn "s_axil_awaddr").length > 1) e1) && ok
  let e2 ← msg (do let _ ← AxiStreamBus.fromPrefix dut.pins "s_axil")
  ok := (← check "binding: AXI-Stream on an AXI-Lite prefix lists the signals with that prefix"
    ((e2.splitOn "has no signal 's_axil_tdata'").length > 1 && (e2.splitOn "Signals with that prefix").length > 1) e2) && ok
  -- the wrong role: this design is a slave, so a RAM (a slave agent) cannot bind
  let b ← Bench.new dut dut.idle
  let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
  let e3 ← msg (do let _ ← AxiLiteRam.new b bus)
  ok := (← check "binding: a slave agent on a slave interface is refused, with the signal named"
    ((e3.splitOn "is an INPUT of the design").length > 1 && (e3.splitOn "s_axil_awvalid").length > 1) e3) && ok
  Sim.destroy dut
  let e4 ← msg (do let _ ← Sv.Dut.load { regsConfig true with clock := "clk" })
  ok := (← check "loading: a wrong clock name is reported with the design's ports"
    ((e4.splitOn "no input port 'clk'").length > 1 && (e4.splitOn "aclk").length > 1) e4) && ok
  return ok

/-- The UVM environment for the register block, generated from the design
    and a Lean run. -/
def uvmShapeTest : IO Bool := do
  let mut ok := true
  let cfg := regsConfig true
  let dut ← Sv.Dut.load cfg
  let b ← Bench.new dut dut.idle (maxCycles := 2000)
  let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
  let m ← AxiLiteMaster.new b bus
  let mon ← AxiLiteMonitor.new b bus
  let seq : List AxiLiteTxn :=
    [ { write := true, addr := 0x00, data := 0xDEADBEEF, strb := 0xF }
    , { write := false, addr := 0x00, data := 0, strb := 0xF }
    , { write := false, addr := 0x40, data := 0, strb := 0xF } ]
  m.run seq
  let expected ← mon.items
  let bench := { Uvm.AxiBench.ofDut "regs_tb" cfg dut with axil := [("s_axil", seq, expected)] }
  let tb := match Uvm.emitAxi bench with
    | .ok t => t
    | .error e => s!"ERROR {e}"
  let has := fun (sub : String) => (tb.splitOn sub).length > 1
  ok := (← check "UVM: interface with the design's signals and widths"
    (has "interface s_axil_if (input logic clk);" && has "  logic [7:0] awaddr;" &&
     has "  logic [31:0] wdata;" && has "  logic [3:0] wstrb;" && has "  logic [1:0] bresp;")) && ok
  ok := (← check "UVM: the transaction is a sequence item with the protocol's fields"
    (has "class s_axil_item extends uvm_sequence_item;" && has "    rand bit [7:0] addr;" &&
     has "    rand bit [3:0] strb;" && has "    bit [1:0] resp;")) && ok
  ok := (← check "UVM: driver, monitor with analysis port, scoreboard, env, test"
    (has "class s_axil_driver extends uvm_driver #(s_axil_item);" &&
     has "seq_item_port.get_next_item(req);" &&
     has "uvm_analysis_port #(s_axil_item) ap;" &&
     has "class s_axil_scoreboard extends uvm_scoreboard;" &&
     has "class regs_tb_env extends uvm_env;" && has "run_test(\"regs_tb_test\");")) && ok
  ok := (← check "UVM: the design instantiated by port name, with its parameters, clock and active-low reset"
    (has "axil_regs #(.HONOR_WSTRB(1)) dut (.aclk(clk), .aresetn(rst), .s_axil_awaddr(s_axil_bus.awaddr)," &&
     has ".reg0_o()" && has "logic rst = 1'b0;")) && ok
  ok := (← check "UVM: the sequence is the Lean sequence, the expected items are what the Lean monitor saw"
    (has "s_axil_s.add(1, 64'h0, 64'hdeadbeef, 'hf);" &&
     has "env.s_axil_sb.expect_item(1, 64'h0, 64'hdeadbeef, 'hf, 0);" &&
     has "env.s_axil_sb.expect_item(0, 64'h0, 64'hdeadbeef, 'hf, 0);" &&
     has "env.s_axil_sb.expect_item(0, 64'h40, 64'h0, 'hf, 2);")) && ok
  let bad := Uvm.emitAxi { bench with axil := [("m_axil", seq, expected)] }
  ok := (← check "UVM: a prefix the design does not have is an error"
    (match bad with | .error e => (e.splitOn "has no signal 'm_axil_awaddr'").length > 1 | .ok _ => false)) && ok
  Sim.destroy dut
  return ok

/-! ### 3. A Sparkle design behind SystemVerilog names -/

def sparkleAsSvTest : IO Bool := do
  let mut ok := true
  IO.FS.writeFile wrapperPath (Sparkle.Backend.SvWrapper.emit axisScaleWrapper)
  let dut ← Sv.Dut.load
    { sources := [wrapperPath, ".lake/build/gen/sv/axis_scale_core.sv"], top := "axis_scale" }
  for (label, inPace, outPace) in
      [("no back-pressure", Pace.always, Pace.always), ("gaps and back-pressure", .random 11 50, .random 12 40)] do
    let b ← Bench.new dut dut.idle (maxCycles := 2000)
    let src ← AxiStreamSource.new b (← AxiStreamBus.fromPrefix dut.pins "s_axis") inPace
    let snk ← AxiStreamSink.new b (← AxiStreamBus.fromPrefix dut.pins "m_axis") outPace
    for f in wordFrames do src.send f
    let mut got : List AxiStreamFrame := []
    for _ in wordFrames do
      if let some f ← snk.recv then got := got ++ [f]
    let rep ← b.report
    ok := (← check s!"Sparkle design as `axis_scale`: {wordFrames.length} frames come out as 3x+1 per word, {label} ({rep.cycles} cycles)"
      (got == wordFrames.map scaleFrame && rep.ok) s!"{got.length} frames; {rep.errors.take 3}") && ok
  Sim.destroy dut
  return ok

/-- The Sparkle design between two third-party width adapters, instantiated
    from an ordinary SystemVerilog top. -/
def sparkleInSvTopTest : IO Bool := do
  let mut ok := true
  let dut ← Sv.Dut.load
    { sources := [ "Examples/SvInterop/rtl/sparkle_in_sv_top.sv", wrapperPath
                 , ".lake/build/gen/sv/axis_scale_core.sv"
                 , s!"{thirdParty}/verilog-axis/rtl/axis_adapter.v" ]
      top := "sparkle_in_sv_top" }
  let b ← Bench.new dut dut.idle (maxCycles := 5000)
  let src ← AxiStreamSource.new b (← AxiStreamBus.fromPrefix dut.pins "s_axis") (.random 13 70)
  let snk ← AxiStreamSink.new b (← AxiStreamBus.fromPrefix dut.pins "m_axis") (.random 14 50)
  for f in wordFrames do src.send f
  let mut got : List AxiStreamFrame := []
  for _ in wordFrames do
    if let some f ← snk.recv then got := got ++ [f]
  let rep ← b.report
  ok := (← check s!"SystemVerilog top = adapter 8→32 + Sparkle stage + adapter 32→8: bytes in, 3x+1 per word out ({rep.cycles} cycles)"
    (got == wordFrames.map scaleFrame && rep.ok) s!"{got.length} frames; {rep.errors.take 3}") && ok
  Sim.destroy dut
  return ok

/-! ### 4. verilog-axi: AXI4-Lite RAM -/

def axilRamTest : IO Bool := do
  let mut ok := true
  let dut ← Sv.Dut.load
    { sources := [s!"{thirdParty}/verilog-axi/rtl/axil_ram.v"], top := "axil_ram"
      params := [("ADDR_WIDTH", 12)] }
  let paces : List (String × AxiLitePace) :=
    [ ("no gaps", {})
    , ("address late", { aw := .every 4 })
    , ("data late", { w := .every 4 })
    , ("slow responses", { b := .every 3, r := .every 3 })
    , ("everything random", { aw := .random 1 50, w := .random 2 50, b := .random 3 50
                              ar := .random 4 50, r := .random 5 50 }) ]
  let mut seed := 0
  for (label, pace) in paces do
    seed := seed + 1
    let b ← Bench.new dut dut.idle (maxCycles := 20000)
    let bus ← AxiLiteBus.fromPrefix dut.pins "s_axil"
    let m ← AxiLiteMaster.new b bus pace
    let mon ← AxiLiteMonitor.new b bus
    let checked ← AxiLiteMonitor.memoryScoreboard b mon 4
    -- writes of 1..9 bytes at unaligned addresses, then everything read back
    let mut good := true
    for k in [0:12] do
      let addr := 0x100 * seed + k * 13 + 1
      let data := bytesFrom (seed * 31 + k) (k % 9 + 1)
      let _ ← m.write addr data
      let (back, resp) ← m.read addr data.size
      if back != data || resp != .okay then good := false
    let rep ← b.report
    ok := (← check s!"axil_ram: 12 byte-level writes read back, {label} ({rep.cycles} cycles, {(← mon.items).length} transactions, {← checked.get} bytes checked)"
      (good && rep.ok && (← checked.get) > 50) s!"{rep.errors.take 3}") && ok
  Sim.destroy dut
  return ok

/-! ### 5. verilog-axis: width adapter -/

def frames : List AxiStreamFrame :=
  [1, 3, 4, 5, 8, 13, 2, 16, 7].zipIdx.map fun (len, k) =>
    { tdata := bytesFrom (k * 17 + 3) len, tuser := k % 2 }

def adapterTest (sWidth mWidth : Nat) : IO Bool := do
  let mut ok := true
  let dut ← Sv.Dut.load
    { sources := [s!"{thirdParty}/verilog-axis/rtl/axis_adapter.v"], top := "axis_adapter"
      params := [("S_DATA_WIDTH", sWidth), ("M_DATA_WIDTH", mWidth),
                 ("S_KEEP_ENABLE", 1), ("M_KEEP_ENABLE", 1)] }
  for (label, inPace, outPace) in
      [("no back-pressure", Pace.always, Pace.always), ("gaps and back-pressure", .random 6 60, .random 7 40)] do
    let b ← Bench.new dut dut.idle (maxCycles := 5000)
    let sBus ← AxiStreamBus.fromPrefix dut.pins "s_axis"
    let mBus ← AxiStreamBus.fromPrefix dut.pins "m_axis"
    let src ← AxiStreamSource.new b sBus inPace
    let snk ← AxiStreamSink.new b mBus outPace
    let monIn ← AxiStreamMonitor.new b sBus
    let monOut ← AxiStreamMonitor.new b mBus
    for f in frames do src.send f
    let mut got : List AxiStreamFrame := []
    for _ in frames do
      if let some f ← snk.recv then got := got ++ [f]
    let rep ← b.report
    ok := (← check s!"axis_adapter {sWidth} → {mWidth} bits: {frames.length} frames (1..16 bytes) arrive intact, {label} ({rep.cycles} cycles)"
      (got == frames && rep.ok) s!"got {got.length} frames; {rep.errors.take 3}") && ok
    ok := (← check "  passive monitors on both sides see the same frames"
      ((← monIn.items) == frames && (← monOut.items) == frames && (← src.sent.items) == frames)) && ok
  Sim.destroy dut
  return ok

/-! ### 6. PicoRV32: a CPU as an AXI4-Lite master -/

namespace Rv32

def addi (rd rs1 : Nat) (imm : Int) : Nat :=
  ((imm % 4096).toNat <<< 20) ||| (rs1 <<< 15) ||| (rd <<< 7) ||| 0x13
def add (rd rs1 rs2 : Nat) : Nat := (rs2 <<< 20) ||| (rs1 <<< 15) ||| (rd <<< 7) ||| 0x33
def sw (rs2 rs1 imm : Nat) : Nat :=
  ((imm / 32) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (2 <<< 12) ||| ((imm % 32) <<< 7) ||| 0x23
def bne (rs1 rs2 : Nat) (off : Int) : Nat :=
  let u := (off % 8192).toNat
  (((u >>> 12) % 2) <<< 31) ||| (((u >>> 5) % 64) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15)
    ||| (1 <<< 12) ||| (((u >>> 1) % 16) <<< 8) ||| (((u >>> 11) % 2) <<< 7) ||| 0x63
def ebreak : Nat := 0x00100073

/-- sum = 1 + 2 + … + 10, every partial sum stored at 0x100, the total at
    0x104, then stop. -/
def program : List Nat :=
  [ addi 1 0 0          -- 0x00  sum = 0
  , addi 2 0 1          -- 0x04  i = 1
  , addi 3 0 11         -- 0x08  limit
  , add 1 1 2           -- 0x0c  loop: sum += i
  , sw 1 0 0x100        -- 0x10        mem[0x100] = sum
  , addi 2 2 1          -- 0x14        i += 1
  , bne 2 3 (-12)       -- 0x18        if i != limit goto loop
  , sw 1 0 0x104        -- 0x1c  mem[0x104] = sum
  , ebreak ]            -- 0x20

end Rv32

def picoTest : IO Bool := do
  let mut ok := true
  let dut ← Sv.Dut.load
    { sources := [s!"{thirdParty}/picorv32/picorv32.v"], top := "picorv32_axi"
      reset := some "resetn", resetActiveHigh := false }
  let b ← Bench.new dut dut.idle (maxCycles := 20000)
  let bus ← AxiLiteBus.fromPrefix dut.pins "mem_axi"
  let ram ← AxiLiteRam.new b bus { ar := .random 9 70, r := .random 10 70, b := .every 2 }
  let mon ← AxiLiteMonitor.new b bus
  ram.loadWords 0 Rv32.program
  let trap ← dut.pins.pin "trap"
  let trapped : IO.Ref Bool ← IO.mkRef false
  b.agents.modify (·.push { name := "trap", drive := fun _ i => pure i
                            observe := fun _ i o => do
                              if trap.get i o != 0 then trapped.set true
                              return []
                            busy := return false })
  let done ← b.runUntil trapped.get "the program to reach ebreak"
  let rep ← b.report
  let txns ← mon.items
  let writes := txns.filter (·.write)
  let partialSums := [1, 3, 6, 10, 15, 21, 28, 36, 45, 55]
  let expected : List AxiLiteTxn :=
    partialSums.map (fun s => { write := true, addr := 0x100, data := s, strb := 0xF })
      ++ [{ write := true, addr := 0x104, data := 55, strb := 0xF }]
  ok := (← check s!"picorv32_axi: the program runs to its ebreak ({rep.cycles} cycles, {txns.length} bus transactions)"
    (done && rep.ok) s!"{rep.errors.take 3}") && ok
  ok := (← check "picorv32_axi: its writes, as transactions, are the program's stores (10 partial sums, then the total)"
    (writes == expected) s!"{writes.map toString}") && ok
  let fetches := txns.filter (!·.write)
  let fetchOk := fetches.all fun t => Rv32.program[t.addr / 4]? == some t.data
  ok := (← check s!"picorv32_axi: every one of its {fetches.length} reads fetched the instruction at that address"
    (fetchOk && (fetches.take 4).map (·.addr) == [0, 4, 8, 12])) && ok
  ok := (← check "picorv32_axi: the RAM holds 55 at 0x104"
    ((← ram.readByte 0x104) == 55 && (← ram.readByte 0x100) == 55)) && ok
  Sim.destroy dut
  return ok

def main : IO Unit := do
  IO.println "--- SystemVerilog interoperability ---"
  if !(← Sv.available) then
    IO.println "  SKIP (verilator not found)"
    return
  let mut ok := true
  ok := (← regsTest) && ok
  ok := (← bindingTest) && ok
  ok := (← uvmShapeTest) && ok
  ok := (← sparkleAsSvTest) && ok
  if ← System.FilePath.pathExists s!"{thirdParty}/verilog-axi/rtl/axil_ram.v" then
    ok := (← axilRamTest) && ok
    ok := (← adapterTest 8 32) && ok
    ok := (← adapterTest 32 8) && ok
    ok := (← picoTest) && ok
    ok := (← sparkleInSvTopTest) && ok
  else
    IO.println s!"  SKIP third-party designs (run Examples/SvInterop/fetch.sh)"
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.SvInteropTest
