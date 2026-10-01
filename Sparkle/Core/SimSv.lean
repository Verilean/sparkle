/-
  SimSv — simulate an EXISTING SystemVerilog / Verilog design.

  `#sim` simulates what Sparkle wrote.  This loads a design somebody else
  wrote — any source Verilator accepts — and exposes its ports BY NAME:

    let dut ← Sv.Dut.load { sources := ["rtl/axil_ram.v"], top := "axil_ram",
                            params := [("ADDR_WIDTH", 12)] }
    -- dut.inputs / dut.outputs : name, width — read from the elaborated design

  The port list is not typed in again: after `verilator --cc` the generated
  model header declares every port with its direction and range
  (`VL_IN16(&s_axil_awaddr,11,0)`), parameters already resolved.  The loader
  reads it, writes the wrapper that exposes the JIT C ABI
  (`Sparkle.Core.Sim.Verilator.emitTb`), builds, and loads the result.

  Clock and reset are driven by the wrapper; their names and the reset
  polarity are configuration (`aclk` / `aresetn` active low, …).  Every other
  port is a pin: `Pins` is one value per port, in `inputs` / `outputs` order.

  Timing is the JIT's (see `SimVerilator.lean`): `read` after `step` returns
  the outputs the design showed in the cycle the inputs were applied, before
  the clock edge.

  Limits: one clock; ports of an SV `interface` type are not supported
  (Verilator needs a wrapper with flat ports for those); `inout` ports are
  ignored.
-/
import Sparkle.Core.SimVerilator

namespace Sparkle.Core.Sim.Sv

open Sparkle.Core.JIT
open Sparkle.Core.Sim.Verilator (PortSpec emitTb buildAndLoad)

structure Port where
  name : String
  width : Nat
  isInput : Bool
  deriving Repr, BEq, Inhabited

structure Config where
  /-- source files, in the order Verilator should read them -/
  sources : List String
  top : String
  clock : String := "clk"
  /-- reset port, if the design has one -/
  reset : Option String := some "rst"
  resetActiveHigh : Bool := true
  /-- clock cycles the reset is held for -/
  resetCycles : Nat := 2
  /-- top-level parameter overrides (`-G<name>=<value>`) -/
  params : List (String × Nat) := []
  includeDirs : List String := []
  defines : List String := []
  extraArgs : List String := []
  objDir : String := "/tmp/sparkle_verilator"

/-- One value per port, in `Dut.inputs` / `Dut.outputs` order. -/
abbrev Pins := Array Nat

structure Dut where
  handle : JITHandle
  top : String
  /-- input ports, without the clock and the reset -/
  inputs : Array Port
  outputs : Array Port
  /-- first JIT slot of each port -/
  inSlot : Array Nat
  outSlot : Array Nat

/-- Verilator spells a character it cannot use in C++ as `__0HH` (hex). -/
private partial def demangle (s : String) : String :=
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | '_' :: '_' :: '0' :: a :: b :: rest =>
      let hex (c : Char) : Option Nat :=
        if c.isDigit then some (c.toNat - '0'.toNat)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else none
      match hex a, hex b with
      | some x, some y => go rest (Char.ofNat (x * 16 + y) :: acc)
      | _, _ => go ('_' :: '0' :: a :: b :: rest) ('_' :: acc)
    | c :: rest => go rest (c :: acc)
    | [] => acc.reverse
  String.ofList (go s.toList [])

/-- Ports declared in a Verilator model header: `(C++ name, port)`.
    Lines look like `VL_IN8(&clk,0,0);`, `VL_OUT(&q,31,0);`,
    `VL_INW(&bus,95,0,3);` (older releases omit the `&`). -/
def parseHeaderPorts (header : String) : List (String × Port) :=
  (header.splitOn "\n").filterMap fun line =>
    let t := line.trimAscii.toString
    let dir? : Option Bool :=
      if t.startsWith "VL_INOUT" then none
      else if t.startsWith "VL_IN" then some true
      else if t.startsWith "VL_OUT" then some false
      else none
    match dir?, t.splitOn "(" with
    | some isInput, [_, rest] =>
      match (rest.splitOn ")").headD "" |>.splitOn "," with
      | name :: msb :: lsb :: _ =>
        let cName := (name.trimAscii.toString.replace "&" "")
        match msb.trimAscii.toString.toNat?, lsb.trimAscii.toString.toNat? with
        | some m, some l =>
          some (cName, { name := demangle cName, width := m - l + 1, isInput })
        | _, _ => none
      | _ => none
    | _, _ => none

private def slotsOf (width : Nat) : Nat := if width ≤ 64 then 1 else (width + 31) / 32

private def run (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, stdin := .null }

/-- Is `verilator` on the PATH? -/
def available : IO Bool := do
  try
    return (← run "verilator" #["--version"]).exitCode == 0
  catch _ => return false

/-- Build and load `cfg.top`.  Errors name what is missing: an unknown
    clock or reset port is reported with the ports the design does have. -/
def Dut.load (cfg : Config) : IO Dut := do
  let sources ← cfg.sources.mapM fun (s : String) => do
    if !(← System.FilePath.pathExists s) then
      throw (IO.userError s!"Sv.Dut.load: source file '{s}' does not exist")
    return (← IO.FS.realPath s).toString
  let includes ← cfg.includeDirs.mapM fun (d : String) => do
    return (← IO.FS.realPath d).toString
  let tag := String.join (cfg.params.map fun (n, v) => s!"_{n}{v}")
  let objDir := s!"{cfg.objDir}/sv_{cfg.top}{tag}"
  IO.FS.createDirAll objDir
  -- Verilator 5 refuses a design with delays unless told what to do with
  -- them; RTL simulation ignores them.
  let version := (← run "verilator" #["--version"]).stdout
  let major := ((version.splitOn " ").getD 1 "0").splitOn "." |>.headD "0" |>.toNat? |>.getD 0
  let common : List String :=
    ["-Wno-fatal"] ++ (if major ≥ 5 then ["--no-timing"] else [])
    ++ cfg.params.map (fun (n, v) => s!"-G{n}={v}")
    ++ includes.map (fun d => s!"-I{d}")
    ++ cfg.defines.map (fun d => s!"+define+{d}")
    ++ cfg.extraArgs
  -- Pass 1: elaborate only, to learn the ports.
  let r ← run "verilator" (#["--cc", "--top-module", cfg.top, "--Mdir", objDir]
    ++ common.toArray ++ sources.toArray)
  if r.exitCode != 0 then
    throw (IO.userError s!"Sv.Dut.load: verilator rejected '{cfg.top}':\n{r.stderr}")
  let header ← IO.FS.readFile s!"{objDir}/V{cfg.top}.h"
  let all := parseHeaderPorts header
  let names := all.map (·.2.name)
  let isIn (n : String) : Bool := all.any fun (_, p) => p.name == n && p.isInput
  if !isIn cfg.clock then
    throw (IO.userError s!"Sv.Dut.load: '{cfg.top}' has no input port '{cfg.clock}' to use as the clock (set `clock`); its ports are {names}")
  if let some rst := cfg.reset then
    if !isIn rst then
      throw (IO.userError s!"Sv.Dut.load: '{cfg.top}' has no input port '{rst}' to use as the reset (set `reset`, or `none`); its ports are {names}")
  let cOf (n : String) : String := ((all.find? (·.2.name == n)).map (·.1)).getD n
  let pins := all.filter fun (_, p) => p.name != cfg.clock && some p.name != cfg.reset
  let ins := pins.filter (·.2.isInput)
  let outs := pins.filter (!·.2.isInput)
  let spec (xs : List (String × Port)) : List PortSpec :=
    xs.map fun (c, p) => { name := c, width := p.width }
  let tb := emitTb cfg.top (spec ins) (spec outs) (cOf cfg.clock)
    (cfg.reset.map fun r => (cOf r, cfg.resetActiveHigh)) cfg.resetCycles
  -- Pass 2: build with the wrapper.
  let handle ← buildAndLoad cfg.top sources tb objDir common
  let firstSlots (xs : List (String × Port)) : Array Nat := Id.run do
    let mut acc : Array Nat := #[]
    let mut next := 0
    for (_, p) in xs do
      acc := acc.push next
      next := next + slotsOf p.width
    return acc
  return { handle, top := cfg.top
           inputs := (ins.map (·.2)).toArray, outputs := (outs.map (·.2)).toArray
           inSlot := firstSlots ins, outSlot := firstSlots outs }

namespace Dut

/-- All inputs low. -/
def idle (d : Dut) : Pins := Array.replicate d.inputs.size 0

def inputIndex? (d : Dut) (name : String) : Option Nat := d.inputs.findIdx? (·.name == name)
def outputIndex? (d : Dut) (name : String) : Option Nat := d.outputs.findIdx? (·.name == name)

def portNames (d : Dut) : List String :=
  (d.inputs.map (·.name)).toList ++ (d.outputs.map (·.name)).toList

end Dut

instance : Sparkle.Core.Sim.Sim Dut Pins Pins where
  reset d := JIT.reset d.handle
  step d pins := do
    for h : k in [0:d.inputs.size] do
      let p := d.inputs[k]
      let v := (pins.getD k 0) % 2 ^ p.width
      let slot := d.inSlot.getD k 0
      if p.width ≤ 64 then
        JIT.setInput d.handle slot.toUInt32 v.toUInt64
      else
        for j in [0:slotsOf p.width] do
          JIT.setInput d.handle (slot + j).toUInt32 ((v >>> (32 * j)) % 4294967296).toUInt64
    JIT.evalTick d.handle
  read d := do
    let mut out : Pins := Array.mkEmpty d.outputs.size
    for h : k in [0:d.outputs.size] do
      let p := d.outputs[k]
      let slot := d.outSlot.getD k 0
      if p.width ≤ 64 then
        out := out.push (← JIT.getOutput d.handle slot.toUInt32).toNat
      else
        let mut v := 0
        for j in [0:slotsOf p.width] do
          v := v ||| (((← JIT.getOutput d.handle (slot + j).toUInt32).toNat % 4294967296) <<< (32 * j))
        out := out.push v
    return out
  destroy d := JIT.destroy d.handle

end Sparkle.Core.Sim.Sv
