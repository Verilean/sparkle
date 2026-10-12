/-
  `#simChecked`: the typed JIT / Verilator simulator of a declaration, built
  from the ARTIFACT the design writer prints.

  `#sim` (Sparkle/Compiler/Elab.lean) is NOT changed and stays OUTSIDE the
  guarantee: its `.sv` is `toVerilogDesign (optimizeDesign design)` (the
  unchecked optimizer twice), its JIT C `toCJIT (optimizeDesign design)`,
  and its wrapper numbers the inputs by their position among the fields.

  Here the `.sv` is `toVerilogDesignChecked design` and the JIT C is
  `toCJIT (simArtifact design)`: both from `designArtifact design` — the
  top through `checkedOptimize`, the other modules as they are. The top is
  looked up by `topModule` (as the writer and `toCJIT` do). The wrapper
  drives each input at the slot the JIT C gives it (`jitInputSlots`), and
  keeps every input but `clk` and `rst` as a field (`#sim` also leaves out
  inputs named `reset`, `*_rst`, `*_clk`, …, which shifts its numbering
  against the JIT C's: `Tests/Compiler/SimIndexTest.lean`).

  NOTHING here is a statement about the JIT C's behaviour: no theorem
  relates `toCJIT`'s output to the IR semantics. What this command changes
  is which modules the simulator is generated from.

  The command body is `#sim`'s, copied by a script, with those changes.
-/
import Sparkle.Compiler.Elab

namespace Sparkle.Compiler.Elab
open Lean Lean.Elab Lean.Elab.Command Lean.Meta
open Sparkle.IR.AST (Operator Port Module Expr Stmt)
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

/-- The design `#simChecked` generates from: the design writer's modules. -/
def simArtifact (d : Sparkle.IR.AST.Design) : Sparkle.IR.AST.Design :=
  { d with modules := Sparkle.Backend.Verilog.designArtifact d }

/-- Names `#sim` treats as clock/reset and leaves out of `SimInput`
    (a copy of its private `isSimClkRst`). -/
def simClkRst (name : String) : Bool :=
  ["clk", "clock", "CLK", "rst", "reset", "RST", "rst_n", "resetn", "RESETN"].any (· == name)
  || name.endsWith "_clk" || name.endsWith "_rst"

/-- `#sim`'s numbering of the inputs: the position among the ports it keeps. -/
def simInputIndex (inputs : List Port) : List (String × Nat) :=
  ((inputs.filter fun p => !simClkRst p.name).zipIdx).map fun (p, i) => (p.name, i)

/-- The JIT C's numbering (`Sparkle.Backend.CSim.emitSetInputSwitch`, read):
    every port but `clk`, in order; a port wider than 64 bits takes
    `(w + 31) / 32` consecutive slots. The first slot of each port. -/
def jitInputSlots (inputs : List Port) : List (String × Nat) :=
  ((inputs.filter fun p => p.name != "clk").foldl
    (fun (acc : List (String × Nat) × Nat) p =>
      let w := p.ty.bitWidth
      (acc.1 ++ [(p.name, acc.2)], acc.2 + (if w > 64 then (w + 31) / 32 else 1)))
    ([], 0)).1

/-- Helper: elaborate a string as a Lean command -/
private def elabSimCheckedStr (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "#simChecked parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

/-- Sanitize a name to valid Lean identifier -/
private def simLeanIdent (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- `#simChecked f` — as `#sim f`, from the design writer's artifact.

    Generates `f.SimChecked.SimInput`, `SimOutput`, `Simulator`, `load`,
    `loadVerilator`, `jitCppPath`, `svPath` (files under
    `.lake/build/gen/simchecked/`). -/
elab "#simChecked" id:ident : command => do
  let declName ← Lean.Elab.Command.liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  -- Phase 1: Synthesize + generate JIT C++ AND Verilog .sv (in TermElabM)
  let (ns, jitPath, svPath, topName, userInputs, outputs, allInputs) ← Lean.Elab.Command.liftTermElabM do
    let design ← synthesizeHierarchical declName
    -- ONE artifact for the text and for the JIT C: the design writer's modules
    let art := simArtifact design
    let jitC := Sparkle.Backend.CSim.toCJIT art
    let verilog := Sparkle.Backend.Verilog.toVerilogDesignChecked design
    let ns := simLeanIdent (toString declName.components.getLast!)
    let jitPath := s!".lake/build/gen/simchecked/{ns}_jit.c"
    let svPath  := s!".lake/build/gen/simchecked/{ns}.sv"
    try
      IO.FS.createDirAll ".lake/build/gen/simchecked"
      IO.FS.writeFile jitPath jitC
      IO.FS.writeFile svPath  verilog
    catch _ => pure ()
    -- The top: the module the writer and `toCJIT` take (`topModule`), no
    -- lookup by declaration name and no fallback.
    let m ← match art.modules.find? (·.name == art.topModule) with
      | some m => pure m
      | none => throwError "#simChecked: the design has no module named {art.topModule}"
    -- every port but the two the compiler adds (`clk`, `rst`): a user input
    -- named like a clock or reset (`soft_rst`, `reset`, …) stays drivable
    let userInputs := m.inputs.filter fun p => p.name != "clk" && p.name != "rst"
    let outputs := m.outputs
    pure (ns, jitPath, svPath, m.name, userInputs, outputs, m.inputs)
  -- Phase 2: Generate typed wrappers (in CommandElabM)
  let lb := "{"
  let rb := "}"
  elabSimCheckedStr s!"namespace {ns}.SimChecked"
  elabSimCheckedStr "open Sparkle.Core.JIT"
  elabSimCheckedStr s!"def jitCppPath : String := \"{jitPath}\""
  if userInputs.isEmpty then
    elabSimCheckedStr "structure SimInput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      userInputs.map fun p => s!"  {simLeanIdent p.name} : BitVec {p.ty.bitWidth}"
    elabSimCheckedStr s!"structure SimInput where\n{fields}\n  deriving Repr, BEq, Inhabited"
  if outputs.isEmpty then
    elabSimCheckedStr "structure SimOutput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      outputs.map fun p => s!"  {simLeanIdent p.name} : BitVec {p.ty.bitWidth}"
    elabSimCheckedStr s!"structure SimOutput where\n{fields}\n  deriving Repr, BEq, Inhabited"
  elabSimCheckedStr "structure Simulator where\n  handle : JITHandle"
  -- the JIT C's own slot of each port (`jitInputSlots`), not the position
  -- among the wrapper's fields; a wide port is written slot by slot
  let slots := jitInputSlots allInputs
  let setCalls := userInputs.flatMap fun p =>
    let s := (slots.lookup p.name).getD 0
    let w := p.ty.bitWidth
    if w ≤ 64 then
      [s!"  JIT.setInput sim.handle {s} i.{simLeanIdent p.name}.toNat.toUInt64"]
    else
      (List.range ((w + 31) / 32)).map fun j =>
        s!"  JIT.setInput sim.handle {s + j} ((i.{simLeanIdent p.name}.toNat >>> {32 * j}) % 4294967296).toUInt64"
  let stepBody := String.intercalate "\n" setCalls
  elabSimCheckedStr s!"def Simulator.step (sim : Simulator) (i : SimInput) : IO Unit := do\n{stepBody}\n  JIT.evalTick sim.handle"
  -- For each output port: when the port width is > 64 bits,
  -- emit multiple `JIT.getOutput` calls reading 32-bit chunks
  -- (the C-side `jit_get_output` already exposes wide ports
  -- as N consecutive switch cases of `uint32_t` slot reads —
  -- see `emitGetOutputSwitch` in Sparkle/Backend/CSim.lean).
  -- Then OR-shift them into the BitVec.  Fixes Issue #75
  -- (silent truncation of > 64-bit JIT output ports).
  let (readLines, _) := outputs.foldl
    (fun (acc : List String × Nat) (p : Port) =>
      let w := p.ty.bitWidth
      let nameId := simLeanIdent p.name
      if w ≤ 64 then
        let line :=
          s!"  let v_{nameId} ← JIT.getOutput sim.handle {acc.2}\n" ++
          s!"  let {nameId} := BitVec.ofNat {w} v_{nameId}.toNat"
        (acc.1 ++ [line], acc.2 + 1)
      else
        -- Wide port: read ⌈w/32⌉ 32-bit slots and OR-shift.
        let nWords := (w + 31) / 32
        let slotIdxs := List.range nWords
        let reads := slotIdxs.map fun j =>
          s!"  let v_{nameId}_{j} ← JIT.getOutput sim.handle {acc.2 + j}"
        -- Assemble: each slot j contributes
        --   (BitVec.ofNat w v_<nameId>_j.toNat) <<< (32 * j)
        -- and we fold them with `|||`.
        let combineTerm (j : Nat) : String :=
          s!"(BitVec.ofNat {w} (v_{nameId}_{j}.toNat &&& 0xFFFFFFFF) <<< {32 * j})"
        let combined :=
          match slotIdxs with
          | [] => s!"(BitVec.ofNat {w} 0)"
          | j :: rest =>
            rest.foldl (fun s k => s ++ " ||| " ++ combineTerm k) (combineTerm j)
        let assemble :=
          s!"  let {nameId} : BitVec {w} := {combined}"
        (acc.1 ++ reads ++ [assemble], acc.2 + nWords))
    ([], 0)
  let readBody := String.intercalate "\n" readLines
  let readReturn := String.intercalate ", " <| outputs.map fun p => simLeanIdent p.name
  elabSimCheckedStr s!"def Simulator.read (sim : Simulator) : IO SimOutput := do\n{readBody}\n  pure {lb} {readReturn} {rb}"
  elabSimCheckedStr "def Simulator.reset (sim : Simulator) : IO Unit :=\n  JIT.reset sim.handle"
  elabSimCheckedStr "def Simulator.destroy (sim : Simulator) : IO Unit :=\n  JIT.destroy sim.handle"
  elabSimCheckedStr s!"def load : IO Simulator := do\n  let h ← JIT.compileAndLoad jitCppPath\n  pure {lb} handle := h {rb}"
  -- Opt the generated wrapper into the unified `Sparkle.Core.Sim.Sim`
  -- typeclass so call-sites can write `sim.step inp` / `sim.read`
  -- against any backend (pure-Lean / JIT / Verilator) without
  -- knowing which one produced `sim`.
  elabSimCheckedStr <|
    "instance : Sparkle.Core.Sim.Sim Simulator SimInput SimOutput where\n" ++
    "  reset   := Simulator.reset\n" ++
    "  step    := Simulator.step\n" ++
    "  read    := Simulator.read\n" ++
    "  destroy := Simulator.destroy"
  -- Verilator backend.  Reuses the same `Simulator` shape because
  -- the Verilator wrapper exposes the JIT C ABI; only `load`
  -- differs (it builds a `.so` from the `.sv` instead of from
  -- the JIT `.cpp`).
  elabSimCheckedStr s!"def svPath : String := \"{svPath}\""
  elabSimCheckedStr s!"def topModuleName : String := \"{topName}\""
  let portSpec (p : Sparkle.IR.AST.Port) : String :=
    "{ name := \"" ++ p.name ++ "\", width := " ++ toString p.ty.bitWidth ++ " : Sparkle.Core.Sim.Verilator.PortSpec }"
  let inputPortSpecs := String.intercalate ", " (userInputs.map portSpec)
  let outputPortSpecs := String.intercalate ", " (outputs.map portSpec)
  elabSimCheckedStr <|
    "def loadVerilator : IO Sparkle.Core.Sim.Verilator.Simulator :=\n" ++
    "  Sparkle.Core.Sim.Verilator.of svPath topModuleName\n" ++
    "    [" ++ inputPortSpecs ++ "]\n" ++
    "    [" ++ outputPortSpecs ++ "]"
  elabSimCheckedStr s!"end {ns}.SimChecked"


end Sparkle.Compiler.Elab
