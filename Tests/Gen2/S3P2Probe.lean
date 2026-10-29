import Sparkle
set_option autoImplicit false
-- WRITTEN, NOT BUILT. A PROBE (logs only; it asserts nothing about the result and is an error in no case).

/-! # S3 control P2 (scripts/gen2/S3_GROUP_FREEZE.md rev1 §6): a real group parent with a combinational child?

Two fixtures, each a `circuit do` parent WITH a register (slots ≠ []) calling a slotless `@[hardware_module]` child
with a `Bool` result (a `Bool` call pushes `instFields` and sets `instStruct`, Elab.lean:4058, :4080; so the shape has
`instFields ≠ []` and the machine arm closes with `closeInstsGM`, Elab.lean:5261-5263):

* `s3cntZ` calls `s3isZeroH` (a one-expression comparison: a gate-route child);
* `s3cntP` calls `s3parityH` (shared `let`s, as `pickByteH`: a machine-route child).

For each parent, logged as `S3P2 …` lines (each step in its own `try`):
1. GATES on the entry constant (`entryConst`, as `CallWidthHuntTest.gatesOf`): certified / mixed gate, `machineShape?`
   with its slots, call entries and `instFields`.
2. THE REAL COMPILE `synthesizeCombinational f` (environment and messages put back): the instance statements of the
   returned module, each with its connection keys and its module's input names in the design — whether `"clk"`/`"rst"`
   are among them.
3. THE MACHINE ARM alone (`synthesizeMachineCertified` from reset refs at depth 1, as `CallWidthHuntTest.machineArm`):
   `some` = the arm closes (with `instFields ≠ []` that is `closeInstsGM`), `none` = fall-through to legacy; and whether
   its module equals the real compile's (route 3 TAKEN by the real entry).
4. `RESULT`: `POSITIVE` iff the arm returned the real module, `insts ≠ []`, `instFields ≠ []`, `slots ≠ []`, and some
   instance's module has neither `"clk"` nor `"rst"` among its inputs; otherwise `NO POSITIVE` with the reason. A
   `NO POSITIVE` line is a coverage finding (no real group parent with a combinational child), not an S3 failure. -/
namespace Tests.Gen2.S3P2Probe
open Lean Meta Elab Command
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A Bool child: one comparison (gate route). -/
@[hardware_module]
def s3isZeroH (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  x === 0#8

/-- A Bool child with shared `let`s (machine route, as `pickByteH`). -/
@[hardware_module]
def s3parityH (w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  let hi := w.map (BitVec.extractLsb' 4 4 ·)
  let lo := w.map (BitVec.extractLsb' 0 4 ·)
  let x := hi ^^^ lo
  x === 0#4

/-- A counter whose result is the Bool child on the counter. -/
def s3cntZ (inc : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  circuit do
    let c ← Signal.reg 0#8
    let cS := (c : Signal defaultDomain (BitVec 8))
    let z := s3isZeroH cS
    c <~ cS + inc
    return z

/-- The same with the shared-`let` child. -/
def s3cntP (inc : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  circuit do
    let c ← Signal.reg 0#8
    let cS := (c : Signal defaultDomain (BitVec 8))
    let z := s3parityH cS
    c <~ cS + inc
    return z

private def short (s : String) : String :=
  let t := s.replace "\n" " "
  if t.length ≤ 300 then t else String.ofList (t.toList.take 300) ++ " …"

/-- The refs the entry clears at depth 0 (copied from `Tests.Compiler.CallWidthHuntTest.resetRefs`). -/
def resetRefs : MetaM Unit := do
  sparkleTypeCache.set {}
  sparkleSubModuleCache.set {}
  sparkleChildCache.set {}
  sparkleSubInstanceOutputs.set {}
  sparkleSingleOutInstanceCache.set {}
  sparkleFvarValueMap.set {}
  sparkleWireWidthCache.set {}
  sparkleLetWireCache.set {}
  sparkleLoopWireCache.set {}
  sparkleWireCanon.set {}

/-- The machine arm alone, from reset refs, at depth 1 (copied from `CallWidthHuntTest.machineArm`). -/
def machineArm (n : Name) (shape : MachineShape) :
    MetaM (Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) := do
  let tenv ← Lean.getEnv
  resetRefs
  sparkleSynthDepth.set 1
  try
    synthesizeMachineCertified (fun e hint top named => translateExprToWire tenv e hint top named)
      (fun _ => pure ()) n shape
  finally
    sparkleSynthDepth.set 0

/-- The instance statements of a module: (module name, instance name, connection keys). -/
def instsOf (m : Sparkle.IR.AST.Module) : List (String × String × List String) :=
  m.body.filterMap fun st => match st with
    | .inst mn iname conns => some (mn, iname, conns.map (·.1))
    | _ => none

elab "#s3_p2_probe " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let env ← getEnv
  let savedMsgs := (← get).messages
  -- 1. gates
  let gates : String × Option MachineShape ← try
      liftTermElabM do
        let ci ← getConstInfo f
        let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
        let g := (certifiedShape? false [] ec).isSome
        let mx := (mixedCertifiedShape? false [] ec (instancePredicate env)).isSome
        let sh := machineShape? false [] ec (structEnv env)
        let s := match sh with
          | none => "no machine shape"
          | some shape => s!"machine shape: slots {shape.layout.slots.length}, call entries {shape.insts.map (·.1)}, instFields {shape.instFields}"
        pure (s!"certified gate {g}, mixed gate {mx}; {s}", sh)
    catch ex => do
      let msg ← ex.toMessageData.toString
      pure (s!"ERROR {short msg}", none)
  logInfo m!"S3P2 {f} GATES: {gates.1}"
  -- 2. the real compile
  let real : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ← try
      let r ← liftTermElabM (synthesizeCombinational f)
      pure (some r)
    catch ex => do
      let msg ← ex.toMessageData.toString
      logInfo m!"S3P2 {f} COMPILE: ERROR {short msg}"
      pure none
  setEnv env
  modify fun st => { st with messages := savedMsgs }
  let mut combKid := false
  match real with
  | none => pure ()
  | some (m, D) =>
    logInfo m!"S3P2 {f} COMPILE: module {m.name}, {m.body.length} statements, design modules {D.modules.map (·.name)}"
    for (mn, iname, keys) in instsOf m do
      match D.modules.find? (·.name == mn) with
      | none => logInfo m!"S3P2 {f} INSTANCE {iname} of {mn}: module NOT in the design; connection keys {keys}"
      | some mc =>
        let ins := mc.inputs.map (·.name)
        let clkrst := ins.contains "clk" || ins.contains "rst"
        if !clkrst then combKid := true
        logInfo m!"S3P2 {f} INSTANCE {iname} of {mn}: child inputs {ins} (clk/rst among them: {clkrst}); connection keys {keys} (clk/rst connected: {keys.contains "clk" || keys.contains "rst"}); child body {mc.body.length} statements"
  -- 3. the machine arm alone
  let arm : String × Bool ← match gates.2 with
    | none => pure ("not run (no machine shape)", false)
    | some shape =>
      try
        let r ← liftTermElabM (machineArm f shape)
        match r with
        | none => pure ("NONE: the arm falls through to the legacy route", false)
        | some (am, _) =>
          let same := match real with
            | some (m, _) => am == m
            | none => false
          pure (s!"SOME: the arm closes ({if shape.instFields.isEmpty then "closeInstsM" else "closeInstsGM"}); equal to the real compile's module: {same}", same)
      catch ex => do
        let msg ← ex.toMessageData.toString
        pure (s!"ERROR {short msg}", false)
  setEnv env
  modify fun st => { st with messages := savedMsgs }
  logInfo m!"S3P2 {f} MACHINE ARM: {arm.1}"
  -- 4. result
  let shapeOk := match gates.2 with
    | some shape => !shape.insts.isEmpty && !shape.instFields.isEmpty && !shape.layout.slots.isEmpty
    | none => false
  if arm.2 && shapeOk && combKid then
    logInfo m!"S3P2 RESULT {f}: POSITIVE — route 3 taken with closeInstsGM (insts ≠ [], instFields ≠ [], slots ≠ []), an instance's child has no clk/rst input"
  else
    logInfo m!"S3P2 RESULT {f}: NO POSITIVE — arm returned the real module {arm.2}, shape insts/instFields/slots nonempty {shapeOk}, a child without clk/rst {combKid}. A coverage finding, not an S3 failure."

end Tests.Gen2.S3P2Probe

#s3_p2_probe Tests.Gen2.S3P2Probe.s3cntZ
#s3_p2_probe Tests.Gen2.S3P2Probe.s3cntP
