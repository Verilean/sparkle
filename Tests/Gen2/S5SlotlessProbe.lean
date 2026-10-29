import Sparkle
import Tools.ShippingMachineCommand
set_option autoImplicit false
-- WRITTEN, NOT BUILT (2026-10-29). A PROBE (logs only; it asserts nothing about the result and is an error in no
-- case). To be run by `kjob lake build Tests.Gen2.S5SlotlessProbe`.

/-! # S5 control P2 (scripts/gen2/S5_SLOTLESS_FREEZE.md rev0 §7 P2, D4): real slotless parents?

Fixtures (plain `def`s, no `Signal.reg` in the parent):
* (a) `s5oneP` calls a slotless one-output machine-route child `s5pickH` (as `pickByteH`, shared `let`s);
  (a') `s5onePC`: the same call inside a `circuit do` without a register;
* (b) `s5grpP` calls a `Bool`-result child `s5parityH` (as `s3parityH`; a `Bool` call gives `instFields ≠ []`);
* (c) `s5engineOnce`: a copy of `engineOnce` (Tests/Compiler/MultiInstanceTest.lean:58): one call of a REGISTERED
  record-output child (`s5pe`, a copy of `pe`), several projections; expected case S (clk/rst inputs without slots).

For each, logged as `S5P2 …` lines (each step in its own `try`). The diagnostics are COLLECTED into a list; the
environment and the messages are put back after the compile, the arm and the endpoint (so their own logs do not
leak), and the collected diagnostics are logged at the end, so they all appear in the build log:
1. GATES on the entry constant (`entryConst true false [] …`, as `synthesizeCombinationalCoreWith` builds it):
   certified / mixed gate, `machineShape?`: slots, call entries, `instFields`.
2. THE REAL COMPILE `synthesizeCombinational f`: the parent's input names and whether `"clk"`/`"rst"` are among
   them (case S / case C), each instance with its connection keys and its module's inputs (child clk/rst).
3. THE MACHINE ARM alone (`synthesizeMachineCertified`, reset refs, depth 1): `some`/`none`; whether its MODULE
   and its DESIGN equal the real compile's. Equality is NOT an observation of the route: the real entry
   post-processes the top module (`synthesizeCombinationalWith`: register dedup, `mergeChecked`) and runs the arm
   at depth 0, so a difference does not refute the route either.
4. ROUTE EVIDENCE: the dispatch of `synthesizeFromConst` (Sparkle/Compiler/Elab.lean) re-evaluated in the same
   order on the same entry constant: certified gate, then mixed gate, then `machineShape?` + the arm's `some`,
   else the legacy route. The first guard that fires is logged with the guard values. The arm's `some` is the
   probe's evaluation (depth 1, reset refs), not an observation inside the real run.
5. PACKAGE DATA: `#machine_endpoint f` is elaborated (errors captured and logged, messages put back) and the
   constants `f.machineData`, `f.machineSource`, `f.machine_next`, `f.machine_result` are looked up. A `Pkg` needs
   them (`Pkg.comb`, CombPkg:8-12, is call-free step 1); their absence is a coverage finding (D4), not an S5 failure.
   Their PRESENCE is not a `Pkg` / `ChildShips` application.
6. `RESULT`: module vs machine arm, route evidence, slots, `instFields`, case S/C, package data present. -/
namespace Tests.Gen2.S5SlotlessProbe
open Lean Meta Elab Command
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A one-output machine-route child (as `pickByteH`). -/
@[hardware_module]
def s5pickH (w : Signal defaultDomain (BitVec 16)) (sel : Signal defaultDomain (BitVec 2)) :
    Signal defaultDomain (BitVec 8) :=
  let hi := w.map (BitVec.extractLsb' 8 8 ·)
  let lo := w.map (BitVec.extractLsb' 0 8 ·)
  let x := hi ^^^ lo
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) hi
    (Signal.mux (sel === (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) lo
      (Signal.mux (sel === (Signal.pure 2#2 : Signal defaultDomain (BitVec 2))) x (x + x)))

/-- (a) a slotless one-output parent: a plain `def`. -/
def s5oneP (w : Signal defaultDomain (BitVec 16)) (sel : Signal defaultDomain (BitVec 2)) :
    Signal defaultDomain (BitVec 8) :=
  let y := s5pickH w sel
  y + y

/- (a') removed after g2s5p-h-f7e42988: the same call in a `circuit do` without a register is REFUSED by the
front end ("circuit do: at least one `let r ← Signal.reg …` is required"). Coverage finding: a register-less
`circuit do` one-output parent is not a compilable source form. -/

/-- A `Bool` child with shared `let`s (as `s3parityH`). -/
@[hardware_module]
def s5parityH (w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  let hi := w.map (BitVec.extractLsb' 4 4 ·)
  let lo := w.map (BitVec.extractLsb' 0 4 ·)
  let x := hi ^^^ lo
  x === 0#4

/-- (b) a slotless group parent (a `Bool` call). -/
def s5grpP (w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let z := s5parityH w
  Signal.mux z w (w + w)

/-- The record output of `s5pe` (copy of `PeOut`, MultiInstanceTest:26-28). -/
structure S5PeOut (dom : DomainConfig) where
  aOut : Signal dom (BitVec 32)
  pOut : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (S5PeOut dom) dom := ⟨⟩

/-- A registered child (copy of `pe`, MultiInstanceTest:32-41). -/
@[hardware_module] def s5pe {dom : DomainConfig}
    (aIn pIn w : Signal dom (BitVec 32)) : S5PeOut dom :=
  circuit do
    let aReg ← Signal.reg (0#32)
    let pReg ← Signal.reg (0#32)
    let aS := (aReg : Signal dom (BitVec 32))
    let pS := (pReg : Signal dom (BitVec 32))
    aReg <~ aIn
    pReg <~ pIn + aIn * w
    return ({ aOut := aS, pOut := pS } : S5PeOut dom)

/-- (c) copy of `engineOnce` (MultiInstanceTest:58-61): one call, several projections. -/
def s5engineOnce {dom : DomainConfig}
    (x y w : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let e := s5pe x y w
  e.aOut + e.pOut

private def short (s : String) : String :=
  let t := s.replace "\n" " "
  if t.length ≤ 300 then t else String.ofList (t.toList.take 300) ++ " …"

/-- The refs the entry clears at depth 0 (copied from `Tests.Gen2.S3P2Probe.resetRefs`). -/
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

/-- The machine arm alone, from reset refs, at depth 1 (copied from `Tests.Gen2.S3P2Probe.machineArm`). -/
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

elab "#s5_p2_probe " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let env ← getEnv
  let savedMsgs := (← get).messages
  -- the diagnostics, logged at the end (after the messages are put back)
  let mut diags : Array MessageData := #[]
  -- 1. gates: (text, certified gate, mixed gate, machine shape, gates evaluated without error)
  let gates : String × Bool × Bool × Option MachineShape × Bool ← try
      liftTermElabM do
        let ci ← getConstInfo f
        let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
        let g := (certifiedShape? false [] ec).isSome
        let mx := (mixedCertifiedShape? false [] ec (instancePredicate env)).isSome
        let sh := machineShape? false [] ec (structEnv env)
        let s := match sh with
          | none => "no machine shape"
          | some shape => s!"machine shape: slots {shape.layout.slots.length}, call entries {shape.insts.map Prod.fst}, instFields {shape.instFields}"
        pure (s!"certified gate {g}, mixed gate {mx}; {s}", g, mx, sh, true)
    catch ex => do
      let msg ← ex.toMessageData.toString
      pure (s!"ERROR {short msg}", false, false, none, false)
  let (gatesTxt, gCert, gMixed, gShape, gOk) := gates
  diags := diags.push m!"S5P2 {f} GATES: {gatesTxt}"
  -- 2. the real compile
  let real : Except String (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ← try
      let r ← liftTermElabM (synthesizeCombinational f)
      pure (.ok r)
    catch ex => do
      let msg ← ex.toMessageData.toString
      pure (.error (short msg))
  setEnv env
  modify fun st => { st with messages := savedMsgs }
  let mut caseS := false
  let mut kidClk := false
  match real with
  | .error msg => diags := diags.push m!"S5P2 {f} COMPILE: ERROR {msg}"
  | .ok (m, D) =>
    let pins := m.inputs.map (·.name)
    caseS := pins.contains "clk" || pins.contains "rst"
    diags := diags.push m!"S5P2 {f} COMPILE: module {m.name}, inputs {pins} (parent clk {pins.contains "clk"}, rst {pins.contains "rst"}: case {if caseS then "S" else "C"}), {m.body.length} statements, design modules {D.modules.map (·.name)}"
    for (mn, iname, keys) in instsOf m do
      match D.modules.find? (·.name == mn) with
      | none => diags := diags.push m!"S5P2 {f} INSTANCE {iname} of {mn}: module NOT in the design; connection keys {keys}"
      | some mc =>
        let ins := mc.inputs.map (·.name)
        let clkrst := ins.contains "clk" || ins.contains "rst"
        if clkrst then kidClk := true
        diags := diags.push m!"S5P2 {f} INSTANCE {iname} of {mn}: child inputs {ins} (child clk/rst: {clkrst}); connection keys {keys} (clk/rst connected: {keys.contains "clk" || keys.contains "rst"})"
  -- 3. the machine arm alone: (text, arm ran without error, arm some, module equal, design equal)
  let arm : String × Bool × Bool × Bool × Bool ← match gShape with
    | none => pure ("not run (no machine shape)", true, false, false, false)
    | some shape =>
      try
        let r ← liftTermElabM (machineArm f shape)
        match r with
        | none => pure ("NONE: the arm falls through to the legacy route", true, false, false, false)
        | some (am, aD) =>
          let (sameM, sameD) := match real with
            | .ok (m, D) => (am == m, aD == D)
            | .error _ => (false, false)
          pure (s!"SOME: the arm closes ({if shape.instFields.isEmpty then "closeInstsM" else "closeInstsGM"}); module equal to the real compile's: {sameM}; design equal to the real compile's: {sameD} (equality is not route evidence: the real top module is post-processed)", true, true, sameM, sameD)
      catch ex => do
        let msg ← ex.toMessageData.toString
        pure (s!"ERROR {short msg}", false, false, false, false)
  let (armTxt, armOk, armSome, armSameM, armSameD) := arm
  setEnv env
  modify fun st => { st with messages := savedMsgs }
  diags := diags.push m!"S5P2 {f} MACHINE ARM: {armTxt}"
  -- 4. route evidence: the dispatch order of `synthesizeFromConst`, first guard that fires
  let (route, machineRoute) :=
    if !gOk then ("ROUTE: UNDETERMINED (gates raised)", false)
    else if gCert then ("ROUTE: certified gate (certifiedShape? some; fires first)", false)
    else if gMixed then ("ROUTE: mixed gate (certified none, mixedCertifiedShape? some)", false)
    else match gShape with
      | none => ("ROUTE: legacy (certified none, mixed none, machineShape? none)", false)
      | some _ =>
        if !armOk then ("ROUTE: UNDETERMINED (gates none, machine shape some, the probe's arm raised)", false)
        else if armSome then ("ROUTE: machine arm (certified none, mixed none, machineShape? some, the probe's arm some at depth 1 from reset refs; not observed inside the real run)", true)
        else ("ROUTE: legacy (certified none, mixed none, machineShape? some, the probe's arm none)", false)
  diags := diags.push m!"S5P2 {f} {route}"
  -- 5. package data: `#machine_endpoint f` (errors captured), then the generated constants
  let before := (← get).messages
  let epErr : String ← try
      elabCommand (← `(command| #machine_endpoint $(mkIdent f)))
      let msgs := (← get).messages
      if msgs.hasErrors && !before.hasErrors then
        let errs ← msgs.toList.filterMapM fun m => do
          if m.severity == .error then
            return some (short (← m.data.toString))
          else return none
        pure s!"ERRORS {errs.take 3}"
      else pure "no error"
    catch ex => do
      let msg ← ex.toMessageData.toString
      pure s!"EXCEPTION {short msg}"
  modify fun st => { st with messages := savedMsgs }
  let env2 ← getEnv
  let hasC (s : Name) : Bool := env2.contains (f ++ s)
  let pkgData := hasC `machineData && hasC `machineSource && hasC `machine_next && hasC `machine_result
  diags := diags.push m!"S5P2 {f} PACKAGE DATA: #machine_endpoint {epErr}; machineData {hasC `machineData}, machineSource {hasC `machineSource}, machine_next {hasC `machine_next}, machine_result {hasC `machine_result}"
  -- 6. result
  let (slots, fields, insts) := match gShape with
    | some shape => (shape.layout.slots.length, shape.instFields, shape.insts.length)
    | none => (0, [], 0)
  let modTxt :=
    if !armSome then "MODULE vs MACHINE ARM: not comparable (no arm result)"
    else if armSameM then s!"MODULE MATCHES MACHINE ARM (design equal {armSameD})"
    else s!"MODULE DIFFERS FROM MACHINE ARM (design equal {armSameD})"
  let verdict :=
    if machineRoute && slots == 0 && insts > 0 && pkgData then
      "POSITIVE slotless parent (machine route by guard evidence) with package data present"
    else "NO POSITIVE (coverage finding, D4; not an S5 failure)"
  diags := diags.push m!"S5P2 RESULT {f}: {modTxt}; {route}; slots {slots}, call entries {insts}, instFields {fields}; case {if caseS then "S (parent has clk/rst)" else "C (parent has neither)"}; a child with clk/rst {kidClk}; package data {pkgData} (package data exists is NOT a Pkg / ChildShips application). {verdict}"
  for msg in diags do
    logInfo msg

end Tests.Gen2.S5SlotlessProbe

#s5_p2_probe Tests.Gen2.S5SlotlessProbe.s5oneP
#s5_p2_probe Tests.Gen2.S5SlotlessProbe.s5grpP
#s5_p2_probe Tests.Gen2.S5SlotlessProbe.s5engineOnce
