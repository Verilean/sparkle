import Tools.ShippingMachineDepthCommand
import Tools.ShippingMachineShipsHierHCommand
import Tools.ShippingHierSVRunH
import Tools.ShippingHierPremises
import Tools.ShippingHierShipsSV

/-! # Evaluating the shipping theorems' premises on a real compile

A generated shipping theorem is conditional: it holds of every run of the
compiler, given facts about the run's modules. That the theorem was
generated says nothing about whether those facts hold. This file evaluates
them on the modules of an actual compile, premise by premise, with the
checkers the theorems name (`shipsHierCheck`, `shipsHierHCheck`,
`kidsMaskedN`, `kidsComb`, `extendsAwayB`, `noInstOfB`, …) and traces the
run boundaries (the module an instance resolves to is a full-entry / core run
of its child) by compiling the child again and comparing the modules.
Each premise gets a status:

* `holds` / `fails` — a decidable checker, evaluated (its soundness lemma
  turns `holds` into the fact the proof uses);
* `boundary` — a run boundary traced: a run of the child's entry produces
  exactly the instance's module (the compiler's sub-synthesis is an
  `IO.Ref`, opaque in the logic, so this stays a premise of the theorem);
* `reflection` — the reflection boundary (`MachineDefines` / `EntryDefines`:
  the declaration's value is the reified source; checked per declaration by
  the endpoint generator's kernel checks, trusted as the validated parser);
* `open` — a premise about the run's inputs or initial state, or a stage not
  connected (named, not evaluated).

The shipped-IR stage and the emitted-Verilog stage are reported apart. -/
namespace Tools.ShippingPremiseEval
open Lean Meta
open Sparkle.IR.AST

open Sparkle.IR.Machine (moduleByName)

inductive Status | holds | fails | boundary | reflection | open_
  deriving BEq, Repr, Inhabited

structure Item where
  label : String
  status : Status
  sv : Bool := false
  deriving Inhabited

def chk (label : String) (b : Bool) (sv : Bool := false) : Item :=
  { label, status := if b then .holds else .fails, sv }

def Status.str : Status → String
  | .holds => "holds" | .fails => "FAILS" | .boundary => "boundary(traced)"
  | .reflection => "reflection" | .open_ => "open"

/-- The instance modules of a body, resolved in a design. -/
def instMods (ms : List Sparkle.IR.AST.Module) (body : List Stmt) : List (String × Option Sparkle.IR.AST.Module) :=
  body.filterMap fun st => match st with
    | .inst mn _ _ => some (mn, moduleByName ms mn)
    | _ => none

def fullEntry (c : Name) : MetaM Sparkle.IR.AST.Module :=
  return (← Sparkle.Compiler.Elab.synthesizeCombinational c).1

/-- The calls' premise of a composed theorem with combinational children
(`R k mc`: the call's module is its child's full-entry run), through the
sufficient condition `BoundH_of_each`: every instance module is the
full-entry run of the (single) called child. With calls of several children
the precise premise (`BoundH`, by the call–instance correspondence) is not
evaluated here. -/
def evalRuns (pre : String) (children : List Name) (ms : List Sparkle.IR.AST.Module) (body : List Stmt) :
    MetaM (List Item) := do
  let kids := children.eraseDups
  if kids.length != 1 then
    return [{ label := s!"{pre}calls' premise (several children: the call–instance correspondence `BoundH` is not evaluated)",
              status := .open_ }]
  let c := kids.head!
  let mcc ← fullEntry c
  let mut out : List Item := []
  for (mn, mc?) in instMods ms body do
    match mc? with
    | none => out := out ++ [chk s!"{pre}instance {mn} resolves in the design" false]
    | some mc =>
      out := out ++ [{ label := s!"{pre}instance {mn}: the full-entry run of {c} (GateRun/MachineRun)",
                       status := if mcc == mc then .boundary else .fails }]
  out := out ++ [{ label := s!"{pre}{c}: EntryDefines / MachineDefines", status := .reflection }]
  return out

/-- The run boundary `Bnd raw D` of `c`'s composed theorem at depth `dep`
(`machineBoundN{dep}` / `BndH`), traced on its core run `(raw, D)`. -/
partial def evalBnd (pre : String) (c : Name) (dep : Nat) (raw : Sparkle.IR.AST.Module) (D : Design) :
    MetaM (List Item) := do
  let r ← Tools.ShippingMachineCommand.readMachine c
  let calls := r.shape.insts.map (·.1)
  if r.shape.instFields.isEmpty then
    -- combinational children (`BndH`): the calls' premise and the checker
    let runs ← evalRuns pre calls D.modules raw.body
    return runs ++ [chk s!"{pre}kidsComb {c}" (Tools.ShippingMachineDepthH.kidsComb D.modules raw.body)]
  let seqKids := (calls.filter fun k => (Tools.ShippingMachineMemCommand.memWidths? k).isNone).eraseDups
  let mut out : List Item := []
  if seqKids.length > 1 then
    out := out ++ [{ label := s!"{pre}several sequential children: the call–instance correspondence (InstOfCall) is matched by module equality only",
                     status := .open_ }]
  for (mn, mc?) in instMods D.modules raw.body do
    let some mc := mc? | out := out ++ [chk s!"{pre}instance {mn} resolves" false]; continue
    if (Sparkle.Compiler.MachMemory.memParams? mc).isSome then continue
    let mut matched := false
    for k in seqKids do
      if matched then continue
      let kr ← Tools.ShippingMachineCommand.readMachine k
      if kr.shape.insts.isEmpty then
        -- `MachineRun k` (depth 0 leaf / `seq_child_run`)
        if (← fullEntry k) == mc then
          matched := true
          out := out ++ [({ label := s!"{pre}instance {mn}: the full-entry run of {k} (MachineRun)", status := .boundary } : Item),
                         ({ label := s!"{pre}{k}: MachineDefines / MachineCloses", status := .reflection } : Item)]
      else
        -- `MachineRunN k` at depth `dep - 1`
        let (rawk, Dk) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore k [] false
        let dz := Sparkle.IR.ZeroWidth.dropZeroWidthModule rawk
        if dz == mc || Sparkle.IR.RefineCheck.mergeChecked dz == mc then
          matched := true
          out := out ++ [({ label := s!"{pre}instance {mn}: post-processing of a core run of {k} (MachineRunN)", status := .boundary } : Item),
                         ({ label := s!"{pre}{k}: MachineDefines / MachineCloses", status := .reflection } : Item),
                         chk s!"{pre}ExtendsAway {k}" (Tools.ShippingHierPremisesBase.extendsAwayB rawk.name Dk.modules D.modules),
                         chk s!"{pre}NoInstOf {k}" (Tools.ShippingHierPremisesBase.noInstOfB rawk.name rawk.body)]
          if dep == 0 then
            out := out ++ [chk s!"{pre}{k} has children: depth 0 too shallow" false]
          else
            out := out ++ (← evalBnd s!"{pre}{k} > " k (dep - 1) rawk Dk)
    unless matched do
      out := out ++ [chk s!"{pre}instance {mn}: a run of one of {seqKids}" false]
  return out

/-- The decidable premises of `linked_sv_run` / `linked_sv_of_run(H)` on the
shipped module `o`: the parent's emitted Verilog under the oracle seeding. -/
def evalSVParent (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (o : Sparkle.IR.AST.Module) : List Item :=
  let wof := Tools.SVParser.RoundtripProof.moduleWof o
  let we := Tools.SVParser.EmitSem.weOf wof
  [chk "sv: instance/assign/register fragment" (o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI) true,
   chk "sv: emitted-Verilog check (seqCheck)" (Tools.SVParser.EmitSem.seqCheck wof we o.body) true,
   chk "sv: checker and emitter widths agree" ((Tools.ShippingSeqSVSoundness.seqNames o.body).all
     (fun x => Sparkle.IR.RegDedup.declWidth o x == we x)) true,
   chk "sv: instance-driven wires extracted, no wider than emitted"
     ((Tools.ShippingHierOpen.bodyInstOuts C o.body).all fun w =>
       ((Sparkle.IR.HierCheck.openIns o).map (·.name)).contains w &&
       decide (Sparkle.IR.RegDedup.declWidth o w ≤ we w)) true]

/-- The sequential / memory route: `f.machine_ships_hier` (depth `none`) or
`f.machine_ships_hierN{n}`. -/
def evalShipsHierSeq (declName : Name) (dep : Option Nat) : MetaM (List Item) := do
  let (raw, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false
  let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let C := Tools.ShippingMachineLinked.childMap D.modules
  let mut out : List Item := [chk "shipsHierCheck (hierBinds, linkedWF shipped, distinct instances, no self-read, extracted wires, widths, reset)"
    (Tools.ShippingHierPremisesBase.shipsHierCheck C b)]
  match dep with
  | some n =>
    out := out ++ [chk "Bd: kidsMaskedN" (Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body)]
    out := out ++ (← evalBnd "Bnd: " declName n raw D)
    out := out ++ [{ label := "children start at reset (ResetNk), inputs and start registers within widths", status := .open_ }]
    out := out ++ evalSVParent C o
    out := out ++ [chk "sv: instance-output widths on the shipped module (shipped_sv)"
      (Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth o) o.body) true]
    out := out ++ [chk "sv: the shipped module's children bounded (kidsMaskedN on it)"
      (Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules o.body) true,
      { label := "sv: the children's own emitted Verilog at depth ≥ 1 (not connected: design_sv_run is one-level)",
        status := .open_, sv := true }]
  | none =>
    let seqB := Tools.ShippingMachineShipsHier.kidsMasked C b.body
    let memB := Tools.ShippingMachineShipsHier.kidsMem C b.body
    out := out ++ [chk "Bd: kidsMasked (sequential) or kidsMem (memory)" (seqB || memB)]
    out := out ++ (← evalBnd "Bnd: " declName 0 raw D)
    out := out ++ [{ label := "children start at reset (Reset1/ResetM), inputs and start registers within widths", status := .open_ }]
    out := out ++ evalSVParent C o
    out := out ++ [chk "sv: instance-output widths on the shipped module (shipped_sv)"
      (Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth o) o.body) true]
    out := out ++ [chk "sv: the shipped module's children bounded"
      (Tools.ShippingMachineShipsHier.kidsMasked C o.body || Tools.ShippingMachineShipsHier.kidsMem C o.body) true]
  out := out ++ [{ label := s!"{declName}: MachineDefines / MachineCloses", status := .reflection }]
  return out

/-- The combinational route: `f.machine_ships_hierH`. -/
def evalShipsHierH (declName : Name) : MetaM (List Item) := do
  let (raw, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false
  let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let C := Tools.ShippingMachineLinked.childMap D.modules
  let r ← Tools.ShippingMachineCommand.readMachine declName
  let mut out : List Item := [chk "shipsHierHCheck (common facts, local children, width-typed)"
    (Tools.ShippingHierPremises.shipsHierHCheck D.modules b)]
  out := out ++ (← evalRuns "calls: " (r.shape.insts.map (·.1)) D.modules raw.body)
  out := out ++ [{ label := "inputs within widths, start state within widths off the outputs", status := .open_ }]
  out := out ++ evalSVParent C o
  out := out ++ [chk "sv: the shipped module width-typed with local children"
      (Tools.ShippingHierTyped.hierTyped C o && Tools.ShippingHierOptRunH.kidsLocal D.modules o.body) true,
    { label := "sv: the children's own emitted Verilog (not connected for the combinational linked run)",
      status := .open_, sv := true },
    { label := s!"{declName}: MachineDefines / MachineCloses", status := .reflection }]
  return out

/-- The classification of a generated shipping theorem by its evaluated
premises: `PREM` (every module premise holds or is a traced boundary) or
`NOPREM:<failing>`; then `SV:parent` (the parent's emitted-Verilog premises
hold), `SV:no:<failing>`. Generation alone is never counted as `PREM`. -/
def classify (items : List Item) : String :=
  let bad := items.filter fun i => !i.sv && i.status == .fails
  let badSV := items.filter fun i => i.sv && i.status == .fails
  let prem := if bad.isEmpty then "PREM" else "NOPREM:" ++ ",".intercalate (bad.map (fun i => (i.label.take 40).toString))
  let sv := if !bad.isEmpty then "SV:na"
    else if badSV.isEmpty then "SV:parent" else "SV:no:" ++ ",".intercalate (badSV.map (fun i => (i.label.take 40).toString))
  s!"{prem}|{sv}"

def report (items : List Item) : String :=
  "\n".intercalate (items.map fun i => s!"  [{i.status.str}]{if i.sv then " (sv)" else ""} {i.label}")

/-- One measurement record: `<tag>|GEN:FAIL:<why>` when the theorem is not
generated; `<tag>|GEN:OK|EVAL:FAIL:<why>` when its premises could not be
evaluated; otherwise `<tag>|GEN:OK|<classify>`. A theorem counts as applying
to the run only with `PREM`, and reaching the emitted Verilog only with
`SV:parent` (the parent's text; the children's text is reported apart). -/
def measure (tag : String) (gen : MetaM Unit) (eval : MetaM (List Item)) : MetaM String := do
  let clean (m : MessageData) : MetaM String := do
    return (((← m.toString).replace "\n" " ").replace "|" "/").take 300 |>.toString
  try gen
  catch ex => return s!"{tag}|GEN:FAIL:{← clean ex.toMessageData}"
  try
    let items ← eval
    return s!"{tag}|GEN:OK|{classify items}"
  catch ex => return s!"{tag}|GEN:OK|EVAL:FAIL:{← clean ex.toMessageData}"

end Tools.ShippingPremiseEval
