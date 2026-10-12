import Tests.Compiler.ShippingCallsCloseTest
import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.ShippingDesignSVTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tools.ShippingMachineCommand
import Tools.ShippingHierPremises
import Tools.ShippingShipsDesignSVAll

/-! # The gate and the proposed checks on the real parents (G1 measurement)

Logs only (compiled code); no theorem, no assertion, never throws.

For every declaration of the imported test modules that has a
`f.machineData` AND calls (`shape.insts ≠ []`; whichever those are — the
list is discovered, not written here) the full entry is run again (`synthesizeCombinational f`) and, on the module
`b` and design it returns, with `o = checkedOptimize b`:

* `hierGate b`, `hierBinds b` — the gate hypothesis of the derived
  theorems (`Tools/ShippingChecksRun.lean`; this file does not import them:
  it only evaluates compiled checks);
* `kept` — whether `checkedOptimize b` is `b` itself (the fallback);
* `shipsHierCheck`, `shipsHierHCheck`, `outsCheck … 0 o` — today's premises;
* `outsA` — every module of the design assigns its outputs;
* `P1` — the instance statements of `o` and `b` are the same LIST;
* `instNamesNodup(o)`; `P2b` — `linkedWF (childMap design.modules) o.body`.

One line per declaration, prefixed `CHECKS`; a `CHECKS TOTAL` line. -/
namespace Tests.Compiler.ChecksDerivedTest
open Lean Meta
open Sparkle.IR.AST

def isInst : Stmt → Bool
  | .inst .. => true
  | _ => false

def line (f : Name) : MetaM (Option (String × Bool)) := do
  let r ← Tools.ShippingMachineCommand.readMachine f
  if r.shape.insts.isEmpty then return none
  let (b, design) ← Sparkle.Compiler.Elab.synthesizeCombinational f
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let C := Tools.ShippingMachineLinked.childMap design.modules
  let names := Tools.ShippingHierState.instNames o.body
  let hb := Sparkle.IR.RefineCheck.hierBinds b
  let s := s!"hierGate={Sparkle.IR.RefineCheck.hierGate b} hierBinds={hb} " ++
    s!"kept={o.body == b.body} " ++
    s!"shipsHierCheck={Tools.ShippingHierPremisesBase.shipsHierCheck C b} " ++
    s!"shipsHierHCheck={Tools.ShippingHierPremises.shipsHierHCheck design.modules b} " ++
    s!"outsCheck0={Tools.ShippingDesignSVBack.outsCheck C 0 o} " ++
    s!"outsA={design.modules.all Tools.ShippingDesignSVBack.outsAssigned} " ++
    s!"P1={o.body.filter isInst == b.body.filter isInst} " ++
    s!"instNamesNodup(o)={names.eraseDups.length == names.length} " ++
    s!"P2b={Tools.ShippingHierOpen.linkedWF C o.body} " ++
    s!"insts={(b.body.filter isInst).length} modules={design.modules.length}"
  return some (s, hb)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    match n with
    | .str p "machineData" => acc.push p
    | _ => acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut parents := 0
  let mut binds := 0
  let mut errs := 0
  for f in names do
    try
      match ← line f with
      | some (s, hb) =>
        parents := parents + 1
        if hb then binds := binds + 1
        IO.println s!"CHECKS {f}: {s}"
      | none => pure ()
    catch ex =>
      errs := errs + 1
      IO.println s!"CHECKS {f}: ERROR ({← ex.toMessageData.toString})"
  IO.println s!"CHECKS TOTAL: parents {parents}, hierBinds true {binds}, errors {errs}"

end Tests.Compiler.ChecksDerivedTest
