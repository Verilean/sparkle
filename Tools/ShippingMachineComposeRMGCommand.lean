import Tools.ShippingMachineComposeRMCommand
import Tools.ShippingEntryReadsLinked
-- BUILT (unit SR2g): t1 exit 0 (in-test audit + two conclusion comparisons THROW on failure).

/-! # Unit SR2g: `f.machine_composedRMG` — `machine_composedRM` with the callees' `EntryDefines` replaced by the
run-local `EntryDefinesRunsG` (see `Tools.ShippingEntryReadsLinked`).  Same generator as SR2c/SR2d, with
`c.gate_linkedG` (from `c.gate_child` / `c.gate_linked` by renaming the entry-boundary constants). -/
namespace Tools.ShippingMachineComposeRNGCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine listE)
open Tools.ShippingMachineLinkedCommand

/-- rename constants (levels kept) -/
def renameConsts (e : Lean.Expr) (m : List (Name × Name)) : Lean.Expr :=
  e.replace fun x => match x with
    | .const n ls => (m.lookup n).map (mkConst · ls)
    | _ => none

/-- `c.gate_childG`, `c.gate_linkedG`: `c.gate_child` / `c.gate_linked` with the all-world `EntryDefines` replaced by the
run-local `EntryDefinesRunG` (same proof term shape, run through `gate_child_fullG` / `childFn_of_gateRunG`). -/
def ensureGateLinkedG (c : Name) : MetaM Unit := do
  if (← getEnv).contains (c ++ `gate_linkedG) then return
  let m : List (Name × Name) := [
    (``Tools.ShippingInlineSoundness.EntryDefines, ``Tools.ShippingEntryReadsLinked.EntryDefinesRunG),
    (``Tools.ShippingGateChild.gate_child_full, ``Tools.ShippingEntryReadsLinked.gate_child_fullG),
    (``Tools.ShippingGateChild.GateRun, ``Tools.ShippingEntryReadsLinked.GateRunG),
    (``Tools.ShippingGateChild.childFn_of_gateRun, ``Tools.ShippingEntryReadsLinked.childFn_of_gateRunG),
    (c ++ `gate_child, c ++ `gate_childG)]
  for nm in [`gate_child, `gate_linked] do
    let some (.thmInfo ti) := (← getEnv).find? (c ++ nm) | throwError "{c ++ nm}: not a theorem"
    addTheorem (c ++ Name.mkSimple (nm.toString ++ "G")) (renameConsts ti.type m) (renameConsts ti.value m)

def generateComposedRNG (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_composedRNG
  if (← getEnv).contains name then return name
  let old ← Tools.ShippingMachineComposeRCommand.generateComposedR declName
  let some (.thmInfo ti) := (← getEnv).find? old | throwError "{old}: not a theorem"
  let r ← readMachine declName
  let kids := (r.shape.insts.map (·.1)).eraseDups
  for c in kids do
    unless (← getEnv).contains (c ++ `gate_linked) do
      throwError "{declName}: callee {c} has no gate_linked (only gate children are handled)"
    ensureGateLinkedG c
  lambdaTelescope ti.value fun ys body => do
  unless ys.size == 12 do throwError "{old}: {ys.size} binders"
  unless body.isAppOf ``Tools.ShippingMachineComposeR.machine_linked_callsR do
    throwError "{old}: value is not machine_linked_callsR"
  let args := body.getAppArgs
  unless args.size == 27 do throwError "{old}: {args.size} head arguments"
  let mref := ys[1]!
  let cref := ys[3]!
  let nat := mkConst ``Nat
  -- the new boundary
  let oT ← mkAppM ``Tools.ShippingChildInvA.RefLawsAOps
    #[mkConst ``Tools.ShippingChildFresh.MkRefd, mref, cref]
  withLocalDeclD `O oT fun O => do
  let f0 ← mkAppOptM ``Tools.ShippingMachineComposeRA.machine_linked_callsRA
    (((args.extract 0 9).map some) ++ #[some mref, some cref, some O])
  let hT := (← inferType f0).bindingDomain!
  withLocalDeclD `h hT fun h => do
  let mut p := mkApp f0 h
  -- hsimple … hcalls, verbatim (they do not depend on the boundary)
  for a in args.extract 14 26 do p := mkApp p a
  for y in ys[8:] do
    if (args.extract 14 26).any (·.containsFVar y.fvarId!) then
      throwError "{old}: hcalls mentions the old boundary binder {y}"
  -- the callees' reflection facts
  let rDecls := kids.toArray.mapIdx fun j c =>
    (Name.mkSimple s!"hR{j}", fun (_ : Array Lean.Expr) =>
      pure (mkAppN (mkConst ``Tools.ShippingEntryReadsLinked.EntryDefinesRunsG)
        #[mref, cref, toExpr c, mkConst (c ++ `gateValue)]))
  withLocalDeclsD rDecls fun hRs => do
  let hfnT := (← whnf (← inferType p)).bindingDomain!
  let names := r.shape.insts.map (·.1)
  let mut perR : Array Lean.Expr := #[]
  for k in [0:names.length] do
    let c := names[k]!
    let goalK := ((hfnT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
      (toExpr c)).bindingBody!
    let j := kids.idxOf c
    let hRS : Term := ⟨mkIdent (Name.mkSimple s!"hR{j}")⟩
    let lem := mkIdent (`_root_ ++ c ++ `gate_linkedG)
    let tac ← `(tactic| (exact ⟨rfl, fun mctx' cctx' mc Dc w w' _ _ _ _ hrun =>
      $lem mc ⟨_, _, _, _, w, w', Dc, hrun, $hRS mctx' cctx'⟩⟩))
    perR := perR.push (← proveByTactic goalK tac)
  let nameT := mkConst ``Name
  let QmR (m : Nat) : MetaM Lean.Expr :=
    withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
      let rk := ((hfnT.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
        cv).bindingBody!
      mkLambdaFVars #[kv, cv] rk
  let n := names.length
  let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← QmR n]
  for m' in [0:n] do
    let m := n - 1 - m'
    let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
    chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
      #[nameT, ← QmR m, toExpr names[m]!, rest', perR[m]!, chain]
  let pF := mkApp p chain
  let value ← mkLambdaFVars (#[ys[0]!, ys[1]!, ys[2]!, ys[3]!, ys[6]!, ys[7]!, O, h] ++ hRs) pF
  addTheorem name (← inferType value) value
  return name


end Tools.ShippingMachineComposeRNGCommand

namespace Tools.ShippingMachineComposeRMGCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine)
open Tools.ShippingMachineLinkedCommand

def generateComposedRMG (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_composedRMG
  if (← getEnv).contains name then return name
  let rn ← Tools.ShippingMachineComposeRNGCommand.generateComposedRNG declName
  let soundHead := match (← getConstInfo (declName ++ `machine_sound)) with
    | .thmInfo t => t.value.getAppFn.constName?.getD .anonymous
    | _ => .anonymous
  unless soundHead == ``Tools.ShippingMachineAuto.machine_trace_of_data_ext do
    throwError "{declName}: only the flat data_ext head is handled, not {soundHead}"
  let args ← soundArgs declName soundHead
  let pM := mkAppN (mkConst ``Tools.ShippingMachineComposeRM.machine_traceL_of_data_extRM) args
  forallTelescope (← inferType pM) fun xs _ => do
    let h := mkAppN pM xs
    let find (n : Name) : MetaM Lean.Expr := do
      for x in xs do
        if (← whnfR (← inferType x)).isAppOf n then return x
      throwError "{declName}: no binder of type {n}"
    let findRef (st : Name) : MetaM Lean.Expr := do
      for x in xs do
        let t ← whnfR (← inferType x)
        if t.isAppOf ``ST.Ref && (t.getAppArgs.back?.map (·.isConstOf st)).getD false then return x
      throwError "{declName}: no reference to {st}"
    let O ← find ``Tools.ShippingChildInvA.RefLawsAOps
    let (ms, _, _) ← forallMetaBoundedTelescope (← inferType (mkConst rn)) 8
    unless ms.size == 8 do throwError "{rn}: binders"
    ms[0]!.mvarId!.assign (← find ``Lean.Meta.Context)
    ms[1]!.mvarId!.assign (← findRef ``Lean.Meta.State)
    ms[2]!.mvarId!.assign (← find ``Lean.Core.Context)
    ms[3]!.mvarId!.assign (← findRef ``Lean.Core.State)
    ms[6]!.mvarId!.assign O
    unless ← isDefEq (← inferType ms[7]!) (← inferType h) do
      throwError "{declName}: the trace's type does not match {rn}"
    ms[7]!.mvarId!.assign h
    let p ← instantiateMVars (mkAppN (mkConst rn) ms)
    if p.hasMVar then throwError "{declName}: unassigned arguments"
    forallTelescope (← inferType p) fun hRs concl => do
      let value ← mkLambdaFVars (xs ++ hRs) (mkAppN p hRs)
      let _ := concl
      addTheorem name (← inferType value) value
      return name

end Tools.ShippingMachineComposeRMGCommand
