import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineComposeRA
-- BUILT (unit SR2c, par/u-sr2c): s2/s4 exit 0 (via Tests.Compiler.ComposedCallerMixATest); co-import check co1 exit 0. No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR2c: `f.machine_composedRN` — `machine_linked_callsRA` with `hcalls` and `hfn` DISCHARGED

For a parent whose every call is a one-output GATE child (`c.gate_linked` exists): the theorem
`f.machine_composedRN` is `Tools.ShippingMachineComposeRA.machine_linked_callsRA` where

* `hcalls` is the term the old generator built for `f.machine_composedR` (`hcalls` does not mention the
  boundary: it relates `P k`/`F k` to the source's `machineCall_k`; reused verbatim from the old theorem's value);
* `hfn` is PROVED from the child's own theorem: `realChildA_inv` (inside the head) gives the child's run
  `RunsTo (synthesizeCombinational c) …`, and `c.gate_linked` (= `c.gate_child`, `gate_child_full`) turns that run
  and `EntryDefines` of `c` into `ChildFn mc (P k) (F k)`.

Premises of the generated theorem (nothing else): `O`, the trace `h : MachineTraceLBX (ServedRealA O …)` (PREMISE:
not derived here from the endpoint data), and one `EntryDefines` per distinct callee. NOT claimed: runtime fit;
`RealChildA` is a history. Machine-route children (`child_linked`) are not handled (error). -/
namespace Tools.ShippingMachineComposeRACommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine listE)
open Tools.ShippingMachineLinkedCommand

def generateComposedRN (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_composedRN
  if (← getEnv).contains name then return name
  let old ← Tools.ShippingMachineComposeRCommand.generateComposedR declName
  let some (.thmInfo ti) := (← getEnv).find? old | throwError "{old}: not a theorem"
  let r ← readMachine declName
  let kids := (r.shape.insts.map (·.1)).eraseDups
  for c in kids do
    unless (← getEnv).contains (c ++ `gate_linked) do
      throwError "{declName}: callee {c} has no gate_linked (only gate children are handled)"
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
      pure (mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
        #[ys[0]!, mref, ys[2]!, cref, toExpr c, mkConst (c ++ `gateValue)]))
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
    let lem := mkIdent (`_root_ ++ c ++ `gate_linked)
    let tac ← `(tactic| (exact ⟨rfl, fun mctx' cctx' mc Dc w w' _ _ _ _ hrun =>
      $lem mc ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.EntryDefines.ctx $hRS⟩⟩))
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

end Tools.ShippingMachineComposeRACommand
