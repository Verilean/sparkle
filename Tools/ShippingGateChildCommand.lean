import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChild

/-! # Generated gate children

`#gate_child c`, for a combinational declaration the certified unified gate
compiles, adds `c.gate_child`: a run of the full entry on `c` returns a
module that computes
`c`'s source function (`c.machineSource`, read the machine route's way) on its
argument ports (`ChildFn`, the premise `machine_linked` keeps about each
call's module). It is `Tools.ShippingGateChild.gate_child_full` at `c`: the
gate's peel of `c`'s value is the quote of the term read off it (kernel
`rfl`; the value is the entry constant's, the declaration as read or its
unfolding — `EntryDefines`), the term is well formed, its input positions are the binders'
(evaluation), and the source function at constant inputs is the term's value
(kernel `rfl`). -/
namespace Tools.ShippingGateChildCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab Tools.ShippingUnifiedSource
open Tools.ShippingMachineCommand (unq Binders listE natListE stypeE termE binderE binderT addDef
  progress)

/-- The gate's reading of `declName`: its value, binders, domain, term and
input positions, as definitions `declName.gate*`. -/
def gateDefs (declName : Name) : MetaM Unit := do
  if (← getEnv).contains (declName ++ `gateVw) then return
  let env ← getEnv
  let ci0 ← getConstInfo declName
  -- the constant the entry hands on: the declaration as read, or its unfolding
  let ci := entryConst true false [] ci0 (instancePredicate env) (userInliner env) (structEnv env)
  let some value := ci.value? | throwError "{declName}: no value"
  unless (certifiedShape? false [] ci).isNone do
    throwError "{declName}: the first combinational gate takes it"
  unless (mixedCertifiedShape? false [] ci (instancePredicate env)).isSome do
    throwError "{declName}: the unified gate does not take its entry constant"
  let some (bs, body) := mixedGatePeel value | throwError "{declName}: the gate's peel"
  let kinds := bs.map (·.2)
  let c := Binders.ofKinds kinds
  let some ⟨srt, t⟩ := unq c body | throwError "{declName}: the body is not read as a term"
  let idx := (List.range kinds.length).zip kinds
  let bposL := idx.filterMap fun (p, k) => if k == .bool then some p else none
  let vposL := idx.filterMap fun (p, k) => match k with | .bits _ => some p | _ => none
  let vwL := idx.filterMap fun (_, k) => match k with | .bits w => some w | _ => none
  -- the domain the body's Signals are over
  -- (a Signal type, else the first argument of a pure / mux / map)
  let domHeads := [``Sparkle.Core.Signal.Signal, ``Sparkle.Core.Signal.Signal.pure,
    ``Sparkle.Core.Signal.Signal.mux, ``Sparkle.Core.Signal.Signal.map]
  let some sigApp := body.find? fun x =>
      domHeads.any fun h => x.isAppOf h && x.getAppNumArgs ≥ 2
    | throwError "{declName}: no Signal in the body"
  let dom := sigApp.getAppArgs[0]!
  let q := quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bposL.getD j 0))
    (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vposL.getD j 0)) t
  unless q.equal body do throwError "{declName}: the term does not quote back to the body"
  let refl (e : Lean.Expr) : MetaM Lean.Expr := match Tools.ShippingEntrySoundness.reflExpr e with
    | .ok r => pure r
    | .error msg => throwError msg
  let exprT := mkConst ``Lean.Expr
  let natListT := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  addDef (declName ++ `gateValue) exprT (← refl value)
  addDef (declName ++ `gateDom) exprT (← refl dom)
  addDef (declName ++ `gateBinders) (mkApp (mkConst ``List [.zero]) binderT)
    (listE binderT (bs.map binderE))
  addDef (declName ++ `gateSort) (mkConst ``SType) (stypeE srt)
  addDef (declName ++ `gateTerm) (mkApp (mkConst ``Tools.ShippingUnifiedSource.Term) (mkConst (declName ++ `gateSort))) (termE t)
  addDef (declName ++ `gateBpos) natListT (natListE bposL)
  addDef (declName ++ `gateVpos) natListT (natListE vposL)
  addDef (declName ++ `gateVw) natListT (natListE vwL)

open Lean.Elab.Command in
/-- `declName.gate_child` (after `gateDefs` and the source definitions). -/
def gateTheorem (declName : Name) : CommandElabM Unit := do
  let n (s : String) : Ident := mkIdent (`_root_ ++ declName ++ Name.mkSimple s)
  let c : Ident := mkIdent declName
  let cq : Lean.Term := quote declName
  -- the domain family of the source function: one domain, or every domain
  let srcT ← liftTermElabM do inferType (mkConst (declName ++ `machineSource))
  let i0 : Lean.Term ← if srcT.bindingDomain!.isConstOf ``Unit then `(Unit.unit)
    else `(Sparkle.Core.Domain.defaultDomain)
  let _ := c
  unless (← getEnv).contains (declName ++ `gate_peel) do elabCommand (← `(command|
    theorem $(n "gate_peel") : mixedGatePeel $(n "gateValue") = some ($(n "gateBinders"),
        Tools.ShippingUnifiedSource.quote $(n "gateDom")
          (fun j => Tools.ShippingMixedSourceBridge.inputExpr $(n "gateBinders").length
            ($(n "gateBpos").getD j 0))
          (fun j => Tools.ShippingMixedSourceBridge.inputExpr $(n "gateBinders").length
            ($(n "gateVpos").getD j 0))
          $(n "gateTerm")) := by rfl))
  unless (← getEnv).contains (declName ++ `gate_old) do elabCommand (← `(command|
    theorem $(n "gate_old") : ∀ d : DefinitionVal, d.value = $(n "gateValue") →
        certifiedShape? false [] (.defnInfo d) = none := by
      intro d hd; simp only [certifiedShape?, hd]; rfl))
  unless (← getEnv).contains (declName ++ `gate_wf) do elabCommand (← `(command|
    theorem $(n "gate_wf") : $(n "gateTerm").WF $(n "gateBpos").length $(n "gateVpos").length
        (fun j => $(n "gateVw").getD j 0) := by
      delta $(n "gateTerm") $(n "gateSort") $(n "gateBpos") $(n "gateVpos") $(n "gateVw")
      simp (config := { decide := true }) [Tools.ShippingUnifiedSource.Term.WF]))
  -- the ports the linked theorem reads the child by are the gate's binders
  unless (← getEnv).contains (declName ++ `gate_binders) do elabCommand (← `(command|
    theorem $(n "gate_binders") :
        Tools.ShippingMachineAuto.MachineData.bsIn $(n "machineData") = $(n "gateBinders") := by
      decide))
  unless (← getEnv).contains (declName ++ `gate_child) do elabCommand (← `(command|
    theorem $(n "gate_child") {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
        {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
        {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
        (hr : Tools.ShippingEntrySoundness.RunsTo (synthesizeCombinational $cq)
          mctx mref cctx cref w (b, design) w')
        (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq $(n "gateValue")) :
        Tools.ShippingMachineCompose.ChildFn b
          (fun vs => Tools.ShippingMachineChild.InRange vs
            ($(n "gateBinders").filter fun b => b.2 != .domain))
          (Tools.ShippingMachineChild.childValue $(n "machineSource") $(n "gateBinders") $i0) :=
      Tools.ShippingGateChild.gate_child_full hr entry $(n "gate_old") $(n "gate_peel") $(n "gate_wf")
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (fun _ _ => rfl)))
  -- at the module of a run, in the form the linked theorem reads a child
  unless (← getEnv).contains (declName ++ `gate_linked) do elabCommand (← `(command|
    theorem $(n "gate_linked") (mc : Sparkle.IR.AST.Module)
        (h : Tools.ShippingGateChild.GateRun $cq $(n "gateValue") mc) :
        Tools.ShippingMachineCompose.ChildFn mc
          (Tools.ShippingMachineChild.childRange $(n "machineData"))
          (Tools.ShippingMachineChild.childValue $(n "machineSource")
            (Tools.ShippingMachineAuto.MachineData.bsIn $(n "machineData")) $i0) := by
      unfold Tools.ShippingMachineChild.childRange
      rw [$(n "gate_binders"):ident]
      exact Tools.ShippingGateChild.childFn_of_gateRun $(n "gate_child") h))

open Lean.Elab.Command in
/-- `declName.gate_child` and its definitions (the source definitions too,
when missing); fails, leaving no theorem, when a generated proof fails. -/
def generateGateChild (declName : Name) : CommandElabM Name := do
  liftTermElabM do
    unless (← getEnv).contains (declName ++ `machineSource) do
      discard <| Tools.ShippingMachineCommand.generateSourceDefs declName
    withOptions (fun o => Lean.Elab.async.set o false) (gateDefs declName)
  let before := (← get).messages.toList.length
  withScope (fun s => { s with opts := maxRecDepth.set (Lean.Elab.async.set s.opts false) 100000 })
    (gateTheorem declName)
  -- every generated theorem must be added without error (an error leaves a
  -- `sorry` or no declaration at all)
  if (← get).messages.toList.drop before |>.any (·.severity == .error) then
    throwError "{declName}: a generated proof failed"
  let name := declName ++ `gate_child
  unless (← getEnv).contains name do throwError "{name} was not added"
  for ax in ← liftCoreM (Lean.collectAxioms name) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return name

open Lean.Elab.Command in
/-- `declName.machine_composed`: `declName.machine_linked` with its premise
about each call's module replaced by that module being a run of the child's
full entry (`GateRun`), every child the gate's (`Tools.ShippingGateChild.
runs_of_linked`, each call discharged by its child's `gate_linked`). -/
def generateComposed (declName : Name) : CommandElabM Name := do
  let children ← liftTermElabM do
    let r ← Tools.ShippingMachineCommand.readMachine declName
    pure (r.shape.insts.map (·.1))
  unless (← getEnv).contains (declName ++ `machine_linked) do
    throwError "{declName}: run #machine_linked {declName} first"
  for c in children.eraseDups do
    unless (← getEnv).contains (c ++ `gate_linked) do
      if (← getEnv).contains (c ++ `machine_sound) then
        throwError "{declName}: the child {c} is on the machine route"
      discard <| generateGateChild c
  let n := children.length
  let name := declName ++ `machine_composed
  let rTac ← do
    -- one case per call, then the calls beyond the list are absurd
    let mut tac ← `(tactic| exact absurd hk (by omega))
    for c in children.reverse do
      tac ← `(tactic| (rcases k with _ | k
                       · exact $(mkIdent (`_root_ ++ c ++ `gate_linked)) mc hrun
                       $tac:tactic))
    `(tactic| (intro k mc h; obtain ⟨hk, hrun⟩ := h; $tac:tactic))
  liftTermElabM do
    let lt ← inferType (mkConst (declName ++ `machine_linked))
    let value ← forallTelescope lt fun xs _ => do
      let H := mkAppN (mkConst (declName ++ `machine_linked)) xs
      let nameT := mkConst ``Lean.Name
      let csE := Tools.ShippingMachineCommand.listE nameT (children.map toExpr)
      let vsE := Tools.ShippingMachineCommand.listE (mkConst ``Lean.Expr)
        (children.map fun c => mkConst (c ++ `gateValue))
      let modT := mkConst ``Sparkle.IR.AST.Module
      let R ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `mc modT fun mc => do
        let lt ← mkAppM ``LT.lt #[k, mkNatLit n]
        let gr := mkApp3 (mkConst ``Tools.ShippingGateChild.GateRun)
          (← mkAppM ``List.getD #[csE, k, toExpr Name.anonymous])
          (← mkAppM ``List.getD #[vsE, k, mkConst ``Lean.Expr.bvar |>.app (mkNatLit 0)]) mc
        mkLambdaFVars #[k, mc] (mkAnd lt gr)
      let p ← mkAppOptM ``Tools.ShippingGateChild.runs_of_linked
        #[none, none, none, none, none, none, none, none, none, none, none, H, R]
      let hRT := (← whnf (← inferType p)).bindingDomain!
      let hR ← Tools.ShippingMachineLinkedCommand.proveByTactic hRT rTac
      mkLambdaFVars xs (mkApp p hR)
    Tools.ShippingMachineLinkedCommand.addTheorem name (← inferType value) value
  return name

open Lean.Elab.Command in
elab "#machine_composed " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← generateComposed declName
  logInfo m!"{name}: the linked run of the emitted module shows the source, given that each call's module is its child's full-entry run, checked by the kernel"

open Lean.Elab.Command in
elab "#gate_child " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← generateGateChild declName
  logInfo m!"{name}: the gate-compiled child's full-entry module computes its source function, checked by the kernel"

end Tools.ShippingGateChildCommand
