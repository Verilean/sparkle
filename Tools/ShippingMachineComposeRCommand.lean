import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineComposeR
import Tools.ShippingChildCache
import Tools.ShippingMachineNestR
import Tools.ShippingMachineTeleNestR
import Tools.ShippingMachineShipsHierHCommand
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingShipsDesignSVCommand

/-! # `#machine_design_svHR f`: combinational children, the run boundary derived

`f.machine_composedR`: `machine_linked_callsR` from the endpoint carrying
`ServedReal` (the `data_ext` R head, under `ChildSynthIs`), each call's
`ChildFn` from its child's own theorem (`c.gate_linked` / `c.child_linked`) on
the run that `ServedReal` gives for the instance serving the call, with the
child's reflection fact (`EntryDefines` / `MachineDefines`+`MachineCloses`).
Its premise: `ChildSynthIs` and those reflection facts, in the run's
contexts — no premise about the calls' modules (`GateRun` / `MachineRun` /
`BoundH`). Then `f.machine_ships_hierHR` (`machine_ships_hierH` with the
trivial `R` and that premise as `Bnd`) and `f.machine_design_svHR`. -/
namespace Tools.ShippingMachineComposeRCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand

/-- The endpoint head, its derived-boundary twin and its wired twin. -/
def headsOf (soundHead : Name) (nested : Bool) : Name × Name × Name :=
  if soundHead == ``Tools.ShippingMachineTeleNest.machine_trace_of_tele_ext then
    (``Tools.ShippingMachineTeleNest.machine_trace_of_tele_ext,
      ``Tools.ShippingMachineTeleNest.machine_traceL_of_tele_extR,
      ``Tools.ShippingMachineTeleNest.machine_traceL_of_tele_ext)
  else if nested then
    (``Tools.ShippingMachineNest.machine_trace_of_nested_ext,
      ``Tools.ShippingMachineNest.machine_traceL_of_nested_extR,
      ``Tools.ShippingMachineNest.machine_traceL_of_nested_ext)
  else (``Tools.ShippingMachineAuto.machine_trace_of_data_ext,
    ``Tools.ShippingMachineComposeR.machine_traceL_of_data_extR,
    ``Tools.ShippingMachineAuto.machine_traceL_of_data_ext)

def generateComposedRCore (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_composedR
  if (← getEnv).contains name then return name
  progress s!"{declName}: composedR (combinational, boundary derived)"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no hardware-module call"
  if r.shape.layout.slots.isEmpty || !r.shape.loops.isEmpty then
    throwError "{declName}: only a circuit do with slots (and sub-machines) is supported"
  -- the endpoint's head theorem, and its twin with the wiring and the lets
  let soundHead := match (← getConstInfo (declName ++ `machine_sound)) with
    | .thmInfo t => t.value.getAppFn.constName?.getD .anonymous
    | _ => .anonymous
  let (head, headL, _) := headsOf soundHead r.nested
  let args ← soundArgs declName head
  let pL := mkAppN (mkConst headL) args
  let data := args[1]!
  let pLT ← inferType pL
  forallTelescope pLT fun xs traceT => do
  let h := mkAppN pL xs
  let traceT ← whnfR traceT
  let tyArgs := (← instantiateMVars traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let hsyn := xs.back!
  let ctxOf (n : Name) : MetaM Lean.Expr := do
    for x in xs do
      if (← whnfR (← inferType x)).isAppOf n then return x
    throwError "{declName}: no binder of type {n}"
  let refOf (st : Name) : MetaM Lean.Expr := do
    for x in xs do
      let t ← whnfR (← inferType x)
      if t.isAppOf ``ST.Ref && (t.getAppArgs.back?.map (·.isConstOf st)).getD false then return x
    throwError "{declName}: no reference to {st}"
  let ctx := #[← ctxOf ``Lean.Meta.Context, ← refOf ``Lean.Meta.State, ← ctxOf ``Lean.Core.Context,
    ← refOf ``Lean.Core.State]
  -- every call is a one-output combinational child (`instFields = []`)
  let hsimple ← mkEqRefl (mkApp (mkConst ``List.nil [.zero]) (mkConst ``String))
  let mut p ← mkAppOptM ``Tools.ShippingMachineComposeR.machine_linked_callsR
    #[none, none, none, none, none, none, none, none, none, none, none, none, none, h, hsimple,
      mkNatLit r.nDecl]
  -- the decidable facts about the data
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  -- the children's ranges and functions
  let mut Ps : Array Lean.Expr := #[]
  let mut Fs : Array Lean.Expr := #[]
  let mut childInfo : Array (Name × Name × List MixedGateBinder) := #[]
  for (c, _, _) in r.shape.insts do
    let cData := c ++ `machineData
    let cSrc := c ++ `machineSource
    unless (← getEnv).contains cSrc do
      -- a child the certified gate compiles: its source function only
      try discard <| Tools.ShippingMachineCommand.generateSourceDefs c
      catch _ => throwError "{declName}: run #machine_endpoint {c} first"
    let srcT ← inferType (mkConst cSrc)
    let ιc := srcT.bindingDomain!
    let i0 := if ιc.isConstOf ``Unit then mkConst ``Unit.unit
      else mkConst ``Sparkle.Core.Domain.defaultDomain
    Ps := Ps.push (mkApp (mkConst ``Tools.ShippingMachineChild.childRange) (mkConst cData))
    Fs := Fs.push (← mkAppM ``Tools.ShippingMachineChild.childValue
      #[mkConst cSrc, ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst cData], i0])
    -- the child's binder kinds (its declaration's binders)
    let cr ← readMachine c (allowGate := true)
    childInfo := childInfo.push (cSrc, cData, cr.shape.binders.take cr.nDecl |>.map (·.2))
  let nat := mkConst ``Nat
  let listNat := mkApp (mkConst ``List [.zero]) nat
  let PT ← mkArrow listNat (mkSort .zero)
  let FT ← mkArrow listNat nat
  let PT' := PT
  let FT' := FT
  let PE ← withLocalDeclD `k nat fun k => do
    mkLambdaFVars #[k] (← mkAppM ``List.getD
      #[listE PT Ps.toList, k, ← mkLambdaFVars #[← mkFreshExprMVar listNat] (mkConst ``True)])
  let FE ← withLocalDeclD `k nat fun k => do
    mkLambdaFVars #[k] (← mkAppM ``List.getD
      #[listE FT Fs.toList, k, .lam `v listNat (mkNatLit 0) .default])
  p := mkApp2 p PE FE
  -- the calls' premise
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let argsL := r.shape.insts.map (·.2.1)
  let argsLE := listE listNat (argsL.map fun a => listE nat (a.map mkNatLit))
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    -- per call: the premise at its index and arguments, for every cycle
    let mut perK : Array Lean.Expr := #[]
    for k in [0:argsL.length] do
      let argsE := listE nat ((argsL[k]!).map mkNatLit)
      let restK := (rest.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1 argsE
      let proofK ← withLocalDeclD `j nat fun j => do
        let c := (restK.bindingBody!.instantiate1 j).bindingBody!
        -- the call over the source's state loop
        let some callV := (← getConstInfo (declName ++ Name.mkSimple s!"machineCall_{k}")).value?
          | throwError "{declName}: machineCall_{k}"
        -- the state loop(s), as the trace's extension applies them
        let extApp := (tyArgs[8]!).beta ibb
        let states := extApp.getAppArgs.extract 3 extApp.getAppNumArgs
        let call := callV.beta (ibb ++ states)
        let callArgs := call.getAppArgs
        let (cSrc, cData, kinds) := childInfo[k]!
        unless callArgs.size == kinds.length do
          throwError "{declName}: call {k} has {callArgs.size} arguments, the child {kinds.length} binders"
        -- the argument values
        let mut obs : Array Lean.Expr := #[]
        for (a, kd) in callArgs.toList.zip kinds do
          match kd with
          | .bits w =>
            obs := obs.push (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit w)
              (← mkAppM ``Sparkle.Core.Signal.Signal.val #[a, j]))
          | .bool =>
            obs := obs.push (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
              (← mkAppM ``Sparkle.Core.Signal.Signal.val #[a, j]))
          | .domain => pure ()
        let obsE := listE nat obs.toList
        -- `call_of_facts` at the premise: its implicit arguments from `c`
        let natNat ← mkArrow nat nat
        let mArgs ← (#[listNat, mkApp (mkConst ``List [.zero]) natNat, nat, nat, PT', FT'] :
          Array Lean.Expr).mapM fun t => mkFreshExprMVar (some t)
        let rhsM ← mkFreshExprMVar (some nat)
        let e := mkAppN (mkConst ``Tools.ShippingMachineChild.call_of_facts)
          (mArgs ++ #[obsE, rhsM])
        let (hs, _, concl) ← forallMetaTelescope (← inferType e)
        unless ← isDefEq concl c do
          throwError "{declName}: call {k}: the premise does not have the expected shape"
        let tys ← hs.mapM fun h => do instantiateMVars (← inferType h)
        -- length, bounds, values (kernel `rfl`s and `decide`), range, value
        let some (α0, lhs0, _) := tys[0]!.eq? | throwError "length"
        let hlen := mkApp2 (mkConst ``Eq.refl [← getLevel α0]) α0 lhs0
        let hbd ← mkDecideProof tys[1]!
        let some (α2, lhs2, _) := tys[2]!.eq? | throwError "values"
        let hv := mkApp2 (mkConst ``Eq.refl [← getLevel α2]) α2 lhs2
        let hP ← proveByTactic tys[3]! (← rangeTactic kinds)
        let hF ← proveByTactic tys[4]! (← valueTactic cSrc cData kinds)
        let q ← instantiateMVars (mkAppN e #[hlen, hbd, hv, hP, hF])
        unless ← isDefEq (← inferType q) c do
          throwError "{declName}: call {k}: the assembled premise does not match"
        let _ := (data, argsLE)
        mkLambdaFVars #[j] q
      perK := perK.push proofK
    -- `Q k a := ∀ j, premise at k, a, j`, shifted by `m`
    let Qm (m : Nat) : MetaM Lean.Expr :=
      withLocalDeclD `k nat fun k => withLocalDeclD `a listNat fun a => do
        let rk := (rest.bindingBody!.instantiate1 (← mkAdd k (mkNatLit m))).bindingBody!.instantiate1 a
        let body ← withLocalDeclD `j nat fun j => do
          mkForallFVars #[j] (rk.bindingBody!.instantiate1 j).bindingBody!
        mkLambdaFVars #[k, a] body
    -- the chain over the call list
    let n := argsL.length
    let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil
      #[listNat, ← Qm n]
    for m' in [0:n] do
      let m := n - 1 - m'
      let rest' := listE listNat ((argsL.drop (m + 1)).map fun a => listE nat (a.map mkNatLit))
      chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
        #[listNat, ← Qm m, listE nat ((argsL[m]!).map mkNatLit), rest', perK[m]!, chain]
    withLocalDeclD `k nat fun k => withLocalDeclD `a listNat fun a =>
    withLocalDeclD `j nat fun j => do
      let hkT := ((rest.bindingBody!.instantiate1 k).bindingBody!.instantiate1 a
        |>.bindingBody!.instantiate1 j).bindingDomain!
      withLocalDeclD `hk hkT fun hk => do
        mkLambdaFVars (ibb ++ #[k, a, j, hk]) (mkAppN chain #[k, a, hk, j])
  let _ := argsLE
  p := mkApp p hcalls
  -- the children's reflection facts in the run's contexts: `EntryDefines` for
  -- a gate-compiled child, `MachineDefines`/`MachineCloses` for a machine one
  let kids := (r.shape.insts.map (·.1)).eraseDups
  let mut rTypes : List Lean.Expr := []
  let mut gateOf : Std.HashMap Name Bool := {}
  for c in kids do
    if (← getEnv).contains (c ++ `machine_sound) then
      discard <| Tools.ShippingGateChildCommand.generateMachineChildLinked c
      gateOf := gateOf.insert c false
      let shapeE ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]
      rTypes := rTypes ++ [← mkAppM ``And #[mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineDefines) (ctx ++ #[toExpr c, shapeE]),
        mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineCloses) (ctx ++ #[toExpr c, shapeE])]]
    else
      unless (← getEnv).contains (c ++ `gate_linked) do
        throwError "{declName}: run #gate_child {c} first"
      gateOf := gateOf.insert c true
      rTypes := rTypes ++ [mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
        (ctx ++ #[toExpr c, mkConst (c ++ `gateValue)])]
  let rDecls := (kids.zip rTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hR{j}", fun (_ : Array Lean.Expr) => pure ty)
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
    let lem := mkIdent (`_root_ ++ c ++ (if gateOf.getD c true then `gate_linked else `child_linked))
    let tac ← if gateOf.getD c true then
        `(tactic| (exact ⟨rfl, fun mc Dc w w' hrun => $lem mc ⟨_, _, _, _, w, w', Dc, hrun, $hRS⟩⟩))
      else
        `(tactic| (exact ⟨rfl, fun mc Dc w w' hrun => $lem mc ⟨_, _, _, _, w, w', Dc, hrun, ($hRS).1, ($hRS).2⟩⟩))
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
  let p := mkApp p chain
  -- the run boundary: `ChildSynthIs` and the children's reflection facts, bundled
  let bTypes := (← Tools.ShippingChildCache.splitOf (← inferType hsyn)) :: rTypes
  let bnd ← Tools.ShippingMachineShipsHierCommand.conj bTypes
  let value ← withLocalDeclD `hBnd bnd fun hBnd => do
    let ps ← Tools.ShippingMachineShipsHierCommand.projs hBnd bTypes
    let p' := p.replaceFVars (#[hsyn] ++ hRs) ((← Tools.ShippingChildCache.synOf ps.head!) :: ps.tail).toArray
    mkLambdaFVars (xs.pop ++ #[hBnd]) p'
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name


def generateComposedR (declName : Name) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => Lean.Elab.async.set o false) (generateComposedRCore declName)
  catch ex =>
    setEnv saved
    throw ex

/-- `f.machine_ships_hierHR`: `machine_ships_hierH` with the trivial calls'
premise and the derived run boundary. -/
def generateShipsHR (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_ships_hierHR
  if (← getEnv).contains name then return name
  let cR ← generateComposedR declName
  let r ← readMachine declName
  let soundHead := match (← getConstInfo (declName ++ `machine_sound)) with
    | .thmInfo t => t.value.getAppFn.constName?.getD .anonymous
    | _ => .anonymous
  let (head, _, wiredL) := headsOf soundHead r.nested
  let args ← soundArgs declName head
  let soundL := mkAppN (mkConst wiredL) args
  let data := mkConst (declName ++ `machineData)
  let cT := mkConst cR
  forallTelescope (← inferType cT) fun ys _ => do
    unless ys.size == 12 do throwError "{declName}: the composed theorem's binders ({ys.size})"
    let Bnd ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!, ys[6]!, ys[7]!] (← inferType ys[11]!)
    let trueR ← withLocalDeclD `k (mkConst ``Nat) fun k =>
      withLocalDeclD `mc (mkConst ``Sparkle.IR.AST.Module) fun mc => mkLambdaFVars #[k, mc] (mkConst ``True)
    let thm ← mkAppOptM ``Tools.ShippingMachineShipsHierH.machine_ships_hierH
      #[trueR, Bnd, none, data, none, none, none, none, none, none, none, none, soundL, cT]
    let thm ← instantiateMVars thm
    let ty ← inferType thm
    let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
    let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
    if thm.hasMVar then throwError "{declName}: unassigned arguments"
    addTheorem name (← inferType thm) thm
    return name

/-- `f.machine_design_svHR`: source → the closed emitted texts (existence and
every closed run) from `f.machine_ships_hierHR`. -/
def generateDesignHR (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_design_svHR
  if (← getEnv).contains name then return name
  let ships ← generateShipsHR declName
  let some (.thmInfo ti) := (← getEnv).find? ships | throwError "{ships}: not a theorem"
  let r := ti.value.getAppArgs[0]!
  let bnd0 := ti.value.getAppArgs[1]!
  let ty ← inferType (mkConst ships)
  let value ← forallTelescope ty fun xs _ => do
    let h := mkAppN (mkConst ships) xs
    let bnd ← Tools.ShippingShipsDesignSVCommand.bndAt ships xs bnd0
    let v ← mkAppOptM ``Tools.ShippingShipsDesignSVAll.ships_design_svH_all
      #[r, bnd, none, none, none, none, none, none, none, none, h]
    let v ← instantiateMVars v
    if v.hasMVar then throwError "{declName}: the composition's arguments were not all inferred"
    mkLambdaFVars xs v
  addTheorem name (← inferType value) value
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return name

elab "#machine_design_svHR " d:ident : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateDesignHR declName)
  logInfo m!"{name}: source → shipped design's closed emitted texts, combinational children, the run boundary derived (RefIs + CacheReads + the children's reflection), checked by the kernel"

end Tools.ShippingMachineComposeRCommand
