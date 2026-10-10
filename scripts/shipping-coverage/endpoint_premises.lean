import Tests.Compiler.ShippingChildBoundaryTest
/-! Premises of the derived endpoints, by kind (run, inside the cgroup:
`scripts/shipping-coverage/cgrun.sh -n premises -- lake env lean scripts/shipping-coverage/endpoint_premises.lean`).
For each endpoint, with the generated boundary definitions UNFOLDED and applied: the child boundary,
the reflection facts — how many are asked in the endpoint's own contexts and how many in bound
contexts, and how many context quantifiers are guarded by `ChildRanIn` —, the decidable use
conditions, any retired boundary or proved condition still mentioned (expected: none), and its
axioms; then what `ChildBnd` unfolds to and the generic laws' fields. -/
open Lean Meta
open Sparkle.Tests.Compiler.ShippingChildBoundaryTest

/-- Constants of `e`, unfolding the generated boundary definitions. -/
partial def deepConsts (env : Environment) (e : Expr) (seen : NameSet := {}) : NameSet := Id.run do
  let mut acc := seen
  for n in e.getUsedConstants do
    if acc.contains n then continue
    acc := acc.insert n
    if (n.toString.splitOn "machineBound").length > 1 then
      if let some v := env.find? n >>= (·.value?) then acc := deepConsts env v acc
  return acc

/-- `e` with the generated boundary definitions unfolded and applied. -/
partial def unfoldBnd (env : Environment) (e : Expr) : Expr :=
  let e' := e.replace fun x =>
    match x.getAppFn with
    | .const n _ =>
      if (n.toString.splitOn "machineBound").length > 1 then
        (env.find? n >>= (·.value?)).map fun v => (mkAppN v x.getAppArgs).headBeta
      else none
    | _ => none
  if e' == e then e else unfoldBnd env e'

/-- Occurrences of `c` applied with its Meta context a free variable (the endpoint's own
contexts) / a bound variable (contexts quantified inside the premise). -/
def ctxKinds (c : Name) (argIdx : Nat) (e : Expr) : Nat × Nat := go e (0, 0)
where
  go (e : Expr) (acc : Nat × Nat) : Nat × Nat :=
    let acc := if e.isAppOf c && e.getAppNumArgs > argIdx then
        (if (e.getArg! argIdx).isFVar then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1)) else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- Quantifiers over a Meta context inside `e`. -/
partial def ctxForalls (e : Expr) : Nat :=
  match e with
  | .forallE _ t b _ => (if t.isConstOf ``Lean.Meta.Context then 1 else 0) + ctxForalls t + ctxForalls b
  | .app f a => ctxForalls f + ctxForalls a
  | .lam _ t b _ => ctxForalls t + ctxForalls b
  | .letE _ t v b _ => ctxForalls t + ctxForalls v + ctxForalls b
  | .mdata _ b | .proj _ _ b => ctxForalls b
  | _ => 0

run_cmd Lean.Elab.Command.liftTermElabM do
  let es := rEndpoints ++ hrDecls.map (· ++ `machine_design_svHR) ++
    nrEndpoints.map (fun (f, n) => f ++ Lean.Name.mkSimple s!"machine_design_svNR{n}") ++
    [``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2,
     ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2,
     ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3, ``mixDeep.machine_design_svNR2]
  let cats : List (String × List Name) := [
    ("bnd", [``Tools.ShippingChildInv.ChildBnd]),
    ("refl", [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingMachineEntry.MachineCloses,
      ``Tools.ShippingInlineSoundness.EntryDefines]),
    ("check", [``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSVBack.outsCheck,
      ``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingHierPremises.shipsHierHCheck,
      ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingMachineShipsHier.kidsMem,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingMachineDepthH.kidsComb]),
    ("old", [`Tools.ShippingChildSynth.ChildSynthIs, `Tools.ShippingChildCache.RefIs,
      `Tools.ShippingChildCache.CacheReads, `Tools.ShippingChildInv.EntryHoare,
      `Tools.ShippingChildInv.HarnessHoare, ``Tools.ShippingMachineSeqCommand.BoundaryOf,
      ``Tools.ShippingMachineCallsLinkedT.InstOfCall, ``Tools.ShippingGateChild.MachineRun,
      ``Tools.ShippingGateChild.GateRun, ``Tools.ShippingMachineDepthRun.MachineRunN,
      ``Tools.ShippingMachineDepthRun.MachineRunNC, ``Tools.ShippingMachineDepthH.BndH,
      ``Tools.ShippingMachineDepthH.BoundH, ``Tools.ShippingMachineCompose.ChildFn,
      ``Tools.ShippingChildInv.BodyRel, ``Tools.ShippingChildInv.LegacyRel,
      ``Tools.ShippingChildInv.HarnessRel, ``Tools.ShippingChildInv.TranslateRel])]
  let env ← getEnv
  for e in es do
    let ty ← instantiateMVars (← inferType (mkConst e))
    let cs := deepConsts env ty
    let mut line := s!"{e.getPrefix.getString!}.{e.getString!}:"
    for (cat, names) in cats do
      let hit := names.filter cs.contains
      line := line ++ s!" {cat}={hit.map (·.getString!)}"
    -- the reflection facts by the contexts they are asked in (boundaries unfolded)
    let kinds ← forallTelescope ty fun _ body => do
      let hyps ← (← getLCtx).foldlM (init := #[]) fun a d => pure (a.push d.type)
      let all := (hyps.push body).map (unfoldBnd env ·)
      let sum (c : Name) : Nat × Nat := all.foldl (fun (o, b) e =>
        let (o', b') := ctxKinds c 0 e; (o + o', b + b')) (0, 0)
      let md := sum ``Tools.ShippingMachineEntry.MachineDefines
      let ed := sum ``Tools.ShippingInlineSoundness.EntryDefines
      let mcl := sum ``Tools.ShippingMachineEntry.MachineCloses
      let ran := all.foldl (fun n e => n + (ctxKinds ``Tools.ShippingChildInv.ChildRanIn 3 e).2) 0
      let qs := all.foldl (fun n e => n + ctxForalls e) 0
      pure s!" defines(own,bound)={md} entryDefines(own,bound)={ed} closes(own,bound)={mcl} ctx-quantifiers={qs} ChildRanIn-guards={ran}"
    line := line ++ kinds
    let axs ← Lean.collectAxioms e
    line := line ++ s!" axioms={axs.toList.map (·.toString)}"
    logInfo line
  -- what the child boundary unfolds to
  let unfoldAt (c : Name) : MetaM Expr := do
    forallTelescope (← inferType (mkConst c)) fun xs _ => whnfD (mkAppN (mkConst c) xs)
  logInfo m!"ChildBnd  := {← unfoldAt ``Tools.ShippingChildInv.ChildBnd}"
  logInfo m!"ChildLaws := {← unfoldAt ``Tools.ShippingChildInv.ChildLaws}"
  logInfo m!"StartW    := {← unfoldAt ``Tools.ShippingChildInv.StartW}"
  logInfo m!"ChildRanIn := {← unfoldAt ``Tools.ShippingChildInv.ChildRanIn}"
  -- the laws: RefLaws' fields
  let some (.inductInfo ii) := env.find? ``Tools.ShippingChildInv.RefLaws | throwError "RefLaws"
  let ctor := ii.ctors.head!
  let fields := getStructureFields env ``Tools.ShippingChildInv.RefLaws
  logInfo m!"RefLaws fields: {fields} (ctor {ctor})"
  let some (.inductInfo fi) := env.find? ``Tools.ShippingChildInv.Framed | throwError "Framed"
  logInfo m!"Framed: {fi.ctors.map (·.getString!)}"
  let some (.inductInfo si) := env.find? ``Tools.ShippingChildInv.SideRef | throwError "SideRef"
  logInfo m!"SideRef: {si.ctors.map (·.getString!)}"
