import Tests.Compiler.ShippingChildBoundaryTest
/-! Premises of the derived endpoints, by kind (run: `lake env lean scripts/shipping-coverage/endpoint_premises.lean`).
For each endpoint: the child boundary, the reflection facts, the decidable use conditions, any retired
boundary still mentioned (expected: none), and its axioms; then the generic laws' fields. -/
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
      ``Tools.ShippingMachineDepthH.BoundH, ``Tools.ShippingMachineCompose.ChildFn])]
  let env ← getEnv
  for e in es do
    let ty ← instantiateMVars (← inferType (mkConst e))
    let cs := deepConsts env ty
    let mut line := s!"{e.getPrefix.getString!}.{e.getString!}:"
    for (cat, names) in cats do
      let hit := names.filter cs.contains
      line := line ++ s!" {cat}={hit.map (·.getString!)}"
    -- how many reflection facts (top-level and inside children's boundaries)
    let axs ← Lean.collectAxioms e
    line := line ++ s!" axioms={axs.toList.map (·.toString)}"
    logInfo line
  -- the laws: RefLaws' fields
  let some (.inductInfo ii) := env.find? ``Tools.ShippingChildInv.RefLaws | throwError "RefLaws"
  let ctor := ii.ctors.head!
  let fields := getStructureFields env ``Tools.ShippingChildInv.RefLaws
  logInfo m!"RefLaws fields: {fields} (ctor {ctor})"
  let some (.inductInfo fi) := env.find? ``Tools.ShippingChildInv.Framed | throwError "Framed"
  logInfo m!"Framed: {fi.ctors.map (·.getString!)}"
  let some (.inductInfo si) := env.find? ``Tools.ShippingChildInv.SideRef | throwError "SideRef"
  logInfo m!"SideRef: {si.ctors.map (·.getString!)}"
