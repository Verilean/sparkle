import Tests.Compiler.ParentHoutTyHTest
import Tests.Compiler.FinalGoalTest
import Tools.ShippingParentSeqComposedA
-- BUILT (unit SR3h): s2 exit 0 (Tools.ShippingParentSeqComposedA); c14 exit 0 (Tests.Compiler.ParentSeqComposedATest; c1-c13 exit 1: instances, oldArg% scoping, dcH arg order, audit). In-test audit THROWS on failure.
-- SCOPE (binding): `parent`'s child `cnt` is a SEQUENTIAL leaf (two-field struct result), on the `seq_child_runN` /
-- `machine_linkedT_callsRNA` route, NOT the one-output `child_linked` route. This file builds `soundL` and `composed` for `parent`
-- on the new boundary FROM `BndA` (O, T, AdmCtx, MachineDefines cnt, a JQ start world): the trace `ServedRealA` comes from
-- `machine_traceL_of_data_causalRA_ranA` (MachineRunJQC from `parent_closesA`), the per-call facts `hcalls` are the OLD ones
-- (they mention neither the boundary nor O), and `hrunN` (cnt) is `MachineRun cnt` from the run of cnt's entry + `MachineDefines.ctx`
-- + `cnt.machine_closes`. NOT unconditional semantic equivalence; RealChildA is a history; `T : RefLawsATele` is an ADDED boundary.
namespace Tests.Compiler.ParentSeqComposedATest
open Tests.Compiler.ParentEndpointFactsATest Tests.Compiler.ParentEndpointMaskedATest
open Tests.Compiler.ParentEndpointMaskedATest Tests.Compiler.KidsMaskedParentATest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingParentSeqComposedA Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA
open Tools.ShippingServedRealA Tools.ShippingChildDepthC Tools.ShippingChildTranslateA Tools.ShippingParentRanA
open Tests.Compiler.KidsMaskedParentATest Tests.Compiler.ParentEndpointFactsATest
open Tools.ShippingChildComposeC Tools.ShippingChildRunAMain

open Lean Elab Term Meta in
/-- `oldArg% i j …`: the `j`-th argument of the `i`-th argument of the value of `parent.machine_composedNR1` (a closed term, or one
whose free variables are the binders `m`, `design`, … of that value, matched by user name in the local context). -/
elab "oldArg% " ns:num+ : term => do
  let some (.thmInfo ti) := (← getEnv).find? ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_composedNR1
    | throwError "oldArg%: no old theorem"
  let lctx0 ← getLCtx
  lambdaTelescope ti.value fun ys body => do
    let mut a := body
    for n in ns do
      a := a.getAppArgs[n.getNat]!
    let mut r := a
    for y in ys do
      if r.containsFVar y.fvarId! then
        let nm ← y.fvarId!.getUserName
        match lctx0.findFromUserName? nm with
        | some l => r := r.replaceFVar y l.toExpr
        | none => throwError "oldArg%: no local named {nm}"
    let st := (Lean.collectFVars {} r)
    for f in st.fvarIds do
      unless lctx0.contains f do
        let d ← f.getDecl
        throwError "oldArg%: stray fvar {d.userName} : {d.type} in the term"
    return r

/-- the `Inhabited` instance the old chain used (argument 4 of its trace head), so that the `letObsB` of the statements is the same term -/
local instance parentInhabHL : Inhabited (HList (Tools.ShippingMachineDenote.tys parent.machineData.ss)) := oldArg% 15 4

set_option maxHeartbeats 4000000 in
/-- **The trace of `parent` carrying `ServedRealA`**, from the data `BndA` unpacks to (`O`, `T`, `AdmCtx`, `MachineDefines cnt`, a `JQ` start). -/
theorem parent_traceXA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``parent parent.machineData.shape m design)
      ``parent parent.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) parent.machineSource
      (fun i bools bits => parent.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop parent.machineInits (parent.machineBody i bools bits)))
      (fun i bools bits => parent.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop parent.machineInits (parent.machineBody i bools bits)))
      (letObsB parent.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) parent.machineInits
        parent.machineBody parent.machineExt parent.machineExtB) :=
  @machine_traceL_of_data_causalRA_ranA (oldArg% 15 0) (oldArg% 15 1) (oldArg% 15 2) (oldArg% 15 3) (oldArg% 15 4)
    (oldArg% 15 5) (oldArg% 15 6) (oldArg% 15 7) (oldArg% 15 8) (oldArg% 15 9) (oldArg% 15 10) (oldArg% 15 11)
    (oldArg% 15 12) (oldArg% 15 13) (oldArg% 15 14) (oldArg% 15 15) (oldArg% 15 16) (oldArg% 15 17) (oldArg% 15 18)
    mctx mref cctx cref O (bodyStepC_of_tele O T) hA (D₀ + 1) (htr_of_tele O hA T D₀) m design
    (machineRunJQC_of_closesA O hA hcore entry (parent_closesA O T hA hR0) hw hc)

/-- **`soundL` for `parent`** (MachineTraceLB), from `BndA` and the core run: `parent_traceXA` with `ServedRealA` forgotten. -/
theorem parent_soundLA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (hBnd : BndA mctx mref cctx cref w m design) :
    MachineTraceLB ``parent parent.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      parent.machineSource
      (fun i bools bits => parent.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop parent.machineInits (parent.machineBody i bools bits)))
      (fun i bools bits => parent.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop parent.machineInits (parent.machineBody i bools bits)))
      (letObsB parent.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) parent.machineInits
        parent.machineBody parent.machineExt parent.machineExtB) := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ := parent_traceXA O T hA hR0 hw hc hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

set_option maxHeartbeats 4000000 in
/-- **`composed` for `parent`** (depth 1, `ComposedG`), from `BndA` and the core run, through `machine_linkedT_callsRNA`: the callee `cnt`
(a sequential leaf) enters by `hrunN` = `MachineRun cnt` of the run of cnt's entry (`MachineDefines.ctx`, `cnt.machine_closes`). -/
theorem parent_composedA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (hBnd : BndA mctx mref cctx cref w m design) :
    ComposedG (fun D => KSn (childMap D.modules) 1) (ResetNk 1) ``parent parent.machineData 1 m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) parent.machineSource
      (fun i bools bits => parent.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop parent.machineInits (parent.machineBody i bools bits)))
      (fun i bools bits => parent.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop parent.machineInits (parent.machineBody i bools bits))) := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have h := parent_traceXA O T hA hR0 hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 1 O h (oldArg% 16) (oldArg% 17) (oldArg% 18) (oldArg% 19) (oldArg% 20) (oldArg% 21)
    (oldArg% 22) (oldArg% 23) (oldArg% 24) (oldArg% 25) (oldArg% 26) (oldArg% 27) (oldArg% 28) (oldArg% 29)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < parent.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``cnt := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact parent_insts_cnt k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``cnt cnt.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          cnt.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
/- **`parent`'s depth-1 endpoint with `soundL`, `composed` AND `houtTy` supplied**: `parent_noShips_noBdA_dcH` at `n := 1`, `C := True`,
with `parent_soundLA` / `parent_composedA` as `soundL` / `composed`. The theorem `parent_noShips_noBdA_dcHL` is ADDED by this command
(its type is the inferred type of the term; the audit below reads it back). Remaining premises: `hr`, `entry`, `closes` (the trivial
`True`); `BndA` (existential over `O`/`T`/`AdmCtx`/`MachineDefines cnt`/start world) stays in the conclusion. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(@Tests.Compiler.ParentHoutTyTest.parent_noShips_noBdA_dcH 1 1 (fun _ _ _ _ => True) Unit
    (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hBnd => parent_soundLA hcore entry hBnd)
    (fun hcore entry _ hBnd _ => parent_composedA hcore entry hBnd))
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the endpoint term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.ParentSeqComposedATest.parent_noShips_noBdA_dcHL, levelParams := [], type := ty, value := e }

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := `Tests.Compiler.ParentSeqComposedATest.parent_noShips_noBdA_dcHL
  stdAxioms new
  stdAxioms ``parent_soundLA
  stdAxioms ``parent_composedA
  let ty := (← getConstInfo new).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR3h AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  -- `closes` is the trivial `True`
  forallTelescope ty fun xs _ => do
    let some c := xs.back? | throwError "no binder"
    unless (← whnf (← inferType c)).isConstOf ``True do throwError "SR3h AUDIT FAILED: closes is not True"
  let cl ← depClosure new
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{new}: old boundary in closure: {bad}"
  for must in [``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingParentRanA.machineRanA_main, ``Tests.Compiler.ParentHoutTyTest.parent_houtTy,
      ``Tools.ShippingMachineShipsDepth.composedG_of_NW, ``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA,
      ``Tools.ShippingServedRealA.machineRunJQC_of_closesA, ``Tests.Compiler.ParentDesignCheckFATest.parent_designCheckFA] do
    unless cl.contains must do throwError "SR3h AUDIT FAILED: {must} not in the closure"
  -- the conclusion still carries BndA, and is at depth 1
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  unless (concl.find? (·.isConstOf ``Tests.Compiler.ParentEndpointMaskedATest.BndA)).isSome do
    throwError "SR3h AUDIT FAILED: BndA not in the conclusion"
  -- the conclusion is `_dc`'s at `kD := 1`, `n := 1`: all shared binders (`mctx … closes`) as FVARS of the new theorem, `_dc`'s
  -- other binders as metavariables that the comparison must assign
  let oldTy := (← getConstInfo ``Tests.Compiler.ParentDesignCheckFATest.parent_noShips_noBdA_dc).type
  forallTelescope ty fun newXs newC => do
    let (oldMs, _, oldC) ← forallMetaTelescope oldTy
    unless oldMs.size ≥ 11 do throwError "SR3h AUDIT FAILED: _dc has too few binders"
    -- `kD` (auto-bound) and `n` are the first two binders; the supplied composed fixes both to 1
    let ok0 ← isDefEq oldMs[0]! (mkNatLit 1)
    let ok1 ← isDefEq oldMs[1]! (mkNatLit 1)
    unless ok0 && ok1 do throwError "SR3h AUDIT FAILED: kD/n are not the literal 1"
    -- C := fun _ _ _ _ => True
    let Cfun ← mkLambdaFVars (newXs.extract 0 4) (mkConst ``True)
    unless (← isDefEq oldMs[2]! Cfun) do throwError "SR3h AUDIT FAILED: C"
    unless newXs.size == 11 do throwError "SR3h AUDIT FAILED: new theorem has {newXs.size} binders, expected 11 (mctx mref cctx cref w w' b design hr entry closes)"
    let tailMs := oldMs.extract (oldMs.size - 11) oldMs.size
    for (a, b) in tailMs.zip newXs do
      unless (← isDefEq a b) do throwError "SR3h AUDIT FAILED: binder mismatch {← ppExpr a} vs {← ppExpr b}"
    unless (← isDefEq oldC newC) do throwError "SR3h AUDIT FAILED: conclusion differs from parent_noShips_noBdA_dc's (kD = n = 1, shared binders as fvars)"
  logInfo m!"SR3h AUDIT OK: {new}: standard axioms; outer Prop premises ASSERTED {premises}; soundL, composed, houtTy no longer premises; closure {cl.size} constants, none of RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV; BndA stays in the conclusion; conclusion isDefEq to parent_noShips_noBdA_dc's at kD = n = 1 with the shared binders as fvars"

#print axioms parent_soundLA
#print axioms parent_composedA
#print axioms Tests.Compiler.ParentSeqComposedATest.parent_noShips_noBdA_dcHL
end Tests.Compiler.ParentSeqComposedATest
