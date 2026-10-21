import Tests.Compiler.SeqDeepGrandKidFactsTest
import Tests.Compiler.SeqParentGenTest
import Tests.Compiler.ParentSeqComposedATest
import Tools.ShippingSeqChildDeepRunA
-- BUILT (unit SR3s): see the report for the build names and exits (BUILT lines in the final run are authoritative).
-- SCOPE (binding): `grand -> mid -> cnt`, from ONE core run of `grand`: the trace `ServedRealA`, `soundL` (MachineTraceLB) and
-- `composed` (depth 2, `ComposedG`) of `grand`, on the new boundary.  The depth-1 `composed` of the child `mid` is proved on the new
-- boundary (`mid_composedA`, with its own callee `cnt`), turned into `SeqChildRunN` at depth 2 (`seqChildRunN_of_composedCA`), and
-- enters `grand`'s `hcalls` through `seqFactsRN_of_conv`.  `RealChildA` is a history of past synthesis results; `T` is an ADDED boundary.
namespace Tests.Compiler.SeqDeepGrandEndpointTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineLinked
open Tools.ShippingParentSeqComposedA Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA
open Tools.ShippingServedRealA Tools.ShippingChildDepthC Tools.ShippingChildTranslateA Tools.ShippingParentRanA
open Tools.ShippingMachineShipsHier Tools.ShippingChildComposeC Tools.ShippingChildRunAMain Tools.ShippingMachineShipsDepth Tools.ShippingHierStateG Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tests.Compiler.SeqDeepMidTest Tests.Compiler.SeqDeepMidFactsTest Tests.Compiler.SeqDeepGrandKidFactsTest

open Lean Elab Term Meta in
/-- `oldArgOf% thm i j …`: the `j`-th argument of the `i`-th argument of the value of the theorem `thm` (free variables matched by
user name in the local context; a stray free variable is an error). -/
elab "oldArgOf% " id:ident ns:num+ : term => do
  let nm ← realizeGlobalConstNoOverload id
  let some (.thmInfo ti) := (← getEnv).find? nm | throwError "oldArgOf%: {nm} is not a theorem"
  let lctx0 ← getLCtx
  lambdaTelescope ti.value fun ys body => do
    let mut a := body
    for n in ns do
      a := a.getAppArgs[n.getNat]!
    let mut r := a
    for y in ys do
      if r.containsFVar y.fvarId! then
        let un ← y.fvarId!.getUserName
        match lctx0.findFromUserName? un with
        | some l => r := r.replaceFVar y l.toExpr
        | none => throwError "oldArgOf%: no local named {un}"
    let st := (Lean.collectFVars {} r)
    for f in st.fvarIds do
      unless lctx0.contains f do
        let d ← f.getDecl
        throwError "oldArgOf%: stray fvar {d.userName} : {d.type} in the term"
    return r

open Lean Elab Term Meta in
/-- `oldHcallsArg% thm a j`: the `j`-th argument of the beta-redex that is the body of the lambda `a`-th argument of the value of
`thm` (the generator's `(fun gfB0 gfL0 gfR0 gfHb0 gfHv0 => …) B L R Hb Hv`; `j = 1…4` are the group facts that do NOT mention the
child predicate `PC`).  Free variables are matched by user name in the local context. -/
elab "oldHcallsArg% " id:ident a:num j:num : term => do
  let nm ← realizeGlobalConstNoOverload id
  let some (.thmInfo ti) := (← getEnv).find? nm | throwError "oldHcallsArg%: {nm} is not a theorem"
  let lctx0 ← getLCtx
  lambdaTelescope ti.value fun ys body => do
    let hc := body.getAppArgs[a.getNat]!
    lambdaTelescope hc fun zs inner => do
      unless inner.getAppFn.isLambda do throwError "oldHcallsArg%: the body is not a beta-redex: {inner.getAppFn}"
      let mut r := inner.getAppArgs[j.getNat]!
      for y in ys ++ zs do
        if r.containsFVar y.fvarId! then
          let un ← y.fvarId!.getUserName
          match lctx0.findFromUserName? un with
          | some l => r := r.replaceFVar y l.toExpr
          | none => throwError "oldHcallsArg%: no local named {un}"
      for f in (Lean.collectFVars {} r).fvarIds do
        unless lctx0.contains f do
          let d ← f.getDecl
          throwError "oldHcallsArg%: stray fvar {d.userName} : {d.type}"
      return r

local instance midInhabHL : Inhabited (HList (Tools.ShippingMachineDenote.tys mid.machineData.ss)) :=
  oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 4
local instance grandInhabHL : Inhabited (HList (Tools.ShippingMachineDenote.tys grand.machineData.ss)) :=
  oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 4

section
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The run boundary of the CHILD `mid` (new boundary): the grandchild `cnt`'s reflection at the run's contexts.  The start-world
data (`JQC`) and `AdmCtx` are fields of `MachineRunNCA`/the composed's premises. -/
def midBndA (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ =>
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape

set_option maxHeartbeats 4000000 in
/-- **The trace of `mid` carrying `ServedRealA`**, from a core run of `mid` (the analogue of `parent_traceXA`). -/
theorem mid_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``mid [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``mid mid.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``mid mid.machineData.shape m design)
      ``mid mid.machineData m design (fun i => i) mid.machineSource
      (fun i bools bits => mid.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop mid.machineInits (mid.machineBody i bools bits)))
      (fun i bools bits => mid.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop mid.machineInits (mid.machineBody i bools bits)))
      (letObsB mid.machineData (fun i => i) mid.machineInits
        mid.machineBody mid.machineExt mid.machineExtB) :=
  @machine_traceL_of_data_causalRA_ranA (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 0)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 1)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 2)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 3)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 4)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 5)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 6)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 7)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 8)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 9)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 10)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 11)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 12)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 13)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 14)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 15)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 16)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 17)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 15 18)
    mctx mref cctx cref O (bodyStepC_of_tele O T) hA (D₀ + 1) (htr_of_tele O hA T D₀) m design
    (machineRunJQC_of_closesA O hA hcore entry (mid_closesA O T hA hR0) hw hc)

set_option maxHeartbeats 4000000 in
/-- **`composed` for `mid`** at depth 1 (`ComposedNW`), on the new boundary, from a core run of `mid` (its callee `cnt` is a
sequential leaf: `hrunN` = `MachineRun cnt` of the run of cnt's entry). -/
theorem mid_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``mid [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``mid mid.machineData.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 ``mid mid.machineData 2 m design
      (fun i => i) mid.machineSource
      (fun i bools bits => mid.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop mid.machineInits (mid.machineBody i bools bits)))
      (fun i bools bits => mid.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop mid.machineInits (mid.machineBody i bools bits))) := by
  have h := mid_traceXA O T hA hR0 hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 16)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 17)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 18)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 19)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 20)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 21)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 22)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 23)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 24)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 25)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 26)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 27)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 28)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 29)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < mid.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``cnt := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact mid_insts_cnt k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``cnt cnt.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          cnt.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

open Tools.ShippingMachineChild (boolsOf bitsOf) in
set_option maxHeartbeats 4000000 in
/-- **`mid`'s `SeqChildRunN` at depth 2** from a `MachineRunNCA` of `mid` (new boundary): `seqChildRunN_of_composedCA` with the
depth-1 composed `mid_composedA`; the side facts are the old chain's (`mid.seq_child_runN_ofR1`'s arguments, none mentions the boundary). -/
theorem mid_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``mid mid.machineData.shape (midBndA mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take 2 mid.machineData.bsIn)
      mid.machineData.shape.layout.outs
      (fun vals => mid.machineSource Sparkle.Core.Domain.defaultDomain
        (boolsOf (List.take 2 mid.machineData.bsIn) vals) (bitsOf (List.take 2 mid.machineData.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (midBndA mref cref)
    (fun hcore hadm hjqc entry _ hB => mid_composedA O T hadm hB hjqc.1 (Or.inr hjqc.2) hcore entry)
    (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 11) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 12) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 13) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 14) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 15) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 16) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 17) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 18) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 19) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 20) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 21) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 22)
    Sparkle.Core.Domain.defaultDomain h

set_option maxHeartbeats 4000000 in
/-- **The trace of `grand` carrying `ServedRealA`**, from a core run of `grand` (the analogue of `parent_traceXA`; the closing is
`grand_closesA`, whose child interface is `mid_ifaceP`). -/
theorem grand_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``grand [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``grand grand.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``grand grand.machineData.shape m design)
      ``grand grand.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) grand.machineSource
      (fun i bools bits => grand.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (fun i bools bits => grand.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (letObsB grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) grand.machineInits
        grand.machineBody grand.machineExt grand.machineExtB) :=
  @machine_traceL_of_data_causalRA_ranA (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 0) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 1) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 2) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 3) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 4) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 5) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 6) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 7) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 8) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 9) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 10) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 11) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 12) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 13) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 14) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 15) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 16) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 17) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 15 18)
    mctx mref cctx cref O (bodyStepC_of_tele O T) hA (D₀ + 1) (htr_of_tele O hA T D₀) m design
    (machineRunJQC_of_closesA O hA hcore entry (grand_closesA O T hA hM hR0) hw hc)

/-- **`soundL` for `grand`** (MachineTraceLB): `grand_traceXA` with `ServedRealA` forgotten. -/
theorem grand_soundLA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``grand [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``grand grand.machineData.shape) :
    Tools.ShippingMachineAuto.MachineTraceLB ``grand grand.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      grand.machineSource
      (fun i bools bits => grand.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (fun i bools bits => grand.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (letObsB grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) grand.machineInits
        grand.machineBody grand.machineExt grand.machineExtB) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    grand_traceXA O T hA hM hR0 hw hc hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

set_option maxHeartbeats 4000000 in
/-- **`composed` for `grand`** (depth 2, `ComposedG`), from the same core run, through `machine_linkedT_callsRNA 2`: the callee `mid`
(a child with a grandchild) enters through `MachineRunNCA` (from the served `RealChildA`, `machineRunNCA_of_real_main`) and
`mid_seqChildRunN2`; the per-call facts are the old ones with the child predicate changed by `seqFactsRN_of_conv`. -/
theorem grand_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``grand [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``grand grand.machineData.shape) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``grand grand.machineData 1 m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) grand.machineSource
      (fun i bools bits => grand.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (fun i bools bits => grand.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits))) := by
  have h := grand_traceXA O T hA hM hR0 hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 16) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 17) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 18) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 19) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 20) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 21) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 22) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 23) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 24) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 25) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 26) (oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 27)
    (fun _ mc => Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``mid mid.machineData.shape (midBndA mref cref) mc design)
    (fun i bools bits k c hk => by
      have hk' : k < grand.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1; simpa using this
      have hck : c = ``mid := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk'] at hk
        rw [← Option.some.inj hk]
        exact (grand_insts_mid k hk').1
      subst hck
      -- the group facts of the generated proof that do not mention the child predicate
      have L := (oldHcallsArg% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 29 1)
      have R := (oldHcallsArg% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 29 2)
      have Hb := (oldHcallsArg% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 29 3)
      have Hv := (oldHcallsArg% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 29 4)
      have hlt : k < 2 := by
        have : grand.machineData.shape.insts.length = 2 := by first | decide | decide +kernel
        omega
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      rcases k with _ | _ | k
      · refine ⟨rfl, [0], rfl, (fun mc hmc => ⟨mid_seqChildRunN2 O T hmc, by rw [(mid_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩
        exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (mid.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl
      · refine ⟨rfl, [0], rfl, (fun mc hmc => ⟨mid_seqChildRunN2 O T hmc, by rw [(mid_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩
        exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (mid.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl
      · omega)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < grand.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``mid := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact (grand_insts_mid k hk).1
      subst hck
      exact Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main O T
        (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons hM
        (fun mctx cctx _ w raw D _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR0)
        (fun mctx cctx w raw D hin _ => by
          obtain ⟨_, _, _, hadm', _⟩ := hin
          exact mid_closesA O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
        (by first | decide | decide +kernel))

end


/-- The run boundary of the NEW depth-2 endpoint of `grand`: laws `O`, `T` (PREMISES, a separate assumption family), the admissible
contexts, `MachineDefines` of the callee `mid` AND of its callee `cnt`, and a start world in `JQ`.  It replaces `ChildBnd`. -/
def BndAg : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``mid mid.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

theorem grand_houtTy : ∀ o ∈ grand.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
/- **`grand`'s depth-2 endpoint on the new boundary, with `soundL`, `composed`, `houtTy` and the four checks SUPPLIED**:
`machine_design_noShips_noBd_dc` at `n := 2`, `kD := 1`, `C := True`, `Bnd := BndAg`; `soundL` := `grand_soundLA`, `composed` :=
`grand_composedA`, `hFacts` / `hOuts` / `hBdRun` / `hdc` := `grand_runFacts` / `grand_outsCheck` / `grand_kidsMasked` /
`grand_designCheck` (SR3r) at `n := 1` (their depth is `n + 1 = 2`), all from the SAME core run.  The theorem `grand_noShips_noBdA_dcH` is
ADDED by this command (its type is the inferred type of the term; the audit reads it back). Remaining premises: `hr`, `entry`,
`closes` (the trivial `True`); `BndAg` (existential over `O`/`T`/`AdmCtx`/`MachineDefines mid`/`MachineDefines cnt`/start world)
stays in the conclusion. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 2 BndAg (fun _ _ _ _ => True)
    ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData 1 Unit
    (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_soundLA O T hA hM hR0 hw hc hcore entry)
    (fun hcore entry _ hB _ => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_composedA O T hA hM hR0 hw hc hcore entry)
    grand_houtTy
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_runFacts O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry _ hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_outsCheck O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_kidsMasked O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_designCheck O T 1 hA hM hR0 hcore hpost entry hw hc))
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the endpoint term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH, levelParams := [], type := ty, value := e }

#print axioms grand_soundLA
#print axioms grand_composedA
#print axioms Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH


open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := `Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH
  for nm in [new, ``grand_soundLA, ``grand_composedA, ``grand_traceXA, ``mid_composedA, ``mid_seqChildRunN2] do
    stdAxioms nm
  let ty := (← getConstInfo new).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR3s AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let cl ← depClosure new
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
     `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingMachineDepthRun.machineRunNC_of_real,
     `Tools.ShippingMachineDepthRunR.seqChildRunN_of_composedC].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{new}: old boundary / old child predicate in closure: {bad}"
  for must in [``grand_soundLA, ``grand_composedA, ``grand_traceXA, ``mid_composedA, ``mid_seqChildRunN2, ``grand_designCheck,
      ``grand_runFacts, ``grand_outsCheck, ``grand_kidsMasked, ``grand_closesA, ``mid_ifaceP, ``Tests.Compiler.SeqDeepMidKidFactsTest.mid_kidFactsA,
      ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingParentRanA.machineRanA_main, ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc] do
    unless cl.contains must do throwError "SR3s AUDIT FAILED: {must} not in the closure"
  -- the old composed theorem of grand supplies only PC-free subterms (its L, R, Hb, Hv): the theorem itself is not in the closure
  unless !cl.contains `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 do
    throwError "SR3s AUDIT FAILED: the old grand.machine_composedNR2 constant is in the closure"
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  unless (concl.find? (·.isConstOf ``BndAg)).isSome do throwError "SR3s AUDIT FAILED: BndAg not in the conclusion"
  logInfo m!"SR3s AUDIT OK: {new}: standard axioms; outer Prop premises ASSERTED {premises}; soundL, composed, houtTy and the four checks are no longer premises; closure {cl.size} constants, none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/seqChildRunN_of_composedC; BndAg stays in the conclusion"

end Tests.Compiler.SeqDeepGrandEndpointTest
