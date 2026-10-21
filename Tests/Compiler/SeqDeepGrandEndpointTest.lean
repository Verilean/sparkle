import Tests.Compiler.SeqDeepGrandKidFactsTest
import Tests.Compiler.SeqParentGenTest
import Tests.Compiler.ParentSeqComposedATest
import Tools.ShippingSeqChildDeepRunA
-- UNBUILT (unit SR3s): see the report for the build names.
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
  have hcnt : ∀ (k : Nat) (hk : k < grand.machineData.shape.insts.length),
      ((List.take 2 mid.machineData.bsIn).filter fun b => b.2 != .domain).length =
        (grand.machineData.shape.insts[k]).2.1.length := by
    first | decide | decide +kernel
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
      refine ((oldArgOf% Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 29) i bools bits k _ hk).imp id (fun hS => ?_)
      refine Tools.ShippingSeqChildDeepRunA.seqFactsRN_of_conv (fun mc hmc => mid_seqChildRunN2 O T hmc) ?_ hS
      intro args hargs
      rw [List.getElem?_map, List.getElem?_eq_getElem hk'] at hargs
      cases hargs
      exact hcnt k hk')
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

end Tests.Compiler.SeqDeepGrandEndpointTest
