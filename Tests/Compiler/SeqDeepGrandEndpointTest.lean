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
open Tools.ShippingChildComposeC Tools.ShippingChildRunAMain Tools.ShippingMachineShipsDepth Tools.ShippingHierStateG Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
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

end

end Tests.Compiler.SeqDeepGrandEndpointTest
