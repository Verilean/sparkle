import Tests.Compiler.TopShareTraceTest
import Tools.ShippingQuadLeafGeneric
-- BUILT (unit SR13): g8 exit 0 (dev run, with the statement audit); the final-SHA rebuild is in REPORT-SR13.md.
-- SCOPE (binding): the `topshare` instances of `Tools/ShippingQuadLeafGeneric.lean` — the data-generic lemmas re-derive, for the real declarations
-- `topshare` (callees `wrap`, `wrap3`; shared leaf `acc`), the statements that `TopShareInstTest` / `TopShareTraceTest` proved by hand
-- (`wrap_calleeOK`, `wrap3_calleeOK`, `wrap3_ifaceP`, `topshare_closes0`, `topshare_machineRun`).  The OLD theorems are untouched and stay;
-- here each new proof is `generic lemma + decided data facts`; the statement is written out and must be accepted by the elaborator (statement equality
-- with the old theorem is checked at the bottom by `isDefEq` on the TYPES).  PREMISES stay premises: `O`, `T`, `hA`, `MachineDefines` (parent, callees, leaf),
-- `MachineCloses` of the leaf.  `RealChildA` is a history of past synthesis results.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.QuadLeafGenericTest
open Tests.Compiler.SeqDeepGenDiffTest Tests.Compiler.TopShareInstTest Tools.ShippingQuadLeafGeneric
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA
open Tools.ShippingMachineEntry Tools.ShippingTopShareRun Tools.ShippingChildInv Tools.ShippingEntrySoundness
open Tools.ShippingMemCloses (ChildIfaceP)
open Sparkle.IR.Machine Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit Tools.ShippingSharedLeafNL
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildPinC Tools.ShippingChildDepthC

local notation "leafD" => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData

theorem acc_leafData : LeafData leafD :=
  ⟨Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok,
   Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body, by decide, by decide⟩

theorem wrap_calleeData : LeafCalleeData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData leafD
    wrapN accN 3 := by
  refine ⟨Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok, Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body,
    ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem wrap3_calleeData : LeafCalleeData wrap3.machineData leafD
    ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 accN 3 := by
  refine ⟨wrap3.machine_ok, wrap3.machine_body,
    ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem topshare_quadData : QuadParentData topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData
    wrap3.machineData ``Tests.Compiler.SeqDeepGenDiffTest.topshare wrapN ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 accN 3 := by
  refine ⟨topshare.machine_ok, topshare.machine_body, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

section
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- `CalleeOK` of `wrap` / `wrap3` from the generic `leafCallee_calleeOK` (compare `TopShareInstTest.wrap_calleeOK`, `wrap3_calleeOK`). -/
theorem wrap_calleeOK' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    CalleeOK O mctx cctx wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData :=
  leafCallee_calleeOK O T hA acc_leafData wrap_calleeData entry hR0
    (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _)

theorem wrap3_calleeOK' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    CalleeOK O mctx cctx ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData :=
  leafCallee_calleeOK O T hA acc_leafData wrap3_calleeData entry hR0
    (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _)

theorem wrap3_ifaceP' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.wrap3)
      (Tools.ShippingMachineEntry.machNIn wrap3.machineData.shape)
      (wrap3.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl accN] y.1 y.2 :=
  leafCallee_ifaceP O T hA acc_leafData wrap3_calleeData entry hR0
    (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) h

/-- `MachineClosesAtStart0` of `topshare` from the generic `quad_closes0` (compare `TopShareTraceTest.topshare_closes0`). -/
theorem topshare_closes0' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape :=
  quad_closes0 O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryW entryW3 hR0
    (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _)

theorem topshare_machineRun' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape m design :=
  quad_machineRun O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryT entryW entryW3 hR0
    (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hw hcore

/-- The parent's own run for `topshare` from the generic `quad_entry_run_ret_np` (the data-generic form of what `topshare_returned` feeds on). -/
theorem topshare_entry_run_ret_np' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape) topshare.machineData.shape.insts.length
        topshare.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? wrapN = some y₁ ∧ (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length) k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)  :=
  quad_entry_run_ret_np O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryT entryW entryW3 hR0
    (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hw h

end

/- statement equality of the re-derived theorems with the OLD hand-written ones (conclusions compared by `isDefEq`, default transparency). -/
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let pairs : List (Name × Name) := [
    (``wrap_calleeOK', ``wrap_calleeOK), (``wrap3_calleeOK', ``wrap3_calleeOK), (``wrap3_ifaceP', ``wrap3_ifaceP),
    (``topshare_closes0', ``Tests.Compiler.TopShareTraceTest.topshare_closes0),
    (``topshare_machineRun', ``Tests.Compiler.TopShareTraceTest.topshare_machineRun)]
  for (a, b) in pairs do
    let ta := (← getConstInfo a).type
    let tb := (← getConstInfo b).type
    -- both statements have the same binders (same order); compare the WHOLE types with the new binders substituted into the old
    forallTelescope ta fun xs ca => do
      let cb ← instantiateForall tb xs
      unless (← isDefEq ca cb) do
        throwError "SR13 statement audit: {a} differs from {b}\n{ca}\nvs\n{cb}"
      logInfo m!"statement of {a} ≡ statement of {b} ({xs.size} binders, same binder types)"

end Tests.Compiler.QuadLeafGenericTest

#print axioms Tests.Compiler.QuadLeafGenericTest.topshare_closes0'
#print axioms Tests.Compiler.QuadLeafGenericTest.topshare_machineRun'
#print axioms Tests.Compiler.QuadLeafGenericTest.wrap3_ifaceP'
