import Tests.Compiler.Srm4KidTest
import Tools.ShippingSrm4Parent
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (residue R5, parent half): the parent soundness blocks HAND-APPLIED to `topshareQ` (two calls of the PLAIN callee `wrapP` over the plain leaf `leafP`, two calls of `wrapQ`, whose calls are two of `leafP` and ONE memory entry;
-- `Tests/Compiler/SharedLeafMemKidTest.lean`): `ranA`, `hkid` (`KidFactsNC`: `wrapP` from `leafCallee_kidFactsA` minus `check`, `wrapQ` from `Tests/Compiler/Srm4KidTest.lean`), `runFacts`, `outsCheck`, `kidsMasked`, `traceXA`, and
-- `designCheck` UP TO the children's check `hkids` (named, OPEN).  NOT done here: the composed theorem of `topshareQ` (the callee `wrapQ` mixes a plain-leaf call and a memory call: OPEN, see REPORT-SRM4.md).
-- PREMISES kept (named): `O`, `T`, `hA`, `MachineDefines` of the machines, `MachineCloses` of the plain leaf, the start world, `hcore`; `hkids`.  An example does not make the class complete.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingQuadComposed (GenFacts genTrace)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingInstTagged (originAt)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem wrapP_extra : Tools.ShippingQuadComposed.LeafCalleeExtra wrapP.machineData leafP.machineData 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel

theorem wrapP_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) :
    KidFactsNC O ``wrapP wrapP.machineData.shape.layout.outs (argWidths wrapP.machineData 3) :=
  KidFactsA.toNC (Tools.ShippingQuadComposed.leafCallee_kidFactsA O T leafP_data leafP_kidData wrapP_calleeData wrapP_extra entry hR0 hcl 0)

theorem topshareQ_callees' : topshareQ.machineData.shape.insts.map (·.1) = [``wrapP, ``wrapP, ``wrapQ, ``wrapQ] := by
  first | decide | decide +kernel
theorem topshareQ_len : topshareQ.machineData.shape.insts.length = 4 := by decide

noncomputable def tqOuts : Nat → List OutField := fun k => if k < 2 then wrapP.machineData.shape.layout.outs else wrapQ.machineData.shape.layout.outs
noncomputable def tqIns : Nat → List Nat := fun k => if k < 2 then argWidths wrapP.machineData 3 else argWidths wrapQ.machineData 5

theorem topshareQ_nomem : ∀ x ∈ topshareQ.machineData.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true := by
  first | decide | decide +kernel
theorem topshareQ_insts_ne : topshareQ.machineData.shape.insts ≠ [] := by decide
theorem topshareQ_slotsNe : topshareQ.machineData.shape.layout.slots ≠ [] := by decide
theorem topshareQ_fne : topshareQ.machineData.shape.instFields ≠ [] := by decide
theorem topshareQ_outTy : ∀ o ∈ topshareQ.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by first | decide | decide +kernel
theorem topshareQ_outsClean : ∀ o ∈ topshareQ.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel
theorem topshareQ_scalar : ∀ o ∈ topshareQ.machineData.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true := by first | decide | decide +kernel
theorem topshareQ_cw : Tools.ShippingCallWidths.callWidthsOk topshareQ.machineData 4 tqOuts = true := by first | decide | decide +kernel
theorem topshareQ_ca : Tools.ShippingPortsMatchRaw.callArgsOk topshareQ.machineData 4 tqIns = true := by first | decide | decide +kernel
theorem topshareQ_name : ∀ (k : Nat) (hk : k < topshareQ.machineData.shape.insts.length),
    (topshareQ.machineData.shape.insts[k]).1 = (if k < 2 then ``wrapP else ``wrapQ) := by
  first | decide | decide +kernel

/-- **`KidFactsNC` of every call entry's callee of `topshareQ`** -/
theorem topshareQ_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) :
    ∀ (k : Nat) (hk : k < topshareQ.machineData.shape.insts.length),
      KidFactsNC O (topshareQ.machineData.shape.insts[k]).1 (tqOuts k) (tqIns k) := by
  intro k hk
  rw [topshareQ_name k hk]
  unfold tqOuts tqIns
  split
  · exact wrapP_kidFactsNC O T hR0 hcl entry₁
  · exact wrapQ_kidFactsNC O T hR0 hcl entry₂

theorem topshareQ_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``topshareQ topshareQ.machineData.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (topshareQ_closes0_derived O T hA hR0 hcl entry₁ entry₂) hw

theorem topshareQ_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  kidsNC_runFacts O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body (nDecl := 4) topshareQ_parentData.callsOk
    topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_slotsNe topshareQ_fne topshareQ_outTy topshareQ_nomem
    tqOuts tqIns (topshareQ_hkid O T hR0 hcl entry₁ entry₂) topshareQ_cw hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)

theorem topshareQ_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (m : Nat)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  kidsNC_outsCheck O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body (nDecl := 4) topshareQ_parentData.callsOk
    topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy topshareQ_nomem
    tqOuts tqIns (m + 1) (topshareQ_hkid O T hR0 hcl entry₁ entry₂) hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)
    (topshareQ_runFacts O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw).gate

theorem topshareQ_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  kidsNC_maskedN O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body (nDecl := 4) topshareQ_parentData.callsOk
    topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne topshareQ_outTy topshareQ_nomem
    tqOuts tqIns (topshareQ_hkid O T hR0 hcl entry₁ entry₂) hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)

/-- **`designCheck` of `topshareQ` UP TO the children's check** (`hkids` named, OPEN; for `topshareQ` the matching depth is 1: the memory module of `wrapQ` sits at `kidCheck 0`). -/
theorem topshareQ_designCheck_of_kidsPass (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (m : Nat)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) m) (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) m (checkedOptimize b) = true :=
  kidsNC_designCheck_of_kidsPass O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body (nDecl := 4) topshareQ_parentData.callsOk
    topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_slotsNe topshareQ_fne topshareQ_outTy topshareQ_nomem
    tqOuts tqIns m (topshareQ_hkid O T hR0 hcl entry₁ entry₂) topshareQ_cw topshareQ_ca hpost
    (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareQ_outsClean o ho)) topshareQ_scalar hkids

noncomputable instance topshareQ_inhab : Inhabited (HList (tys topshareQ.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem topshareQ_gen : GenFacts topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits topshareQ.machineBody
    topshareQ.machineResult topshareQ.machineExt topshareQ.machineExtB topshareQ.machineSource :=
  ⟨topshareQ.machine_ok, topshareQ.machine_body, topshareQ.machine_inits, topshareQ.machine_writes, topshareQ.machine_result, topshareQ.machine_source,
   fun i bools bits S S' t h =>
    topshareQ.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

/-- **The trace of `topshareQ`**: `genTrace` at the parent's `MachineRunJQC` (`topshareQ_machineRun_derived`). -/
theorem topshareQ_traceXA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingServedRealA.ServedRealA O ``topshareQ topshareQ.machineData.shape m design) ``topshareQ topshareQ.machineData m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineSource
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits
        topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB) :=
  genTrace O T hA topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ_gen (D₀ := 0)
    (topshareQ_machineRun_derived O T hA hR0 hcl entry₁ entry₂ entryP hw hcore)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hkid
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_runFacts
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_outsCheck
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_kidsMasked
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designCheck_of_kidsPass
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_traceXA
