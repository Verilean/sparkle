import Tests.Compiler.Srm4CalleeTest
import Tools.ShippingSrm4Parent
import Tools.ShippingQuadCalls
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (residue R5, parent half): the parent soundness blocks of the shared-leaf class HAND-APPLIED to `topshareM` (two calls of `wrapM`, two of `wrapM3`, both callees over the memory-bearing leaf `leafM`; `Tests/Compiler/SharedLeafMemKidTest.lean`):
-- `ranA`, `hkid` (`KidFactsNC` of both callees, `Tests/Compiler/Srm4KidTest.lean`), `runFacts`, `outsCheck`, `kidsMasked`, `traceXA`, and `designCheck` UP TO the children's check `hkids` (the named premise: OPEN, `Tools/ShippingSrm4Check.lean`).
-- PREMISES kept (named): `O`, `T`, `hA`, the `MachineDefines` of the four machines, the start world `JQC O 0 w`, the core run `hcore`; `hkids` for `designCheck`.  `RealChildA` is a history of past synthesis results.
-- No `sorry`, no `axiom`, no `native_decide`.
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
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem wrapM3_allord : ∀ k (hk : k < wrapM3.machineData.shape.insts.length), (originAt wrapM3.machineData.shape k).child? = none := by
  first | decide | decide +kernel
theorem wrapM3_outsClean : ∀ o ∈ wrapM3.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem wrapM3_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) :
    KidFactsNC O ``wrapM3 wrapM3.machineData.shape.layout.outs (argWidths wrapM3.machineData 4) :=
  memCallee_kidFactsNC O T wrapM3_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM3_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun _ => leafM.machineData.shape.layout.outs) (fun _ => argWidths leafM.machineData 4)
    (fun k hk cb aw dw h => by rw [wrapM3_allord k hk] at h; cases h)
    (fun k hk _ => by rw [wrapM3_kids k hk]; exact leafM_kidFactsNC O T entryL)
    (by first | decide | decide +kernel) (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapM3_outsClean o ho))
    (by first | decide | decide +kernel) entry

/-! ## `topshareM` -/

theorem topshareM_callees : topshareM.machineData.shape.insts.map (·.1) = [``wrapM, ``wrapM, ``wrapM3, ``wrapM3] := by
  first | decide | decide +kernel
theorem topshareM_len : topshareM.machineData.shape.insts.length = 4 := by decide

/-- the callee's output fields and argument widths at call `k` (calls 0, 1: `wrapM`; 2, 3: `wrapM3`) -/
noncomputable def tmOuts : Nat → List OutField := fun k => if k < 2 then wrapM.machineData.shape.layout.outs else wrapM3.machineData.shape.layout.outs
noncomputable def tmIns : Nat → List Nat := fun k => if k < 2 then argWidths wrapM.machineData 4 else argWidths wrapM3.machineData 4

theorem topshareM_nomem : ∀ x ∈ topshareM.machineData.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true := by
  first | decide | decide +kernel
theorem topshareM_insts_ne : topshareM.machineData.shape.insts ≠ [] := by decide
theorem topshareM_slotsNe : topshareM.machineData.shape.layout.slots ≠ [] := by decide
theorem topshareM_fne : topshareM.machineData.shape.instFields ≠ [] := by decide
theorem topshareM_outTy : ∀ o ∈ topshareM.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel
theorem topshareM_outsClean : ∀ o ∈ topshareM.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel
theorem topshareM_scalar : ∀ o ∈ topshareM.machineData.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel
theorem topshareM_cw : Tools.ShippingCallWidths.callWidthsOk topshareM.machineData 4 tmOuts = true := by
  first | decide | decide +kernel
theorem topshareM_ca : Tools.ShippingPortsMatchRaw.callArgsOk topshareM.machineData 4 tmIns = true := by
  first | decide | decide +kernel

theorem topshareM_name : ∀ (k : Nat) (hk : k < topshareM.machineData.shape.insts.length),
    (topshareM.machineData.shape.insts[k]).1 = (if k < 2 then ``wrapM else ``wrapM3) := by
  first | decide | decide +kernel

/-- **`KidFactsNC` of every call entry's callee of `topshareM`** (`ts_hkid` for the memory-leaf class) -/
theorem topshareM_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) :
    ∀ (k : Nat) (hk : k < topshareM.machineData.shape.insts.length),
      KidFactsNC O (topshareM.machineData.shape.insts[k]).1 (tmOuts k) (tmIns k) := by
  intro k hk
  rw [topshareM_name k hk]
  unfold tmOuts tmIns
  split
  · exact wrapM_kidFactsNC O T entryL entry₁
  · exact wrapM3_kidFactsNC O T entryL entry₂

theorem topshareM_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``topshareM topshareM.machineData.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (topshareM_closes0_derived O T hA entryL entry₁ entry₂) hw

/-! ## the parent's run facts -/

open Tests.Compiler.SharedLeafMemKidEntryTest in
theorem topshareM_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  kidsNC_runFacts O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body (nDecl := 4) topshareM_parentData.callsOk
    topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_slotsNe topshareM_fne topshareM_outTy topshareM_nomem
    tmOuts tmIns (topshareM_hkid O T entryL entry₁ entry₂) topshareM_cw hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)

open Tests.Compiler.SharedLeafMemKidEntryTest in
theorem topshareM_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (m : Nat)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  kidsNC_outsCheck O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body (nDecl := 4) topshareM_parentData.callsOk
    topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy topshareM_nomem
    tmOuts tmIns (m + 1) (topshareM_hkid O T entryL entry₁ entry₂) hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)
    (topshareM_runFacts O T hA entryL entry₁ entry₂ entry hcore hpost hw).gate

open Tests.Compiler.SharedLeafMemKidEntryTest in
theorem topshareM_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  kidsNC_maskedN O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body (nDecl := 4) topshareM_parentData.callsOk
    topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne topshareM_outTy topshareM_nomem
    tmOuts tmIns (topshareM_hkid O T entryL entry₁ entry₂) hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)

open Tests.Compiler.SharedLeafMemKidEntryTest in
/-- **`designCheck` of `topshareM` UP TO the children's check**: everything but `hkids` is derived; `hkids` is the named OPEN premise. -/
theorem topshareM_designCheck_of_kidsPass (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (m : Nat)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) (m + 1)) (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  kidsNC_designCheck_of_kidsPass O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body (nDecl := 4) topshareM_parentData.callsOk
    topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_slotsNe topshareM_fne topshareM_outTy topshareM_nomem
    tmOuts tmIns (m + 1) (topshareM_hkid O T entryL entry₁ entry₂) topshareM_cw topshareM_ca hpost
    (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareM_outsClean o ho)) topshareM_scalar hkids

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM3_kidFactsNC
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hkid
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_ranA
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_runFacts
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_outsCheck
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_kidsMasked
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designCheck_of_kidsPass
