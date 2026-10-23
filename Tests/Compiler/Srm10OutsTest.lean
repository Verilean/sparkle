import Tests.Compiler.Srm5ParentQTest
import Tools.ShippingSrm10Outs
-- BUILT (unit SRM10): s10b2 exit 0 (dev run, default heartbeats, no heartbeat option); the final-SHA rebuild is in REPORT-SRM10.md.
-- SCOPE (instance-specific, topshareM and topshareQ ONLY): `Tools/ShippingSrm10Outs.lean` link B applied to SRM5's `topshareM_hcheck` / `topshareQ_hcheck` under the CONCRETE rank tables `rkM` / `rkQ`
-- (their rank premises are discharged by `rkM_*` / `rkQ_*`) and SRM4's `topshareM_outsCheck` / `topshareQ_outsCheck`: the height-indexed output check `houtsCheck` of the printed parent module.
-- PREMISES kept (named, the same as SRM4/SRM5): `O`, `T`, `hA`, the `MachineDefines` of the machines, `hcore`, `hpost`, `hw`.  NOTE (honest scope): the instance proof USES the uniform `outsCheck` of SRM4 at every depth `m+1`;
-- it shows the height-indexed form is implied there, it does not derive the output facts without the uniform one.  Not claimed: any other class, `design_sv_backN` restated at heights (SRM6), a general rank supply (SRM7).
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tools.ShippingMachineAuto
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm10Outs

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`houtsCheck` of `topshareM` (rank 3) under `rkM`**: the kids (`wrapM`, `wrapM3` at rank 2, their `leafM` kids at rank 1, the memory modules at rank 0) pass `houtsMod`. -/
theorem topshareM_houts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    houtsCheck (childMap D.modules) rkM (f + 2) 2 (checkedOptimize b) = true := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy
    topshareM_nomem hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)).1
  have hrb : rkM (checkedOptimize b).name = some (2 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, Tools.ShippingSrm5Deep.post_name hpost, hMn]; exact rkM_top
  exact houtsCheck_of_outsCheck_hcheck hrb
    (topshareM_hcheck O T hA f entryL entry₁ entry₂ entry hcore hpost hw rkM rkM_mem rkM_top rkM_wrap rkM_wrap3 rkM_leaf)
    (fun m => topshareM_outsCheck O T hA m entryL entry₁ entry₂ entry hcore hpost hw)

/-- **`houtsCheck` of `topshareQ` (rank 2) under `rkQ`**: the kids (`wrapP`, `wrapQ` at rank 1, `leafP` and the memory module at rank 0). -/
theorem topshareQ_houts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    houtsCheck (childMap D.modules) rkQ (f + 1) 1 (checkedOptimize b) = true := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy
    topshareQ_nomem hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)).1
  have hrb : rkQ (checkedOptimize b).name = some (1 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, Tools.ShippingSrm5Deep.post_name hpost, hMn]; exact rkQ_top
  exact houtsCheck_of_outsCheck_hcheck hrb
    (topshareQ_hcheck O T hA f hR0 hcl entry₁ entry₂ entry hcore hpost hw rkQ rkQ_mem rkQ_top rkQ_wrapP rkQ_wrapQ rkQ_leaf)
    (fun m => topshareQ_outsCheck O T hA m hR0 hcl entry₁ entry₂ entry hcore hpost hw)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_houts
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_houts
