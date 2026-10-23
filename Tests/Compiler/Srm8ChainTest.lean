import Tests.Compiler.Srm5ParentTest
import Tests.Compiler.Srm5ParentQTest
import Tools.ShippingSrm8Bridge
-- UNBUILT (unit SRM8): see STATUS-SRM8.md.
-- SCOPE: `HeightPass` (the hypothesis shape of `Tools.ShippingSrm8Bridge.design_at_free_h`) for the two memory-bearing instances `topshareM` (rank 3, depth n = 2) and `topshareQ` (rank 2, depth n = 1),
-- PROVED from `topshareM_hcheck` / `topshareQ_hcheck` (SRM5) plus the rank equation of the shipped module that SRM5 derived INSIDE those proofs (`hrb`) and did not export.  Same premises as the SRM5 theorems (rank table `rk`
-- and its equations stay premises; instance-specific, no general rank supply).  Nothing here proves `HeightBridge`.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingMemKid (memOuts memIns)
open Tools.ShippingMachineAuto
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm5Deep Tools.ShippingMemCloses Tools.ShippingSrm8Bridge

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

open Tests.Compiler.SharedLeafMemKidEntryTest in
/-- `HeightPass` of the shipped module of `topshareM` at depth 2 and fuel `f + 3` (premises of `topshareM_hcheck`, unchanged). -/
theorem topshareM_heightPass (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (rk : String → Option Nat)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrT : rk (Sparkle.IR.ModuleName.ofDecl ``topshareM) = some (2 + 1))
    (hrW : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM) = some (1 + 1))
    (hrW3 : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM3) = some (1 + 1))
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1) : 
    HeightPass (childMap D.modules) rk 2 (f + 3) (checkedOptimize b) := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy
    topshareM_nomem hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (2 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  exact ⟨⟨3, hrb, by omega, by omega⟩, topshareM_hcheck O T hA f entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL⟩

open Tests.Compiler.SharedLeafMemKidEntryTest in
/-- `HeightPass` of the shipped module of `topshareQ` at depth 1 and fuel `f + 2` (premises of `topshareQ_hcheck`, unchanged). -/
theorem topshareQ_heightPass (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (rk : String → Option Nat)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrT : rk (Sparkle.IR.ModuleName.ofDecl ``topshareQ) = some (1 + 1))
    (hrP : rk (Sparkle.IR.ModuleName.ofDecl ``wrapP) = some (0 + 1))
    (hrQ : rk (Sparkle.IR.ModuleName.ofDecl ``wrapQ) = some (0 + 1))
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0) : 
    HeightPass (childMap D.modules) rk 1 (f + 2) (checkedOptimize b) := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy
    topshareQ_nomem hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (1 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  exact ⟨⟨2, hrb, by omega, by omega⟩, topshareQ_hcheck O T hA f hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL⟩

end Tests.Compiler.SharedLeafMemKidIfaceTest
