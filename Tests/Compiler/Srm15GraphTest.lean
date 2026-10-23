import Tests.Compiler.Srm12CorrTest
import Tools.ShippingSrm15Graph
-- UNBUILT (unit SRM15): no build run yet (see REPORT-SRM15.md).
-- SCOPE: `topshareM`/`topshareQ` re-stated through `ran_designCorr_of_graphOf` (Tools/ShippingSrm15Graph.lean).  This is NOT a new discharge of `hgraph`/`hname`: SRM12's `topshareM_corr`/`topshareQ_corr` already supply them.
-- Here `gM`/`gQ` are shown equal to `graphOf dsM`/`graphOf dsQ` (`rfl`), the `FirstOcc` conditions hold by `rfl`, and the per-kid fact is the kids' `ChildIfaceP` (`wrapM_ifaceP` etc., unchanged from SRM12).
-- `hkids` is supplied exactly as in SRM12 (`wrapM_childCorr` ...).  NOT claimed: an arbitrary graph, that `dsM`/`dsQ` list the right declarations beyond these two designs.
set_option autoImplicit false
namespace Tests.Compiler.Srm15GraphTest
open Lean Meta
open Tools.ShippingSrm7Rank Tools.ShippingSrm12Corr Tools.ShippingSrm15Graph Sparkle.Compiler.MachInstOrigin
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm7RankTest Tests.Compiler.Srm12CorrTest
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingMachineAuto
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

noncomputable def dsM : List (Name × MachineData) :=
  [(``topshareM, topshareM.machineData), (``wrapM, wrapM.machineData), (``wrapM3, wrapM3.machineData), (``leafM, leafM.machineData)]
noncomputable def dsQ : List (Name × MachineData) :=
  [(``topshareQ, topshareQ.machineData), (``wrapP, wrapP.machineData), (``wrapQ, wrapQ.machineData), (``leafP, leafP.machineData)]

theorem gM_eq_graphOf : gM = graphOf dsM := rfl
theorem gQ_eq_graphOf : gQ = graphOf dsQ := rfl

theorem dsM_top_first : FirstOcc dsM ``topshareM topshareM.machineData := rfl
theorem dsQ_top_first : FirstOcc dsQ ``topshareQ topshareQ.machineData := rfl

/-- `topshareM` through `ran_designCorr_of_graphOf` -/
theorem topshareM_corr15 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ModCorr (graphOf dsM) b ∧ ModCorr (graphOf dsM) (checkedOptimize b) ∧ DesignCorr (graphOf dsM) D.modules :=
  ran_designCorr_of_graphOf O dsM topshareM.machineData dsM_top_first topshareM_parentData.ok topshareM_parentData.body (nDecl := 4)
    topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne topshareM_outTy
    hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)
    (fun k hk y _ hre => by
      by_cases hk2 : k < 2
      · rw [topshareM_name k hk, if_pos hk2] at hre ⊢
        exact ⟨_, _, _, wrapM_ifaceP O T entryL entry₁ hre⟩
      · rw [topshareM_name k hk, if_neg hk2] at hre ⊢
        exact ⟨_, _, _, wrapM3_ifaceP O T entryL entry₂ hre⟩)
    (fun k hk _ => by
      by_cases hk2 : k < 2
      · rw [topshareM_name k hk, if_pos hk2]; exact wrapM_childCorr O T entryL entry₁
      · rw [topshareM_name k hk, if_neg hk2]; exact wrapM3_childCorr O T entryL entry₂)

/-- `topshareQ` through `ran_designCorr_of_graphOf` -/
theorem topshareQ_corr15 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ModCorr (graphOf dsQ) b ∧ ModCorr (graphOf dsQ) (checkedOptimize b) ∧ DesignCorr (graphOf dsQ) D.modules :=
  ran_designCorr_of_graphOf O dsQ topshareQ.machineData dsQ_top_first topshareQ_parentData.ok topshareQ_parentData.body (nDecl := 4)
    topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne topshareQ_outTy
    hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)
    (fun k hk y _ hre => by
      by_cases hk2 : k < 2
      · rw [topshareQ_name k hk, if_pos hk2] at hre ⊢
        exact ⟨_, _, _, wrapP_ifaceP O T hR0 hcl entry₁ hre⟩
      · rw [topshareQ_name k hk, if_neg hk2] at hre ⊢
        exact ⟨_, _, _, wrapQ_ifaceP O T hR0 hcl entry₂ hre⟩)
    (fun k hk _ => by
      by_cases hk2 : k < 2
      · rw [topshareQ_name k hk, if_pos hk2]; exact wrapP_childCorr O T hR0 hcl entry₁
      · rw [topshareQ_name k hk, if_neg hk2]; exact wrapQ_childCorr O T hR0 hcl entry₂)

end Tests.Compiler.Srm15GraphTest
