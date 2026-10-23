import Tests.Compiler.Srm5ParentQTest
import Tools.ShippingSrm6Sem
set_option autoImplicit false
-- BUILT (unit SRM6): m12 exit 0 (dev); final-SHA rebuild in REPORT-SRM6.md.
-- SCOPE: the SEMANTIC conclusion `DesignSVH` (the closed run of the emitted texts, `Tools/ShippingSrm6Sem.lean`) for the two instances of SRM5, from `topshareM_hcheck` / `topshareQ_hcheck` and `design_sv_runH`.
-- PROVED here: `topshareM_designSVH` (rank 3, stateful run at depth 2) and `topshareQ_designSVH` (rank 2, depth 1).
-- PREMISES kept (named): all those of `topshareM_hcheck` / `topshareQ_hcheck` (rank table `rk` with `hrkmem`, `hrT`..; `O`, `T`, `hA`, machine definitions, `hcore`, `hw`, `hpost`), PLUS the IR run `hrun` of the shipped module at depth 2 / 1 from a state `s` and the width premises `hB : SVBoundsH` (run-level premises, as `SVBounds` in `design_sv_runN`).
-- NOT claimed: that `hrun`/`hB` hold for the machine's actual run (the machine-side links `Reset`/`InvN`/`svBounds_of_checks` are not restated over `hcheck`), the endpoint `machine_design_svH_full`, any other class.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem
open Tools.ShippingSrm5Deep (post_name)
open Tools.ShippingHierStateG (KT KSn KState runModuleTG)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingDesignSV (envAt)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The semantic conclusion for `topshareM`, over `hcheck`**: `topshareM_hcheck` (the children's check by the rank table) composed with `design_sv_runH`: along the IR linked run of the shipped module at depth 2 (children `KT 2`, ranks `topshareM` 3, `wrapM`/`wrapM3` 2, `leafM` 1, memory 0) the emitted texts of the module and of all its descendants run to the same environments (`DesignSVH`). -/
theorem topshareM_designSVH (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hB : SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) seed T' s envs) :
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) seed T' s envs := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy
    topshareM_nomem hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (2 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  exact design_sv_runH D.modules rk 2 (checkedOptimize b) seed T' s envs 3 3 hrb (by omega)
    (topshareM_hcheck O T hA 0 entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL) hrun hB

/-- **The semantic conclusion for `topshareQ`, over `hcheck`** (ranks `topshareQ` 2, `wrapP`/`wrapQ` 1, `leafP` 0; stateful run at depth 1). -/
theorem topshareQ_designSVH (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hB : SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) seed T' s envs) :
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) seed T' s envs := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy
    topshareQ_nomem hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (1 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  exact design_sv_runH D.modules rk 1 (checkedOptimize b) seed T' s envs 2 2 hrb (by omega)
    (topshareQ_hcheck O T hA 0 hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL) hrun hB

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tools.ShippingSrm6Sem.design_sv_runH
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH
