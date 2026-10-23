import Tests.Compiler.Srm6ParentTest
import Tools.ShippingSrm11Bounds
set_option autoImplicit false
-- UNBUILT (unit SRM11): see STATUS-SRM11.md for run names; the final-SHA rebuild is in REPORT-SRM11.md.
-- SCOPE: the width premise `hB : SVBoundsH …` of SRM6's `topshareM_designSVH` / `topshareQ_designSVH`, PROVED from `Tools.ShippingSrm11Bounds.svBoundsH_of_checks` (the `hcheck` analogue of `svBounds_of_checks`)
-- with `topshare*_hcheck`.  The hypothesis `hB` is REPLACED (not discharged) by the machine-side width facts of the uniform chain: `hseedB` (the top seeding maps bounded states to bounded environments),
-- `hst` (bounded start state) and `hkids` (`InvN` of every instance's state at the shipped module's instance statements).  All other premises are those of `topshare*_designSVH`.
-- NOT claimed: that `hseedB`/`hst`/`hkids` hold for the machine's run (they are what `Reset`/the top inputs must supply); the endpoint.  No `sorry`, no `axiom`, no `native_decide`.
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
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingSrm5Deep (post_name)
open Tools.ShippingHierStateG (KT KSn KState runModuleTG)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingDesignSV (envAt)
open Tools.ShippingDesignSVBounds (InvN)
open Sparkle.IR.Semantics (Bounded)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`SVBoundsH` for `topshareM`**, from `topshareM_hcheck` and `svBoundsH_of_checks`. -/
theorem topshareM_svBoundsH (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 2 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) seed T' s envs := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy
    topshareM_nomem hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (2 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  exact svBoundsH_of_checks D.modules rk 2 (checkedOptimize b) seed T' s envs (0 + 3) 3 hrb (by omega)
    (topshareM_hcheck O T hA 0 entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL) hseedB hst hkids hrun

/-- **`SVBoundsH` for `topshareQ`**. -/
theorem topshareQ_svBoundsH (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 1 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) seed T' s envs := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy
    topshareQ_nomem hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (1 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  exact svBoundsH_of_checks D.modules rk 1 (checkedOptimize b) seed T' s envs (0 + 2) 2 hrb (by omega)
    (topshareQ_hcheck O T hA 0 hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL) hseedB hst hkids hrun

/-- **The semantic conclusion for `topshareM` WITHOUT the `hB` binder**: `topshareM_designSVH` with `hB` supplied by `topshareM_svBoundsH`.  Remaining run-level premises: `hrun`, `hseedB`, `hst`, `hkids`. -/
theorem topshareM_designSVH_noB (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 2 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) seed T' s envs :=
  topshareM_designSVH O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL seed T' s envs hrun
    (topshareM_svBoundsH O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL seed T' s envs hrun hseedB hst hkids)

/-- **The semantic conclusion for `topshareQ` WITHOUT the `hB` binder.** -/
theorem topshareQ_designSVH_noB (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 1 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) seed T' s envs :=
  topshareQ_designSVH O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL seed T' s envs hrun
    (topshareQ_svBoundsH O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL seed T' s envs hrun hseedB hst hkids)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tools.ShippingSrm11Bounds.svBoundsH_of_checks
#print axioms Tools.ShippingSrm11Bounds.svBoundsH_of_svBounds
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_noB
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_noB
