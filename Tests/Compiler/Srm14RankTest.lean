import Tests.Compiler.Srm11ParentTest
import Tests.Compiler.Srm7RankTest
set_option autoImplicit false
-- BUILT/UNBUILT: see REPORT-SRM14.md (dev runs and the final-SHA rebuild are recorded there).
-- SCOPE (unit SRM14): the SRM11 instance theorems `topshare{M,Q}_svBoundsH` / `topshare{M,Q}_designSVH_noB` with the rank table `rk` set to the COMPUTED table `rkOf gM 4` / `rkOf gQ 3` of SRM7
-- and the five rank binders (`rk`, `hrkmem`, `hrT`, `hrW`/`hrP`, `hrW3`/`hrQ`, `hrL`) REMOVED: each is PROVED from SRM7 (`rkOf_mem`, `rkOf_decl`, the decided ranks `gM_*`/`gQ_*`), exactly as SRM7's
-- `topshare*_hcheck_computed` does for SRM5.  The corollaries CALL the SRM11 theorems; they do not restate them.
-- SRM12 is NOT used: the SRM11 instance theorems have no per-instance rank binder (no `hkidH`; `hkidH` is internal to `topshare*_hcheck`, proved there by SRM5's `*_kidHeight`).  The graphs `gM`/`gQ` are READ from
-- `machineData.shape.instTagged` of the generated declarations (SRM7); no graph provenance beyond SRM7 is added.
-- PREMISES kept (unchanged, in particular owned by SRM13): `hrun`, `hseedB`, `hst`, `hkids`, and every machine/compiler premise (`O T hA entry* hcore hpost hw`).
-- NOT claimed: that `hseedB`/`hst`/`hkids` hold; that a rank table exists for any other design; the endpoint.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.Srm14RankTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingHierStateG (KT KSn KState runModuleTG)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingDesignSVBounds (InvN)
open Sparkle.IR.Semantics (Bounded)
open Tools.ShippingSrm7Rank Tests.Compiler.Srm7RankTest
open Tests.Compiler.SharedLeafMemKidIfaceTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- `topshareM_svBoundsH` with the rank table COMPUTED (`rkOf gM 4`): no rank binder remains. -/
theorem topshareM_svBoundsH_computed (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 2 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) seed T' s envs :=
  topshareM_svBoundsH O T hA entryL entry₁ entry₂ entry hcore hpost hw (rkOf gM 4) (rkOf_mem gM 4)
    (by rw [rkOf_decl, gM_top]) (by rw [rkOf_decl, gM_wrap]) (by rw [rkOf_decl, gM_wrap3]) (by rw [rkOf_decl, gM_leaf])
    seed T' s envs hrun hseedB hst hkids

/-- `topshareQ_svBoundsH` with the rank table COMPUTED (`rkOf gQ 3`). -/
theorem topshareQ_svBoundsH_computed (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 1 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) seed T' s envs :=
  topshareQ_svBoundsH O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw (rkOf gQ 3) (rkOf_mem gQ 3)
    (by rw [rkOf_decl, gQ_top]) (by rw [rkOf_decl, gQ_wrapP]) (by rw [rkOf_decl, gQ_wrapQ]) (by rw [rkOf_decl, gQ_leaf])
    seed T' s envs hrun hseedB hst hkids

/-- `topshareM_designSVH_noB` with the rank table COMPUTED. -/
theorem topshareM_designSVH_noB_computed (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 2 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) seed T' s envs :=
  topshareM_designSVH_noB O T hA entryL entry₁ entry₂ entry hcore hpost hw (rkOf gM 4) (rkOf_mem gM 4)
    (by rw [rkOf_decl, gM_top]) (by rw [rkOf_decl, gM_wrap]) (by rw [rkOf_decl, gM_wrap3]) (by rw [rkOf_decl, gM_leaf])
    seed T' s envs hrun hseedB hst hkids

/-- `topshareQ_designSVH_noB` with the rank table COMPUTED. -/
theorem topshareQ_designSVH_noB_computed (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 1 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) seed T' s envs :=
  topshareQ_designSVH_noB O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw (rkOf gQ 3) (rkOf_mem gQ 3)
    (by rw [rkOf_decl, gQ_top]) (by rw [rkOf_decl, gQ_wrapP]) (by rw [rkOf_decl, gQ_wrapQ]) (by rw [rkOf_decl, gQ_leaf])
    seed T' s envs hrun hseedB hst hkids

end Tests.Compiler.Srm14RankTest

#print axioms Tests.Compiler.Srm14RankTest.topshareM_svBoundsH_computed
#print axioms Tests.Compiler.Srm14RankTest.topshareQ_svBoundsH_computed
#print axioms Tests.Compiler.Srm14RankTest.topshareM_designSVH_noB_computed
#print axioms Tests.Compiler.Srm14RankTest.topshareQ_designSVH_noB_computed
