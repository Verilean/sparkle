import Tests.Compiler.Srm18ParentTest
import Tests.Compiler.Srm14RankTest
set_option autoImplicit false
-- BUILT (unit SRM19): dev run s1 (exit 0); the final-SHA rebuild in REPORT-SRM19.md is the only final evidence.
-- SCOPE: ONE scoped composed statement per instance (`topshare{M,Q}_svBoundsH_endToEnd`; conclusion = the SRM11 `SVBoundsH` at the start state `⟨st0, mems, kids⟩`, NOT the `designSVH` form).
-- It is SRM18's `_viaStartNk` (which calls SRM16's `_viaResetO`, which uses SRM16's `_hO`) with the rank table set to SRM7's `rkOf gM 4` / `rkOf gQ 3` and the six rank binders (rk hrkmem hrT hrW hrW3 hrL) filled by the SAME SRM7 proofs
-- (`rkOf_mem`, `rkOf_decl`, `gM_*`/`gQ_*`) that SRM14's `_computed` corollaries use.  The SRM14 `_computed` theorems themselves are NOT in the closure: they are SRM11-shaped (hseedB/hst/hkids over a generic `seed`), the
-- viaStartNk statement is SRM13/16-shaped (`seedIn b ins`, hin, RegsAtInit...); only the rank binders coincide (identical types), so only the rank facts are shared.
-- ONE run / witness: `raw b D hcore hpost ins T' st0 mems kids envs hrun` occur once and flow into every component.
-- PREMISES (explicit, NOT derived): machine (O T hA entry* hcore hpost hw), hrun, hin, hst₁ RegsAtInit, hst₂ RegsFit, hst₃ NonRegBounded, hRK : ResetNk, hfit (FitTree).  Nothing says the run starts at reset.
-- No `sorry`, no `axiom`, no `native_decide`.
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
open Tools.ShippingSrm13Supply
open Tools.ShippingSeqOptSoundness (seedIn)


open Tools.ShippingSrm7Rank Tests.Compiler.Srm7RankTest
open Tests.Compiler.SharedLeafMemKidIfaceTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem topshareM_svBoundsH_endToEnd (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (ins : Nat → String → Nat)
    (T' : Nat)
    (st0 : String → Nat) (mems : Sparkle.IR.Semantics.MEnv) (kids : String → KT 2)
    (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 2)) = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) st0)
    (hst₂ : RegsFit (checkedOptimize b))
    (hst₃ : NonRegBounded (checkedOptimize b) st0)
    (hRK : Tools.ShippingMachineShipsDepth.ResetNk 2 raw D kids)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (kids iname)) :
    SVBoundsH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 2)) envs :=
  topshareM_svBoundsH_viaStartNk O T hA entryL entry₁ entry₂ entry hcore hpost hw (rkOf gM 4) (rkOf_mem gM 4)
    (by rw [rkOf_decl, gM_top]) (by rw [rkOf_decl, gM_wrap]) (by rw [rkOf_decl, gM_wrap3]) (by rw [rkOf_decl, gM_leaf])
    ins T' st0 mems kids envs hrun hin hst₁ hst₂ hst₃ hRK hfit

theorem topshareQ_svBoundsH_endToEnd (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (ins : Nat → String → Nat)
    (T' : Nat)
    (st0 : String → Nat) (mems : Sparkle.IR.Semantics.MEnv) (kids : String → KT 1)
    (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 1)) = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) st0)
    (hst₂ : RegsFit (checkedOptimize b))
    (hst₃ : NonRegBounded (checkedOptimize b) st0)
    (hRK : Tools.ShippingMachineShipsDepth.ResetNk 1 raw D kids)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (kids iname)) :
    SVBoundsH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 1)) envs :=
  topshareQ_svBoundsH_viaStartNk O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw (rkOf gQ 3) (rkOf_mem gQ 3)
    (by rw [rkOf_decl, gQ_top]) (by rw [rkOf_decl, gQ_wrapP]) (by rw [rkOf_decl, gQ_wrapQ]) (by rw [rkOf_decl, gQ_leaf])
    ins T' st0 mems kids envs hrun hin hst₁ hst₂ hst₃ hRK hfit

end Tests.Compiler.SharedLeafMemKidIfaceTest
