import Tests.Compiler.Srm17ParentTest
import Tools.ShippingSrm18Start
set_option autoImplicit false
-- BUILT (unit SRM18): dev run a7 (exit 0); the final-SHA rebuild in REPORT-SRM18.md is the only final evidence.
-- SCOPE: the start-state premise `hsk : s.kids = resetKids D n raw` of the SRM17 `_viaResetSrc` corollaries.
-- * `topshare{M,Q}_hsk_not_forced` (PROVED, `bumpedStart_spec`): for EVERY state `s` with the instance theorems' `hrun`, an explicit state with the same registers/memories and the same run result, `ResetNk` kids whenever `s` has,
--   and kids `≠ resetKids D n raw`.  So the run proposition (nor run proposition + `ResetNk`) does not imply `hsk`; no derivation of `hsk` from it exists, and none is claimed.
-- * `topshare{M,Q}_{svBoundsH,designSVH}_viaStartNk` (PROVED, calls SRM16's `_viaResetO`, statement of that theorem unchanged): the start state in the SHAPE the composed statements quantify (`⟨st0, mems, kids⟩`, `ComposedG`'s start),
--   with `hsk` REPLACED by `hRK : ResetNk n raw D kids` (the `Reset` parameter of `ComposedG`/`ComposedGW`, a Prop on instance names only; it is NOT defeq to `hsk`).  A replacement, not a discharge:
--   `hRK`, `hin`, `RegsAtInit`/`RegsFit`/`NonRegBounded` (on `st0`), `FitTree` stay explicit PREMISES; nothing says the run starts at `resetKids`.
-- `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`.
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

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
open Tools.ShippingSrm18Start

/-- **`hsk` is not forced by the instance theorems' run proposition (`topshareM` shape, depth 2).**  For every `s` with `hrun` there is an explicit `s'` (`bumpedStart`) with the same registers/memories and the same run result,
`ResetNk` kids whenever `s` has, and kids different from `resetKids D 2 raw`.  Generic in `raw b D`: no machine premise is used. -/
theorem topshareM_hsk_not_forced {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (ins : Nat → String → Nat) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs) :
    ∃ s' : KState (KT 2),
      runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
        (checkedOptimize b).body (seedIn b ins) T' s' = some envs ∧
      s'.st = s.st ∧ s'.mems = s.mems ∧ s'.kids ≠ Tools.ShippingSrm16Reset.resetKids D 2 raw ∧
      (Tools.ShippingMachineShipsDepth.ResetNk 2 raw D s.kids → Tools.ShippingMachineShipsDepth.ResetNk 2 raw D s'.kids) :=
  ⟨_, Tools.ShippingSrm18Start.bumpedStart_spec raw D _ _ _ _ _ _ s envs hrun⟩

/-- the same at depth 1 (`topshareQ` shape) -/
theorem topshareQ_hsk_not_forced {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (ins : Nat → String → Nat) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs) :
    ∃ s' : KState (KT 1),
      runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
        (checkedOptimize b).body (seedIn b ins) T' s' = some envs ∧
      s'.st = s.st ∧ s'.mems = s.mems ∧ s'.kids ≠ Tools.ShippingSrm16Reset.resetKids D 1 raw ∧
      (Tools.ShippingMachineShipsDepth.ResetNk 1 raw D s.kids → Tools.ShippingMachineShipsDepth.ResetNk 1 raw D s'.kids) :=
  ⟨_, Tools.ShippingSrm18Start.bumpedStart_spec raw D _ _ _ _ _ _ s envs hrun⟩

theorem topshareM_svBoundsH_viaStartNk (O : RefLawsAOps MkRefd mref cref)
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
    (rk : String → Option Nat)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrT : rk (Sparkle.IR.ModuleName.ofDecl ``topshareM) = some (2 + 1))
    (hrW : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM) = some (1 + 1))
    (hrW3 : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM3) = some (1 + 1))
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1)
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
    SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 2)) envs :=
  topshareM_svBoundsH_viaResetO O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' (⟨st0, mems, kids⟩ : KState (KT 2)) envs hrun hin hst₁ hst₂ hst₃ hRK hfit

theorem topshareQ_svBoundsH_viaStartNk (O : RefLawsAOps MkRefd mref cref)
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
    (rk : String → Option Nat)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrT : rk (Sparkle.IR.ModuleName.ofDecl ``topshareQ) = some (1 + 1))
    (hrP : rk (Sparkle.IR.ModuleName.ofDecl ``wrapP) = some (0 + 1))
    (hrQ : rk (Sparkle.IR.ModuleName.ofDecl ``wrapQ) = some (0 + 1))
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0)
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
    SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 1)) envs :=
  topshareQ_svBoundsH_viaResetO O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' (⟨st0, mems, kids⟩ : KState (KT 1)) envs hrun hin hst₁ hst₂ hst₃ hRK hfit

theorem topshareM_designSVH_viaStartNk (O : RefLawsAOps MkRefd mref cref)
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
    (rk : String → Option Nat)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrT : rk (Sparkle.IR.ModuleName.ofDecl ``topshareM) = some (2 + 1))
    (hrW : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM) = some (1 + 1))
    (hrW3 : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM3) = some (1 + 1))
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1)
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
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 2)) envs :=
  topshareM_designSVH_viaResetO O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' (⟨st0, mems, kids⟩ : KState (KT 2)) envs hrun hin hst₁ hst₂ hst₃ hRK hfit

theorem topshareQ_designSVH_viaStartNk (O : RefLawsAOps MkRefd mref cref)
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
    (rk : String → Option Nat)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrT : rk (Sparkle.IR.ModuleName.ofDecl ``topshareQ) = some (1 + 1))
    (hrP : rk (Sparkle.IR.ModuleName.ofDecl ``wrapP) = some (0 + 1))
    (hrQ : rk (Sparkle.IR.ModuleName.ofDecl ``wrapQ) = some (0 + 1))
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0)
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
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' (⟨st0, mems, kids⟩ : KState (KT 1)) envs :=
  topshareQ_designSVH_viaResetO O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' (⟨st0, mems, kids⟩ : KState (KT 1)) envs hrun hin hst₁ hst₂ hst₃ hRK hfit


end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hsk_not_forced
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hsk_not_forced
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaStartNk
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaStartNk
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaStartNk
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaStartNk
#print axioms Tools.ShippingSrm18Start.bumpedStart_spec
#print axioms Tools.ShippingSrm18Start.runModuleTG_kids_congr
