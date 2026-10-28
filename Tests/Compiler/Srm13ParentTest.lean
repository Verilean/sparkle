import Tests.Compiler.Srm11ParentTest
import Tools.ShippingSrm13Supply
set_option autoImplicit false
-- BUILT (unit SRM13): dev runs a2 (Supply), a4 (ParentTest), b4 (AuditTest) all exit 0; the final-SHA rebuild is in REPORT-SRM13.md.
-- SCOPE: corollaries of the SRM11 instance theorems (statements untouched; they are CALLED) for `topshareM`/`topshareQ`.  The top seeding is the machine's `seedIn b ins`; `hseedB` is REPLACED by the input range `hin` (PROVED sufficient: `seedB_checkedOptimize`).
-- `hst` is REPLACED by the three register/width facts `RegsAtInit`/`RegsFit`/`NonRegBounded` of the start state, `hkids` by the machine's children reset `ResetNk`, `hO` (the shipped instances are source instances) and `FitTree` (width fits of each instance tree);
-- sufficiency PROVED in Tools.ShippingSrm13Supply.  These are replacements, not discharges: `RegsFit`, `NonRegBounded`, `FitTree`, `hO`, `hin` and the top `RegsAtInit` are PREMISES here.  NOT claimed: that they hold for the machine's run.  No `sorry`, no `axiom`, no `native_decide`.
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

theorem topshareM_svBoundsH_viaReset (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (ins : Nat → String → Nat) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st) (hst₂ : RegsFit (checkedOptimize b)) (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hrk : Tools.ShippingMachineShipsDepth.ResetNk 2 raw D s.kids)
    (hO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → Stmt.inst mn iname conns ∈ raw.body)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs := by
  exact topshareM_svBoundsH O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL (seedIn b ins) T' s envs hrun
    (seedB_checkedOptimize b ins hin) (bounded_of_regsAtInit hst₁ hst₂ hst₃) (kidInvN_of_resetNk hrk hO hfit)

theorem topshareQ_svBoundsH_viaReset (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (ins : Nat → String → Nat) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st) (hst₂ : RegsFit (checkedOptimize b)) (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hrk : Tools.ShippingMachineShipsDepth.ResetNk 1 raw D s.kids)
    (hO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → Stmt.inst mn iname conns ∈ raw.body)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs := by
  exact topshareQ_svBoundsH O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL (seedIn b ins) T' s envs hrun
    (seedB_checkedOptimize b ins hin) (bounded_of_regsAtInit hst₁ hst₂ hst₃) (kidInvN_of_resetNk hrk hO hfit)

theorem topshareM_designSVH_viaReset (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (ins : Nat → String → Nat) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st) (hst₂ : RegsFit (checkedOptimize b)) (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hrk : Tools.ShippingMachineShipsDepth.ResetNk 2 raw D s.kids)
    (hO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → Stmt.inst mn iname conns ∈ raw.body)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs :=
  topshareM_designSVH_noB O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL (seedIn b ins) T' s envs hrun
    (seedB_checkedOptimize b ins hin) (bounded_of_regsAtInit hst₁ hst₂ hst₃) (kidInvN_of_resetNk hrk hO hfit)

theorem topshareQ_designSVH_viaReset (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (ins : Nat → String → Nat) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st) (hst₂ : RegsFit (checkedOptimize b)) (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hrk : Tools.ShippingMachineShipsDepth.ResetNk 1 raw D s.kids)
    (hO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → Stmt.inst mn iname conns ∈ raw.body)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs :=
  topshareQ_designSVH_noB O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL (seedIn b ins) T' s envs hrun
    (seedB_checkedOptimize b ins hin) (bounded_of_regsAtInit hst₁ hst₂ hst₃) (kidInvN_of_resetNk hrk hO hfit)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaReset
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaReset
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaReset
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaReset
