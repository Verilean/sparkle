import Tests.Compiler.Srm13ParentTest
import Tools.ShippingSrm16Reset
set_option autoImplicit false
-- UNBUILT (unit SRM16): dev runs are in REPORT-SRM16.md.
-- SCOPE: corollaries of the SRM13 `_viaReset` theorems (statements untouched; they are CALLED) for `topshareM`/`topshareQ`.
-- `topshare{M,Q}_hO` (PROVED): the shipped module's instance statements are statements of `raw`, from the machine run `ran` (`core_hierGate_anyAM`), `b.body = raw.body` (`core_kids_facts_ranA`) and `inst_checkedOptimize_sub`.
-- `_viaResetO`: the SRM13 theorem without the `hO` binder.  `_viaResetState`: without `hO` and `hrk`; the start state's kids are the CONSTRUCTED `resetKids D n raw` (`hsk`, a PREMISE: that the run starts from the reset state is not proved here), and `hrk` is
-- PROVED from it by `resetNk_resetKids` under the structural PREMISES `hIUraw hIU hAg hRd` (instance-name uniqueness, same-name register agreement, memory read-register reset 0 of the modules of `D`): these four are NOT proved for the concrete designs.
-- `RegsAtInit`/`RegsFit`/`NonRegBounded`/`FitTree`/`hin` stay PREMISES.  No `sorry`, no `axiom`, no `native_decide`.
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

/-- **`hO` for `topshareM`**: the instance statements of the shipped module are statements of `raw`. -/
theorem topshareM_hO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → Stmt.inst mn iname conns ∈ raw.body := by
  have ran := topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingSrm4Core2.core_hierGate_anyAM O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
      (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne
      topshareM_outTy hpost ran
  have hbb : b.body = raw.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
      (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy
      topshareM_nomem hpost ran).2.1
  intro mn iname conns h
  rw [← hbb]
  exact Tools.ShippingKidsResetSat.inst_checkedOptimize_sub hgate mn iname conns h

/-- **`hO` for `topshareQ`**. -/
theorem topshareQ_hO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → Stmt.inst mn iname conns ∈ raw.body := by
  have ran := topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingSrm4Core2.core_hierGate_anyAM O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
      (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne
      topshareQ_outTy hpost ran
  have hbb : b.body = raw.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
      (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy
      topshareQ_nomem hpost ran).2.1
  intro mn iname conns h
  rw [← hbb]
  exact Tools.ShippingKidsResetSat.inst_checkedOptimize_sub hgate mn iname conns h

theorem topshareM_svBoundsH_viaResetO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hO := topshareM_hO O T hA entryL entry₁ entry₂ entry hcore hpost hw
  exact topshareM_svBoundsH_viaReset O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hO hfit

theorem topshareM_svBoundsH_viaResetState (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 2 raw)
    (hIUraw : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hrk : Tools.ShippingMachineShipsDepth.ResetNk 2 raw D s.kids := by
    rw [hsk]
    exact Tools.ShippingSrm16Reset.resetNk_resetKids 2 raw D hIUraw hIU hAg hRd
  exact topshareM_svBoundsH_viaResetO O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hfit

theorem topshareQ_svBoundsH_viaResetO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hO := topshareQ_hO O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw
  exact topshareQ_svBoundsH_viaReset O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hO hfit

theorem topshareQ_svBoundsH_viaResetState (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 1 raw)
    (hIUraw : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hrk : Tools.ShippingMachineShipsDepth.ResetNk 1 raw D s.kids := by
    rw [hsk]
    exact Tools.ShippingSrm16Reset.resetNk_resetKids 1 raw D hIUraw hIU hAg hRd
  exact topshareQ_svBoundsH_viaResetO O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hfit

theorem topshareM_designSVH_viaResetO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hO := topshareM_hO O T hA entryL entry₁ entry₂ entry hcore hpost hw
  exact topshareM_designSVH_viaReset O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hO hfit

theorem topshareM_designSVH_viaResetState (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 2 raw)
    (hIUraw : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hrk : Tools.ShippingMachineShipsDepth.ResetNk 2 raw D s.kids := by
    rw [hsk]
    exact Tools.ShippingSrm16Reset.resetNk_resetKids 2 raw D hIUraw hIU hAg hRd
  exact topshareM_designSVH_viaResetO O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hfit

theorem topshareQ_designSVH_viaResetO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hO := topshareQ_hO O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw
  exact topshareQ_designSVH_viaReset O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hO hfit

theorem topshareQ_designSVH_viaResetState (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 1 raw)
    (hIUraw : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs := by
  have hrk : Tools.ShippingMachineShipsDepth.ResetNk 1 raw D s.kids := by
    rw [hsk]
    exact Tools.ShippingSrm16Reset.resetNk_resetKids 1 raw D hIUraw hIU hAg hRd
  exact topshareQ_designSVH_viaResetO O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hrk hfit


end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hO
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hO
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaResetO
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaResetState
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaResetO
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaResetState
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaResetO
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaResetState
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaResetO
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaResetState
