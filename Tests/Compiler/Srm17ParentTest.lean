import Tests.Compiler.Srm16ParentTest
import Tests.Compiler.Srm12CorrTest
import Tools.ShippingSrm17Corr
set_option autoImplicit false
-- UNBUILT (unit SRM17): see REPORT-SRM17.md for run names / exits.
-- SCOPE: for `topshareM` (depth 2) and `topshareQ` (depth 1) under the SRM16 machine premises (`O`, `T`, `hA`, the `MachineDefines` of the machines, `hcore`, `hpost`, `hw`):
-- * `ChildP` of the callees (`leafM`/`wrapM`/`wrapM3`, `leafP`/`wrapP`/`wrapQ`) by `memCallee_childP`/`leaf_childP` (Tools/ShippingSrm17Corr.lean);
-- * `topshare{M,Q}_modP`: the run's module `raw` and every module of `D.modules` satisfy `ModP` (`ran_designP`), under the extra explicit premise-free facts `slots ≠ []` of each machine, decided here;
-- * `topshare{M,Q}_{hIUraw,hIU,hAg,hRd}` (PROVED): the four residual premises of SRM16's `resetNk_resetKids`, stated with the SAME Prop text as SRM16's binders, from `topshare{M,Q}_modP`;
-- * `topshare{M,Q}_{svBoundsH,designSVH}_viaResetSrc`: SRM16's `_viaResetState` (CALLED, statement unchanged) WITHOUT the binders `hIUraw hIU hAg hRd`; `hsk` (the start state's kids ARE `resetKids D n raw`), `hin`, `RegsAtInit`/`RegsFit`/`NonRegBounded`, `FitTree`
--   stay explicit PREMISES; hrun is NOT assumed to start at the reset state beyond `hsk`.
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

open Tools.ShippingSrm17Body Tools.ShippingSrm17Corr
open Tools.ShippingInstTagged (originAt)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## `ChildP` of the callees -/

theorem leafM_childP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) : ChildP O ``leafM :=
  memCallee_childP O T leafM_memCallee (fun _ _ _ k hk y hn _ => (leafM_none_false hk hn).elim) entryL (by decide)
    (fun k hk hn => (leafM_none_false hk hn).elim)

theorem wrapM_childP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) : ChildP O ``wrapM :=
  memCallee_childP O T wrapM_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    entry (by decide) (fun k hk _ => by rw [wrapM_kids k hk]; exact leafM_childP O T entryL)

theorem wrapM3_childP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) : ChildP O ``wrapM3 :=
  memCallee_childP O T wrapM3_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM3_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    entry (by decide) (fun k hk _ => by rw [wrapM3_kids k hk]; exact leafM_childP O T entryL)

theorem leafP_childP (O : RefLawsAOps MkRefd mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) :
    ChildP O ``leafP :=
  leaf_childP O leafP_data hR0 hcl

theorem wrapP_childP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) : ChildP O ``wrapP :=
  memCallee_childP O T wrapP_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapP_kids k hk] at hre
      exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre)
    entry (by decide) (fun k hk _ => by rw [wrapP_kids k hk]; exact leafP_childP O hR0 hcl)

theorem wrapQ_childP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) : ChildP O ``wrapQ :=
  memCallee_childP O T wrapQ_memCallee
    (fun m' c' _ k hk y hn hre => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm] at hre
      simp only [wqName, wqNk, wqOuts, wqNames, if_pos hk2]
      exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre)
    entry (by decide)
    (fun k hk hn => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm]
      exact leafP_childP O hR0 hcl)

/-- **`ModP` for `topshareM`**: the run's module `raw` and every module of `D.modules` (a `ChildP` recursion over the callees, `ran_designP`). -/
theorem topshareM_modP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ModP raw ∧ ∀ g ∈ D.modules, ModP g := by
  have ran := topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw
  obtain ⟨hM, -, hD⟩ := ran_designP O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne
    topshareM_slotsNe topshareM_fne topshareM_outTy hpost ran
    (fun k hk _ => by
      by_cases hk2 : k < 2
      · rw [topshareM_name k hk, if_pos hk2]; exact wrapM_childP O T entryL entry₁
      · rw [topshareM_name k hk, if_neg hk2]; exact wrapM3_childP O T entryL entry₂)
  exact ⟨hM, hD⟩

theorem topshareM_hIUraw (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ (mn i : String) (c : List (String × Sparkle.IR.AST.Expr)) (mn' : String) (c' : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn' :=
  ((topshareM_modP O T hA entryL entry₁ entry₂ entry hcore hpost hw)).1.iu

theorem topshareM_hIU (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Sparkle.IR.AST.Expr)) (mn' : String) (c' : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn' :=
  fun m hm => ((topshareM_modP O T hA entryL entry₁ entry₂ entry hcore hpost hw).2 m hm).iu

theorem topshareM_hAg (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat :=
  fun m hm => ((topshareM_modP O T hA entryL entry₁ entry₂ entry hcore hpost hw).2 m hm).ag

theorem topshareM_hRd (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0 :=
  fun m hm => ((topshareM_modP O T hA entryL entry₁ entry₂ entry hcore hpost hw).2 m hm).rd

theorem topshareM_svBoundsH_viaResetSrc (O : RefLawsAOps MkRefd mref cref)
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
    (s : KState (KT 2))
    (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st)
    (hst₂ : RegsFit (checkedOptimize b))
    (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 2 raw)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs :=
  topshareM_svBoundsH_viaResetState O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hsk (topshareM_hIUraw O T hA entryL entry₁ entry₂ entry hcore hpost hw) (topshareM_hIU O T hA entryL entry₁ entry₂ entry hcore hpost hw) (topshareM_hAg O T hA entryL entry₁ entry₂ entry hcore hpost hw) (topshareM_hRd O T hA entryL entry₁ entry₂ entry hcore hpost hw) hfit

/-- **`ModP` for `topshareQ`**: the run's module `raw` and every module of `D.modules` (a `ChildP` recursion over the callees, `ran_designP`). -/
theorem topshareQ_modP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape) (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ModP raw ∧ ∀ g ∈ D.modules, ModP g := by
  have ran := topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw
  obtain ⟨hM, -, hD⟩ := ran_designP O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne
    (by decide) topshareQ_fne topshareQ_outTy hpost ran
    (fun k hk _ => by
      by_cases hk2 : k < 2
      · rw [topshareQ_name k hk, if_pos hk2]; exact wrapP_childP O T hR0 hcl entry₁
      · rw [topshareQ_name k hk, if_neg hk2]; exact wrapQ_childP O T hR0 hcl entry₂)
  exact ⟨hM, hD⟩

theorem topshareQ_hIUraw (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape) (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ (mn i : String) (c : List (String × Sparkle.IR.AST.Expr)) (mn' : String) (c' : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn' :=
  ((topshareQ_modP O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw)).1.iu

theorem topshareQ_hIU (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape) (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Sparkle.IR.AST.Expr)) (mn' : String) (c' : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn' :=
  fun m hm => ((topshareQ_modP O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw).2 m hm).iu

theorem topshareQ_hAg (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape) (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat :=
  fun m hm => ((topshareQ_modP O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw).2 m hm).ag

theorem topshareQ_hRd (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape) (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape) {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (hw : JQC O 0 w) :
    ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0 :=
  fun m hm => ((topshareQ_modP O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw).2 m hm).rd

theorem topshareQ_svBoundsH_viaResetSrc (O : RefLawsAOps MkRefd mref cref)
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
    (s : KState (KT 1))
    (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st)
    (hst₂ : RegsFit (checkedOptimize b))
    (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 1 raw)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    SVBoundsH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs :=
  topshareQ_svBoundsH_viaResetState O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hsk (topshareQ_hIUraw O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) (topshareQ_hIU O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) (topshareQ_hAg O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) (topshareQ_hRd O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) hfit

theorem topshareM_designSVH_viaResetSrc (O : RefLawsAOps MkRefd mref cref)
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
    (s : KState (KT 2))
    (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st)
    (hst₂ : RegsFit (checkedOptimize b))
    (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 2 raw)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 2 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 2 (checkedOptimize b) (seedIn b ins) T' s envs :=
  topshareM_designSVH_viaResetState O T hA entryL entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrW hrW3 hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hsk (topshareM_hIUraw O T hA entryL entry₁ entry₂ entry hcore hpost hw) (topshareM_hIU O T hA entryL entry₁ entry₂ entry hcore hpost hw) (topshareM_hAg O T hA entryL entry₁ entry₂ entry hcore hpost hw) (topshareM_hRd O T hA entryL entry₁ entry₂ entry hcore hpost hw) hfit

theorem topshareQ_designSVH_viaResetSrc (O : RefLawsAOps MkRefd mref cref)
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
    (s : KState (KT 1))
    (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body (seedIn b ins) T' s = some envs)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x)
    (hst₁ : RegsAtInit (checkedOptimize b) s.st)
    (hst₂ : RegsFit (checkedOptimize b))
    (hst₃ : NonRegBounded (checkedOptimize b) s.st)
    (hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D 1 raw)
    (hfit : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (s.kids iname)) :
    DesignSVH (childMap D.modules) rk 1 (checkedOptimize b) (seedIn b ins) T' s envs :=
  topshareQ_designSVH_viaResetState O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw rk hrkmem hrT hrP hrQ hrL ins T' s envs hrun hin hst₁ hst₂ hst₃ hsk (topshareQ_hIUraw O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) (topshareQ_hIU O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) (topshareQ_hAg O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) (topshareQ_hRd O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw) hfit


end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_modP
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hIUraw
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hIU
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hAg
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hRd
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_modP
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hIUraw
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hIU
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hAg
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hRd
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaResetSrc
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaResetSrc
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaResetSrc
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaResetSrc
