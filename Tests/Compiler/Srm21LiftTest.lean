import Tests.Compiler.Srm20BridgeTest
import Tests.Compiler.Srm12CorrTest
import Tools.ShippingSrm21Lift
set_option autoImplicit false
-- BUILT (unit SRM21): dev runs t1 (exit 1, parse error), t2 (exit 0); the final-SHA rebuild in REPORT-SRM21.md is the only final evidence.
-- SCOPE: (P4) `qDepthLift_of_grandInstFree` (QDepthLift from the real-data Prop `QGrandInstFree`, via the generic P2/P3 of Tools/ShippingSrm21Lift.lean) and the topshareQ INSTANCE of (P1):
--   `topshareQ_grandInstFree` from the SRM12 correspondence (`topshareQ_corr`: ModCorr gQ for b, checkedOptimize b, D.modules) and SRM7's computed ranks (gQ_top = 2, gQ_wrapP = gQ_wrapQ = 1, gQ_leaf = 0, memory 0):
--   a module of rank 0 has no instance statement (an instance statement targets a strictly smaller rank), and a grandchild of the shipped body has rank 0.
-- Premises of the instance theorems = those of `topshareQ_corr` (PREMISE: O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw); QDepthLift itself is no longer a premise there.
-- The corollary `topshareQ_svBoundsH_underComposedG'` is SRM20's `topshareQ_svBoundsH_underComposedG` (called UNCHANGED) with the `hlift` binder deleted; the remaining residuals are those of SRM20 (hBnd, hBd, hsrc/hpass/hrst/hclk/hinit, hRK, hinsFit/hstX/hstR, hin/hst₁₋₃, hfit).
-- The NAME `raw.name = ofDecl topshareQ` and `b.body = raw.body` are from `core_kids_facts_ranAM`.  `RealChildA` is a history of past synthesis results.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.Srm21LiftTest
open Lean Meta
open Tools.ShippingSrm7Rank Tools.ShippingSrm12Corr Sparkle.Compiler.MachInstOrigin
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm7RankTest Tests.Compiler.Srm12CorrTest
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingMemCloses Tools.ShippingMachineAuto
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm21Lift
open Tools.ShippingMachineLinked (childMap)
open Sparkle.IR.ModuleName (ofDecl)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierStateG (KT KSn KState runModuleTG instFree)
open Tools.ShippingMachineShipsDepth (ResetNk kidsMaskedN)
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingMachineShipsDepth Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Semantics (MEnv Env)
open Tools.ShippingSrm13Supply Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tests.Compiler.Srm9ComposedTest (TmBnd TqBnd tmExt tmExtB tqExt tqExtB)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **(P4)** `QDepthLift` from (P1) for the shipped body and for `raw`: the depth lift of the reset state (P3) and the run agreement (P2). -/
theorem qDepthLift_of_grandInstFree (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (b : Sparkle.IR.AST.Module)
    (h : QGrandInstFree raw D b) : QDepthLift raw D b := by
  intro kids1 hR
  obtain ⟨kids2, hR2, hc⟩ := resetNk_depth_lift raw D h.2 kids1 hR
  refine ⟨kids2, hR2, ?_⟩
  intro seed T st0 mems envs hrun
  rw [← runModuleTG_depth2_depth1_of_grandInstFree D b h.1 kids2 kids1 hc seed T st0 mems]
  exact hrun

/-! ## the rank argument: a grandchild of a rank-<=2 body has rank 0 and no instance statement -/

theorem childMap_moduleByName {ms : List Sparkle.IR.AST.Module} {mn : String} {gc : Sparkle.IR.AST.Module} {w : Sparkle.IR.Semantics.WEnv}
    (h : childMap ms mn = some (gc, w)) : moduleByName ms mn = some gc := by
  unfold childMap at h
  cases hh : moduleByName ms mn with
  | none => rw [hh] at h; simp at h
  | some c =>
    rw [hh] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]

theorem grandInstFree_of_ranks (D : Sparkle.IR.AST.Design) (hD : DesignCorr gQ D.modules) (body : List Stmt)
    (htop : ∀ mn i conns, Stmt.inst mn i conns ∈ body → ∃ r', rkOf gQ 3 mn = some r' ∧ r' < 2) :
    GrandInstFree D body := by
  intro mn1 i1 c1 gc1 w1 hin1 hch1 mn2 i2 c2 gc2 w2 hin2 hch2
  have hm1 := childMap_moduleByName hch1
  have hm2 := childMap_moduleByName hch2
  have hg1 : gc1 ∈ D.modules := List.mem_of_find?_eq_some hm1
  have hg2 : gc2 ∈ D.modules := List.mem_of_find?_eq_some hm2
  have hn1 : gc1.name = mn1 := Tools.ShippingMachineInst.moduleByName_name hm1
  have hn2 : gc2.name = mn2 := Tools.ShippingMachineInst.moduleByName_name hm2
  obtain ⟨r1, hr1, hlt1⟩ := htop mn1 i1 c1 hin1
  obtain ⟨r, r2, e1, e2, hlt⟩ := inst_rank_of_modCorr_Q hD gc1 hg1 mn2 i2 c2 hin2
  rw [hn1, hr1] at e1
  have hr : r = r1 := (Option.some.inj e1).symm
  intro st hst
  cases st with
  | inst mn3 i3 c3 =>
    exfalso
    obtain ⟨s, s', f1, f2, hlt'⟩ := inst_rank_of_modCorr_Q hD gc2 hg2 mn3 i3 c3 hst
    rw [hn2, e2] at f1
    have : s = r2 := (Option.some.inj f1).symm
    omega
  | _ => simp [Sparkle.IR.Machine.isInst]

/-! ## topshareQ: (P1) from the source facts -/

theorem topshareQ_grandInstFree (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    QGrandInstFree raw D b := by
  obtain ⟨hb, hopt, hD⟩ := topshareQ_corr O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw
  have hran := topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw
  obtain ⟨hMn, hbb, -⟩ := Tools.ShippingSrm3Iface.core_kids_facts_ranAM O topshareQ.machineData topshareQ_parentData.ok
    topshareQ_parentData.body (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB
    topshareQ_insts_ne topshareQ_fne topshareQ_outTy hpost hran
  have hbn : b.name = ofDecl ``topshareQ := (Tools.ShippingSrm5Deep.post_name hpost).trans hMn
  have hon : (checkedOptimize b).name = ofDecl ``topshareQ := (Tools.ShippingModuleNames.checkedOptimize_name b).trans hbn
  have hr2 : rkOf gQ 3 (ofDecl ``topshareQ) = some 2 := by
    simp only [rkOf, decode_ofDecl]; exact gQ_top
  refine ⟨grandInstFree_of_ranks D hD _ ?_, grandInstFree_of_ranks D hD _ ?_⟩
  · intro mn i conns hin
    obtain ⟨r, r', e1, e2, hlt⟩ := inst_rank_of_modCorr_Q (ms := [checkedOptimize b])
      (fun m hm => by rw [List.mem_singleton.mp hm]; exact hopt) (checkedOptimize b) (List.mem_singleton_self _) mn i conns hin
    rw [hon, hr2] at e1
    have : r = 2 := (Option.some.inj e1).symm
    exact ⟨r', e2, by omega⟩
  · intro mn i conns hin
    rw [← hbb] at hin
    obtain ⟨r, r', e1, e2, hlt⟩ := inst_rank_of_modCorr_Q (ms := [b])
      (fun m hm => by rw [List.mem_singleton.mp hm]; exact hb) b (List.mem_singleton_self _) mn i conns hin
    rw [hbn, hr2] at e1
    have : r = 2 := (Option.some.inj e1).symm
    exact ⟨r', e2, by omega⟩

/-- **(P4) for topshareQ: `QDepthLift raw D b` DERIVED** (premises of `topshareQ_corr`). -/
theorem topshareQ_qDepthLift (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    QDepthLift raw D b :=
  qDepthLift_of_grandInstFree raw D b (topshareQ_grandInstFree O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw)

/-- **Corollary**: SRM20's `topshareQ_svBoundsH_underComposedG` (called unchanged) WITHOUT the `hlift` binder; `QDepthLift` is derived from `hBnd` by `topshareQ_qDepthLift`.  All other residuals are SRM20's. -/
theorem topshareQ_svBoundsH_underComposedG'
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D)
    (hBd : kidsMaskedN D.modules b.body = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshareQ.machineData.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = topshareQ.machineData.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT 1),
        (∀ t st, t < T → Tools.ShippingMixedSourceBridge.SourceInputs ``topshareQ (topshareQ.machineData.bsIn.take 4) ids cache
          (fun j => (tqExtB i bools bits j).val (T - 1 - t)) (fun j n => (tqExt i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → topshareQ.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 1 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body → st0 x < 2 ^ declWidth b x) →
        (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
        RegsAtInit (checkedOptimize b) st0 → RegsFit (checkedOptimize b) → NonRegBounded (checkedOptimize b) st0 →
        (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
          childMap D.modules mn = some (gc, gcwe) → FitTree (childMap D.modules) 1 gc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
            (checkedOptimize b).body (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 1)) = some envs ∧
          envs.length = T ∧
          (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            topshareQ.machineData.shape.layout.outs[k]? = some o → (topshareQ.machineSource i bools bits)[k]? = some f → (envs[j]'hj) o.name = f j) ∧
          SVBoundsH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT 1)) envs   := by
  have hB := hBnd
  obtain ⟨O, T0, hA, hR0, hcl, entry₁, entry₂, -, -, -, hw⟩ := hB
  exact Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_underComposedG hcore hpost entry hBnd hBd
    (topshareQ_qDepthLift O T0 hA hR0 hcl entry₁ entry₂ entry hcore hpost hw)

end Tests.Compiler.Srm21LiftTest

#print axioms Tests.Compiler.Srm21LiftTest.qDepthLift_of_grandInstFree
#print axioms Tests.Compiler.Srm21LiftTest.topshareQ_grandInstFree
#print axioms Tests.Compiler.Srm21LiftTest.topshareQ_qDepthLift
#print axioms Tests.Compiler.Srm21LiftTest.topshareQ_svBoundsH_underComposedG'
