import Tests.Compiler.Srm4ParentQTest
import Tests.Compiler.Srm5ParentTest
-- BUILT (unit SRM5): s5h3 exit 0 (dev run, default heartbeats, no heartbeat option); the final-SHA rebuild is in REPORT-SRM5.md.
-- SCOPE: the height-indexed check applied to `topshareQ` (`Tests/Compiler/SharedLeafMemKidTest.lean`): calls `wrapP` ×2 (two calls of the PLAIN leaf `leafP`) and `wrapQ` ×2 (two calls of `leafP` and ONE memory entry).  Heights: `leafP` 0, memory 0, `wrapP` 1,
-- `wrapQ` 1, `topshareQ` 2 — NOTE: `leafP` (an ordinary leaf) and the memory module are both at rank 0, so the kids of `wrapQ` sit at heights 0 and 0 while `wrapM`'s kid `leafM` sits at 1; the unbalanced shape is the point of the height index.
-- PROVED here (same premises as `Tests/Compiler/Srm4ParentQTest.lean`): `wrapP_memCallee` (the decidable data of `wrapP` as a `MemCalleeData` with ordinary calls only), `leafP_kidHeight`, `wrapP_kidHeight`, `wrapQ_kidHeight`,
-- `topshareQ_hcheck`: the parent's height check with the children's check `hkids` of `topshareQ_designCheck_of_kidsPass` DISCHARGED, under a RANK TABLE premise (`rk`, `hrkmem`, the four rank equations).
-- PREMISES kept (named): `O`, `T`, `hA`, `hR0`/`hcl` (the plain leaf), the `MachineDefines` of the machines, `hcore`, `hw`, `hpost`.  `RealChildA` is a history of past synthesis results, not freshness or runtime fit.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Parent
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingMemKid (memOuts memIns)
open Tools.ShippingMachineAuto
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm5Deep Tools.ShippingMemCloses

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

def wpName : Nat → String := fun _ => Sparkle.IR.ModuleName.ofDecl ``leafP
noncomputable def wpNk : Nat → Nat := fun _ => Tools.ShippingQuadLeafGeneric.leafNk leafP.machineData
noncomputable def wpOuts : Nat → List String := fun _ => leafP.machineData.shape.layout.outs.map (·.name)
def wpNames : Nat → List String := fun _ => []

theorem wrapP_kids : ∀ k (hk : k < wrapP.machineData.shape.insts.length), (wrapP.machineData.shape.insts[k]).1 = ``leafP := by
  first | decide | decide +kernel
theorem wrapP_allord : ∀ k (hk : k < wrapP.machineData.shape.insts.length), (originAt wrapP.machineData.shape k).child? = none := by
  first | decide | decide +kernel

theorem wrapP_memCallee : MemCalleeData wrapP.machineData ``wrapP 3 wpName wpNk wpOuts wpNames namesP := by
  refine ⟨wrapP.machine_ok, wrapP.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem wrapP_outsClean : ∀ o ∈ wrapP.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

/-- `ChildIfaceP` of a `RealChildA` of `wrapP` -/
theorem wrapP_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) {y : Res} (h : RealChildA O ``wrapP y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapP) (machNIn wrapP.machineData.shape)
      (wrapP.machineData.shape.layout.outs.map (·.name)) namesP y.1 y.2 :=
  memCallee_ifaceP O T wrapP_memCallee (fun m' c' _ k hk y hn hre => by
    rw [wrapP_kids k hk] at hre
    exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre) entry h

/-- **The height fact of the plain leaf `leafP`** (rank 0: `leafCheck`, from the depth-0 `check` of `leaf_kidFactsA`) -/
theorem leafP_kidHeight (O : RefLawsAOps MkRefd mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (rk : String → Option Nat) (f : Nat) (hr : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0) :
    KidHeight O ``leafP rk f := fun y hre ms hy1 hy2 =>
  hcheck_rank0 (by rw [(leafKid_ifaceP O leafP_data hR0 hcl hre).name]; exact hr)
    ((Tools.ShippingQuadComposed.leaf_kidFactsA O leafP_data leafP_kidData hR0 hcl 0).check y hre ms hy1 hy2).1 f

/-- **The height fact of `wrapP`** (rank 1; both calls are the plain leaf `leafP`, rank 0) -/
theorem wrapP_kidHeight (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (rk : String → Option Nat) (f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl ``wrapP) = some (0 + 1))
    (hl : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hleaf : KidHeight O ``leafP rk f) :
    KidHeight O ``wrapP rk (f + 1) :=
  memCallee_kidHeight O T wrapP_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapP_kids k hk] at hre
      exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre)
    (fun _ => leafP.machineData.shape.layout.outs) (fun _ => Tools.ShippingPortWidthsPure.declWidths leafP.machineData)
    (fun k hk cb aw dw h => by rw [wrapP_allord k hk] at h; cases h)
    (fun k hk _ => by
      rw [wrapP_kids k hk]
      exact KidFactsA.toNC (Tools.ShippingQuadComposed.leaf_kidFactsA O leafP_data leafP_kidData hR0 hcl 0))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapP_outsClean o ho))
    (by first | decide | decide +kernel) entry rk 0 f hrb hrkmem
    (fun k hk _ => ⟨0, hl, Nat.le_refl _⟩)
    (fun k hk _ => by rw [wrapP_kids k hk]; exact hleaf)

/-- **The height fact of `wrapQ`** (rank 1; two calls of `leafP`, rank 0, and ONE memory entry, rank 0) -/
theorem wrapQ_kidHeight (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (rk : String → Option Nat) (f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl ``wrapQ) = some (0 + 1))
    (hl : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hleaf : KidHeight O ``leafP rk f) :
    KidHeight O ``wrapQ rk (f + 1) :=
  memCallee_kidHeight O T wrapQ_memCallee
    (fun m' c' _ k hk y hn hre => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm] at hre
      simp only [wqName, wqNk, wqOuts, wqNames, if_pos hk2]
      exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre)
    wqKidOuts wqKidIns
    (fun k hk cb aw dw h => by
      have hk2 : k = 2 := by
        rcases Nat.lt_or_ge k 2 with hk' | hk'
        · have h0 : (originAt wrapQ.machineData.shape k).child? = none := (wrapQ_ord_lt k hk hk')
          rw [h0] at h; cases h
        · have := wrapQ_len; omega
      subst hk2
      obtain ⟨e1, e2, e3⟩ := memModule_inj ((Option.some.inj (wrapQ_origin2.symm.trans h)))
      subst e1; subst e2; subst e3
      simp only [wqKidOuts, wqKidIns]
      exact ⟨by simp, by simp⟩)
    (fun k hk hn => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm]
      simp only [wqKidOuts, wqKidIns, if_pos hk2]
      exact KidFactsA.toNC (Tools.ShippingQuadComposed.leaf_kidFactsA O leafP_data leafP_kidData hR0 hcl 0))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapQ_outsClean o ho))
    (by first | decide | decide +kernel) entry rk 0 f hrb hrkmem
    (fun k hk hn => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      simp only [wqName, if_pos hk2]
      exact ⟨0, hl, Nat.le_refl _⟩)
    (fun k hk hn => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm]; exact hleaf)

/-- **The height check of `topshareQ` (rank 2), the children's check `hkids` DISCHARGED**, under the rank table `rk`. -/
theorem topshareQ_hcheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
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
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0) :
    hcheck (childMap D.modules) rk (f + 2) (checkedOptimize b) = true := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_outTy
    topshareQ_nomem hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (1 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  have hleaf : KidHeight O ``leafP rk f := leafP_kidHeight O hR0 hcl rk f hrL
  refine Tools.ShippingSrm5Transfer.kidsNC_hcheck O topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body
    (nDecl := 4) topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne
    topshareQ_slotsNe topshareQ_fne topshareQ_outTy topshareQ_nomem tqOuts tqIns (topshareQ_hkid O T hR0 hcl entry₁ entry₂)
    topshareQ_cw topshareQ_ca hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareQ_outsClean o ho)) topshareQ_scalar rk 1 (f + 1) hrb
    (fun k hk y' hre => ?_) (fun k hk y' hre ms hy1 hy2 => ?_)
  · rw [topshareQ_name k hk] at hre
    split at hre
    · have := (wrapP_ifaceP O T hR0 hcl entry₁ hre).name
      exact ⟨0 + 1, by rw [this]; exact hrP, by omega⟩
    · have := (wrapQ_ifaceP O T hR0 hcl entry₂ hre).name
      exact ⟨0 + 1, by rw [this]; exact hrQ, by omega⟩
  · rw [topshareQ_name k hk] at hre
    split at hre
    · exact wrapP_kidHeight O T hR0 hcl entry₁ rk f hrP hrL hrkmem hleaf y' hre ms hy1 hy2
    · exact wrapQ_kidHeight O T hR0 hcl entry₂ rk f hrQ hrL hrkmem hleaf y' hre ms hy1 hy2

/-! ## A concrete rank table satisfying the premises -/

open Classical in
/-- built memory modules and the plain leaf at height 0, `wrapP`/`wrapQ` 1, `topshareQ` 2; every other name has NO rank -/
noncomputable def rkQ : String → Option Nat := fun n =>
  if ∃ (cb : Bool) (aw dw : Nat), n = Sparkle.IR.ModuleName.ofMem cb aw dw then some 0
  else if n = Sparkle.IR.ModuleName.ofDecl ``leafP then some 0
  else if n = Sparkle.IR.ModuleName.ofDecl ``wrapP ∨ n = Sparkle.IR.ModuleName.ofDecl ``wrapQ then some 1
  else if n = Sparkle.IR.ModuleName.ofDecl ``topshareQ then some 2 else none

private theorem rkQ_notMem (c : Lean.Name) : ¬ ∃ (cb : Bool) (aw dw : Nat), Sparkle.IR.ModuleName.ofDecl c = Sparkle.IR.ModuleName.ofMem cb aw dw :=
  fun ⟨cb, aw, dw, h⟩ => Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw h

theorem rkQ_mem : ∀ (cb : Bool) (aw dw : Nat), rkQ (memModule cb aw dw).1.name = some 0 := by
  intro cb aw dw
  have : ∃ (cb' : Bool) (aw' dw' : Nat), (memModule cb aw dw).1.name = Sparkle.IR.ModuleName.ofMem cb' aw' dw' := ⟨cb, aw, dw, rfl⟩
  simp [rkQ, this]

theorem rkQ_leaf : rkQ (Sparkle.IR.ModuleName.ofDecl ``leafP) = some 0 := by
  rw [rkQ, if_neg (rkQ_notMem _)]; simp

theorem rkQ_wrapP : rkQ (Sparkle.IR.ModuleName.ofDecl ``wrapP) = some 1 := by
  have h1 : ¬ Sparkle.IR.ModuleName.ofDecl ``wrapP = Sparkle.IR.ModuleName.ofDecl ``leafP :=
    fun h => absurd (Tools.ShippingModuleName.ofDecl_injective h) (by decide)
  rw [rkQ, if_neg (rkQ_notMem _)]; simp [h1]

theorem rkQ_wrapQ : rkQ (Sparkle.IR.ModuleName.ofDecl ``wrapQ) = some 1 := by
  have h1 : ¬ Sparkle.IR.ModuleName.ofDecl ``wrapQ = Sparkle.IR.ModuleName.ofDecl ``leafP :=
    fun h => absurd (Tools.ShippingModuleName.ofDecl_injective h) (by decide)
  rw [rkQ, if_neg (rkQ_notMem _)]; simp [h1]

theorem rkQ_top : rkQ (Sparkle.IR.ModuleName.ofDecl ``topshareQ) = some 2 := by
  have h1 : ¬ Sparkle.IR.ModuleName.ofDecl ``topshareQ = Sparkle.IR.ModuleName.ofDecl ``leafP :=
    fun h => absurd (Tools.ShippingModuleName.ofDecl_injective h) (by decide)
  have h2 : ¬ Sparkle.IR.ModuleName.ofDecl ``topshareQ = Sparkle.IR.ModuleName.ofDecl ``wrapP :=
    fun h => absurd (Tools.ShippingModuleName.ofDecl_injective h) (by decide)
  have h3 : ¬ Sparkle.IR.ModuleName.ofDecl ``topshareQ = Sparkle.IR.ModuleName.ofDecl ``wrapQ :=
    fun h => absurd (Tools.ShippingModuleName.ofDecl_injective h) (by decide)
  rw [rkQ, if_neg (rkQ_notMem _)]; simp [h1, h2, h3]

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapP_kidHeight
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_kidHeight
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck
