import Tests.Compiler.Srm4ParentTest
import Tests.Compiler.Srm4KidTest
import Tools.ShippingSrm5Deep
import Tools.ShippingSrm5Transfer
import Tools.ShippingModuleNames
-- UNBUILT (unit SRM5)
-- SCOPE: the height-indexed check applied to the memory-leaf class of `Tests/Compiler/SharedLeafMemKidTest.lean`: `topshareM` (calls `wrapM` ×2 and `wrapM3` ×2; each calls `leafM` ×2; `leafM` has the memory entry).  Heights: memory 0, `leafM` 1, `wrapM`/`wrapM3` 2, `topshareM` 3.
-- PROVED here (relative to the same premises as `Tests/Compiler/Srm4ParentTest.lean`): `leafM_kidHeight`, `wrapM_kidHeight`, `wrapM3_kidHeight` (the callee height facts), and `topshareM_hcheck`: the parent's height check with the children's check `hkids` of `topshareM_designCheck_of_kidsPass`
-- DISCHARGED.  The RANK TABLE is a premise (`rk`, with `hrkmem` and the four rank equations); `rkM` is a concrete table satisfying all of them (`rkM_*`), so the premises are satisfiable.
-- PREMISES kept (named): `O`, `T`, `hA`, the `MachineDefines` of the four machines (`entryL`, `entry₁`, `entry₂`, `entry`), the core run `hcore` and start world `hw`, `hpost`.  `RealChildA` is a history of past synthesis results, not freshness or runtime fit.
-- NOT claimed: the other conjuncts of the endpoint, any other class.  No `sorry`, no `axiom`, no `native_decide`.
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
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest
open Tools.ShippingSrm5Height Tools.ShippingSrm5Deep

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem leafM_args : Tools.ShippingPortsMatchRaw.callArgsOk leafM.machineData 4 lmKidIns = true := by first | decide | decide +kernel
theorem wrapM_args : Tools.ShippingPortsMatchRaw.callArgsOk wrapM.machineData 4 (fun _ => argWidths leafM.machineData 4) = true := by first | decide | decide +kernel
theorem wrapM3_args : Tools.ShippingPortsMatchRaw.callArgsOk wrapM3.machineData 4 (fun _ => argWidths leafM.machineData 4) = true := by first | decide | decide +kernel

/-- **The height fact of `leafM`** (rank 1; its only call is the memory entry, at rank 0 by `hrkmem`) -/
theorem leafM_kidHeight (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (rk : String → Option Nat) (f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some (0 + 1))
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0) :
    KidHeight O ``leafM rk (f + 1) :=
  memCallee_kidHeight O T leafM_memCallee (fun _ _ _ k hk y hn _ => (leafM_none_false hk hn).elim) lmKidOuts lmKidIns
    (fun k hk cb aw dw h => by
      have hk0 : k = 0 := by have := leafM_len; omega
      subst hk0
      obtain ⟨e1, e2, e3⟩ := memModule_inj ((Option.some.inj (leafM_origin0.symm.trans h)))
      subst e1; subst e2; subst e3
      exact ⟨rfl, rfl⟩)
    (fun k hk hn => (leafM_none_false hk hn).elim)
    (by first | decide | decide +kernel) leafM_args (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (leafM_outsClean o ho))
    (by first | decide | decide +kernel) entryL rk 0 f hrb hrkmem
    (fun k hk hn => (leafM_none_false hk hn).elim) (fun k hk hn => (leafM_none_false hk hn).elim)

/-- **The height fact of `wrapM`** (rank 2; both calls are `leafM`, rank 1) -/
theorem wrapM_kidHeight (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (rk : String → Option Nat) (f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM) = some (1 + 1))
    (hl : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hleaf : KidHeight O ``leafM rk f) :
    KidHeight O ``wrapM rk (f + 1) :=
  memCallee_kidHeight O T wrapM_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun _ => leafM.machineData.shape.layout.outs) (fun _ => argWidths leafM.machineData 4)
    (fun k hk cb aw dw h => by rw [wrapM_allord k hk] at h; cases h)
    (fun k hk _ => by rw [wrapM_kids k hk]; exact leafM_kidFactsNC O T entryL)
    (by first | decide | decide +kernel) wrapM_args (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapM_outsClean o ho))
    (by first | decide | decide +kernel) entry rk 1 f hrb hrkmem
    (fun k hk _ => ⟨1, hl, Nat.le_refl _⟩)
    (fun k hk _ => by rw [wrapM_kids k hk]; exact hleaf)

/-- **The height fact of `wrapM3`** (rank 2) -/
theorem wrapM3_kidHeight (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (rk : String → Option Nat) (f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl ``wrapM3) = some (1 + 1))
    (hl : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1)
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hleaf : KidHeight O ``leafM rk f) :
    KidHeight O ``wrapM3 rk (f + 1) :=
  memCallee_kidHeight O T wrapM3_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM3_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun _ => leafM.machineData.shape.layout.outs) (fun _ => argWidths leafM.machineData 4)
    (fun k hk cb aw dw h => by rw [wrapM3_allord k hk] at h; cases h)
    (fun k hk _ => by rw [wrapM3_kids k hk]; exact leafM_kidFactsNC O T entryL)
    (by first | decide | decide +kernel) wrapM3_args (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapM3_outsClean o ho))
    (by first | decide | decide +kernel) entry rk 1 f hrb hrkmem
    (fun k hk _ => ⟨1, hl, Nat.le_refl _⟩)
    (fun k hk _ => by rw [wrapM3_kids k hk]; exact hleaf)

open Tests.Compiler.SharedLeafMemKidEntryTest in
/-- **The height check of `topshareM` (rank 3), the children's check `hkids` DISCHARGED**: everything of `topshareM_designCheck_of_kidsPass` plus the children's half, from the rank table (`hr*`, `hrkmem`) and the callees' height facts. -/
theorem topshareM_hcheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
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
    (hrL : rk (Sparkle.IR.ModuleName.ofDecl ``leafM) = some 1) :
    hcheck (childMap D.modules) rk (f + 3) (checkedOptimize b) = true := by
  have hMn := (Tools.ShippingParentTailsA.core_kids_facts_ranA O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_outTy
    topshareM_nomem hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)).1
  have hrb : rk (checkedOptimize b).name = some (2 + 1) := by
    rw [Tools.ShippingModuleNames.checkedOptimize_name, post_name hpost, hMn]; exact hrT
  have hleaf : KidHeight O ``leafM rk (f + 1) := leafM_kidHeight O T entryL rk f hrL hrkmem
  refine Tools.ShippingSrm5Transfer.kidsNC_hcheck O topshareM.machineData topshareM_parentData.ok topshareM_parentData.body
    (nDecl := 4) topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne
    topshareM_slotsNe topshareM_fne topshareM_outTy topshareM_nomem tmOuts tmIns (topshareM_hkid O T entryL entry₁ entry₂)
    topshareM_cw topshareM_ca hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topshareM_outsClean o ho)) topshareM_scalar rk 2 (f + 2) hrb
    (fun k hk y' hre => ?_) (fun k hk y' hre ms hy1 hy2 => ?_)
  · rw [topshareM_name k hk] at hre
    split at hre
    · have := (wrapM_ifaceP O T entryL entry₁ hre).name
      exact ⟨1 + 1, by rw [this]; exact hrW, by omega⟩
    · have := (wrapM3_ifaceP O T entryL entry₂ hre).name
      exact ⟨1 + 1, by rw [this]; exact hrW3, by omega⟩
  · rw [topshareM_name k hk] at hre
    split at hre
    · exact wrapM_kidHeight O T entryL entry₁ rk (f + 1) hrW hrL hrkmem hleaf y' hre ms hy1 hy2
    · exact wrapM3_kidHeight O T entryL entry₂ rk (f + 1) hrW3 hrL hrkmem hleaf y' hre ms hy1 hy2

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_kidHeight
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_kidHeight
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck
