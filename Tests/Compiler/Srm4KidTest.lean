import Tests.Compiler.SharedLeafMemKidIfaceTest
import Tools.ShippingSrm4Kid
import Tools.ShippingQuadComposed
-- BUILT (unit SRM4): e7 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (residue R2): `Tools.ShippingSrm4Kid.memCallee_kidFactsNC` HAND-APPLIED to the callees of `Tests/Compiler/SharedLeafMemKidTest.lean`: `leafM` (every call a memory entry), `wrapM` (every call the memory-bearing leaf `leafM`),
-- `wrapQ` (two calls of the plain leaf `leafP` and one memory entry).  `KidFactsNC` = `KidFactsA` WITHOUT the `check` field (unsatisfiable for a design with a memory module, `Tools.ShippingSrm4Check`).
-- PREMISES kept (named): `entry` / `hR0` (`MachineDefines`), `hcl` (`MachineCloses` of the plain leaf), `O`, `T`; the decidable data (`MemCalleeData`, `callWidthsOk`, name / type conditions).  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingMemKid (memOuts memIns)
open Tools.ShippingMachineAuto
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem leafM_len : leafM.machineData.shape.insts.length = 1 := by decide
theorem leafM_origin0 : (originAt leafM.machineData.shape 0).child? = some (memModule false 4 8) := by first | rfl | decide +kernel

def lmKidOuts : Nat → List OutField := fun _ => memOuts 8
def lmKidIns : Nat → List Nat := fun _ => memIns 4 8

theorem leafM_outsClean : ∀ o ∈ leafM.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem leafM_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) :
    KidFactsNC O ``leafM leafM.machineData.shape.layout.outs (argWidths leafM.machineData 4) :=
  memCallee_kidFactsNC O T leafM_memCallee (fun _ _ _ k hk y hn _ => (leafM_none_false hk hn).elim) lmKidOuts lmKidIns
    (fun k hk cb aw dw h => by
      have hk0 : k = 0 := by have := leafM_len; omega
      subst hk0
      obtain ⟨e1, e2, e3⟩ := memModule_inj ((Option.some.inj (leafM_origin0.symm.trans h)))
      subst e1; subst e2; subst e3
      exact ⟨rfl, rfl⟩)
    (fun k hk hn => (leafM_none_false hk hn).elim)
    (by first | decide | decide +kernel) (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (leafM_outsClean o ho))
    (by first | decide | decide +kernel) entryL

/-! ## `wrapM`: every call is the memory-bearing leaf `leafM` -/

theorem wrapM_allord : ∀ k (hk : k < wrapM.machineData.shape.insts.length), (originAt wrapM.machineData.shape k).child? = none := by
  first | decide | decide +kernel
theorem wrapM_outsClean : ∀ o ∈ wrapM.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem wrapM_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) :
    KidFactsNC O ``wrapM wrapM.machineData.shape.layout.outs (argWidths wrapM.machineData 4) :=
  memCallee_kidFactsNC O T wrapM_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun _ => leafM.machineData.shape.layout.outs) (fun _ => argWidths leafM.machineData 4)
    (fun k hk cb aw dw h => by rw [wrapM_allord k hk] at h; cases h)
    (fun k hk _ => by rw [wrapM_kids k hk]; exact leafM_kidFactsNC O T entryL)
    (by first | decide | decide +kernel) (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapM_outsClean o ho))
    (by first | decide | decide +kernel) entry

/-! ## `wrapQ`: two calls of the plain leaf `leafP` and one memory entry -/

theorem leafP_kidData : Tools.ShippingQuadComposed.LeafKidData leafP.machineData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel

theorem wrapQ_outsClean : ∀ o ∈ wrapQ.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel
theorem wrapQ_len : wrapQ.machineData.shape.insts.length = 3 := by decide
theorem wrapQ_origin2 : (originAt wrapQ.machineData.shape 2).child? = some (memModule false 4 8) := by first | rfl | decide +kernel

theorem wrapQ_ord_lt : ∀ k (hk : k < wrapQ.machineData.shape.insts.length), k < 2 → (originAt wrapQ.machineData.shape k).child? = none := by
  first | decide | decide +kernel

noncomputable def wqKidOuts : Nat → List OutField := fun k => if k < 2 then leafP.machineData.shape.layout.outs else memOuts 8
noncomputable def wqKidIns : Nat → List Nat := fun k => if k < 2 then Tools.ShippingPortWidthsPure.declWidths leafP.machineData else memIns 4 8

theorem wrapQ_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) :
    KidFactsNC O ``wrapQ wrapQ.machineData.shape.layout.outs (argWidths wrapQ.machineData 5) :=
  memCallee_kidFactsNC O T wrapQ_memCallee
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
    (by first | decide | decide +kernel) (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (wrapQ_outsClean o ho))
    (by first | decide | decide +kernel) entry

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_kidFactsNC
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_kidFactsNC
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_kidFactsNC
