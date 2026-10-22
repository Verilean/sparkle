import Tests.Compiler.SharedLeafMemKidEntryTest
import Tools.ShippingSrm3Callee
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit SRM3).
-- SCOPE (SRM3, residue R1): the A-form memory-aware interface / closing layer of `Tools/ShippingSrm3Iface.lean` + `Tools/ShippingSrm3Callee.lean` HAND-APPLIED to the callees of `Tests/Compiler/SharedLeafMemKidTest.lean`:
--   `leafM` (memory-only: its `MachineClosesAtA` and the interface of its `RealChildA` are DERIVED),
--   `wrapM`, `wrapM3` (each calls `leafM`, which has a memory child), `wrapQ` (calls the plain leaf `leafP` AND a memory child).
-- What is DERIVED here: `MachineClosesAtA` of each callee with a memory child (`wrapM_closesA`, `wrapM3_closesA`, `wrapQ_closesA`) and `ChildIfaceP` of its `RealChildA` results (`wrapM_ifaceP`, `wrapM3_ifaceP`, `wrapQ_ifaceP`),
-- hence the eight hand-applied theorems of `Tests/Compiler/SharedLeafMemKidEntryTest.lean` WITHOUT the premises `closes₁/closes₂/ifaceW1/ifaceW3/ifaceQ` (the `*_derived` theorems; the old ones are unchanged).
-- PREMISES (named): `O`, `T`, `hA`, `MachineDefines` of the parent / callees / leaves (`entryL`, `entry₁`, `entry₂`, `hR0`, `entryP`), `MachineCloses` of the plain leaf `leafP` (`hcl`), the decided data facts.
-- NOT applied: the endpoint (`KidFactsA` / `seq_child_runN` / composed trace) of these callees.  The examples do not make the class complete.  `RealChildA` / `JQC` are histories of past synthesis results, not semantic
-- correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingMemLeafRun Tools.ShippingMemLeafCache Tools.ShippingNmGroup Tools.ShippingNmEntry
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Tools.ShippingSharedLeafHit Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingSharedLeafNL
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingMemCloses Tools.ShippingTopShareRun Tools.ShippingTopShareNoParent
open Tools.ShippingSrm3Callee
open Tools.ShippingInstTagged (originAt)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the name of the built synchronous 4/8 memory module -/
def memNm : String := (memModule false 4 8).1.name

/-! ## `leafM`: all calls are memory entries -/

def lmName : Nat → String := fun _ => memNm
def lmNk : Nat → Nat := fun _ => 4
def lmOuts : Nat → List String := fun _ => ["out"]
def lmNames : Nat → List String := fun _ => [memNm]

theorem leafM_memCallee : MemCalleeData leafM.machineData ``leafM 4 lmName lmNk lmOuts lmNames [memNm] := by
  refine ⟨leafM.machine_ok, leafM.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem leafM_allmem : ∀ k (hk : k < leafM.machineData.shape.insts.length),
    (originAt leafM.machineData.shape k).child?.isSome = true := by
  first | decide | decide +kernel

theorem leafM_none_false {k : Nat} (hk : k < leafM.machineData.shape.insts.length)
    (h : (originAt leafM.machineData.shape k).child? = none) : False := by
  have := leafM_allmem k hk
  rw [h] at this
  exact absurd this (by decide)

theorem leafM_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``leafM leafM.machineData.shape :=
  memCallee_closesA O T hA leafM_memCallee (fun k hk y hn _ => (leafM_none_false hk hn).elim)

theorem leafM_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) {y : Res} (h : RealChildA O ``leafM y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafM) (machNIn leafM.machineData.shape)
      (leafM.machineData.shape.layout.outs.map (·.name)) [memNm] y.1 y.2 :=
  memCallee_ifaceP O T leafM_memCallee (fun _ _ _ k hk y hn _ => (leafM_none_false hk hn).elim) entryL h

/-! ## `wrapM`, `wrapM3`: every call is the memory-bearing leaf `leafM` -/

def wmName : Nat → String := fun _ => Sparkle.IR.ModuleName.ofDecl ``leafM
noncomputable def wmNk : Nat → Nat := fun _ => machNIn leafM.machineData.shape
noncomputable def wmOuts : Nat → List String := fun _ => leafM.machineData.shape.layout.outs.map (·.name)
def wmNames : Nat → List String := fun _ => [memNm]

theorem wrapM_kids : ∀ k (hk : k < wrapM.machineData.shape.insts.length), (wrapM.machineData.shape.insts[k]).1 = ``leafM := by
  first | decide | decide +kernel
theorem wrapM3_kids : ∀ k (hk : k < wrapM3.machineData.shape.insts.length), (wrapM3.machineData.shape.insts[k]).1 = ``leafM := by
  first | decide | decide +kernel

theorem wrapM_memCallee : MemCalleeData wrapM.machineData ``wrapM 4 wmName wmNk wmOuts wmNames namesM := by
  refine ⟨wrapM.machine_ok, wrapM.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem wrapM3_memCallee : MemCalleeData wrapM3.machineData ``wrapM3 4 wmName wmNk wmOuts wmNames namesM := by
  refine ⟨wrapM3.machine_ok, wrapM3.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem wrapM_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape :=
  memCallee_closesA O T hA wrapM_memCallee (fun k hk y _ hre => by
    rw [wrapM_kids k hk] at hre
    exact leafM_ifaceP O T entryL hre)

theorem wrapM3_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape :=
  memCallee_closesA O T hA wrapM3_memCallee (fun k hk y _ hre => by
    rw [wrapM3_kids k hk] at hre
    exact leafM_ifaceP O T entryL hre)

/-- **`ChildIfaceP` of a `RealChildA` of `wrapM`** (the premise `ifaceW1` of the hand-applied theorems, DERIVED) -/
theorem wrapM_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) {y : Res} (h : RealChildA O ``wrapM y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape)
      (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2 :=
  memCallee_ifaceP O T wrapM_memCallee (fun m' c' _ k hk y _ hre => by
    rw [wrapM_kids k hk] at hre
    exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre) entry h

/-- **`ChildIfaceP` of a `RealChildA` of `wrapM3`** (the premise `ifaceW3`, DERIVED) -/
theorem wrapM3_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) {y : Res} (h : RealChildA O ``wrapM3 y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape)
      (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2 :=
  memCallee_ifaceP O T wrapM3_memCallee (fun m' c' _ k hk y _ hre => by
    rw [wrapM3_kids k hk] at hre
    exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre) entry h

/-! ## `wrapQ`: two calls of the plain leaf `leafP` and one memory entry -/

def wqName : Nat → String := fun k => if k < 2 then Sparkle.IR.ModuleName.ofDecl ``leafP else memNm
noncomputable def wqNk : Nat → Nat := fun k => if k < 2 then Tools.ShippingQuadLeafGeneric.leafNk leafP.machineData else 4
noncomputable def wqOuts : Nat → List String := fun k => if k < 2 then leafP.machineData.shape.layout.outs.map (·.name) else ["out"]
def wqNames : Nat → List String := fun k => if k < 2 then [] else [memNm]

theorem wrapQ_memCallee : MemCalleeData wrapQ.machineData ``wrapQ 5 wqName wqNk wqOuts wqNames namesQ := by
  refine ⟨wrapQ.machine_ok, wrapQ.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

/-- an entry of `wrapQ` that builds no module is a call of `leafP` at index `< 2` -/
theorem wrapQ_ord : ∀ k (hk : k < wrapQ.machineData.shape.insts.length), (originAt wrapQ.machineData.shape k).child? = none →
    k < 2 ∧ (wrapQ.machineData.shape.insts[k]).1 = ``leafP := by
  first | decide | decide +kernel

theorem wrapQ_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape :=
  memCallee_closesA O T hA wrapQ_memCallee (fun k hk y hn hre => by
    obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
    rw [hnm] at hre
    simp only [wqName, wqNk, wqOuts, wqNames, if_pos hk2]
    exact leafKid_ifaceP O leafP_data hR0 hcl hre)

/-- **`ChildIfaceP` of a `RealChildA` of `wrapQ`** (the premise `ifaceQ`, DERIVED) -/
theorem wrapQ_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) {y : Res} (h : RealChildA O ``wrapQ y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape)
      (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2 :=
  memCallee_ifaceP O T wrapQ_memCallee (fun m' c' _ k hk y hn hre => by
    obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
    rw [hnm] at hre
    simp only [wqName, wqNk, wqOuts, wqNames, if_pos hk2]
    exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre) entry h

end Tests.Compiler.SharedLeafMemKidIfaceTest
end
