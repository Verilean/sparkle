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

/-! ## the eight hand-applied theorems of `SharedLeafMemKidEntryTest` WITHOUT the premises `closes` / `iface` (NEW theorems; the old ones are unchanged) -/

/-- **`MachineClosesAtStart0` of `topshareM` DERIVED** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_closes0`). -/
theorem topshareM_closes0_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_closes0 O T hA entryL entry₁ entry₂ (wrapM_closesA O T hA entryL) (wrapM3_closesA O T hA entryL) (fun y h => wrapM_ifaceP O T entryL entry₁ h) (fun y h => wrapM3_ifaceP O T entryL entry₂ h)

/-- **`MachineRunJQC` of `topshareM` at depth 1** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_machineRun`). -/
theorem topshareM_machineRun_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_machineRun O T hA entryL entry₁ entry₂ (wrapM_closesA O T hA entryL) (wrapM3_closesA O T hA entryL) (fun y h => wrapM_ifaceP O T entryL entry₁ h) (fun y h => wrapM3_ifaceP O T entryL entry₂ h) entryP hw hcore

/-- **The parent's own run of `topshareM`** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_entry_run`). -/
theorem topshareM_entry_run_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w' : Void IO.RealWorld}
    {y : Res}
    (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = csM.length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < csM.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (csM[j]).c = some y) ∧
      (∀ i (hi : i < csM.length) j (hj : j < csM.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < csM.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (csM[j]).d.shape.insts.length),
          (∃ md, ((csM[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((csM[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((csM[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((csM[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? ((csM[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < csM.length) j (hj : j < csM.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (csM[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (csM[j]).d.shape.insts.length),
          ((csM[i]).d.shape.insts[k₁]).1 = ((csM[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? (((csM[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((csM[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_entry_run O T hA entryL entry₁ entry₂ (wrapM_closesA O T hA entryL) (wrapM3_closesA O T hA entryL) (fun y h => wrapM_ifaceP O T entryL entry₁ h) (fun y h => wrapM3_ifaceP O T entryL entry₂ h) entryP hw h

/-- **The shared-leaf DESIGN CLAUSE for the pair `wrapM`, `wrapM3`** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_closing`): the leaf's cache entry `e` is a module of BOTH callee designs, `CacheCoh` of the end cache. -/
theorem topshareM_shared_leaf_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    {D : Nat}
    (hD : D ≠ 0)
    {t m₀ : Sparkle.IR.AST.Module}
    {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hcl : CacheClosedNM (cv w))
    (hk : KeyTop (cv w))
    (hmd : MemDet (cv w))
    (h1 : (cv w).get? ``wrapM = none)
    (h2 : (cv w).get? ``wrapM3 = none)
    (hr : RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_shared_leaf O T hA entryL entry₁ entry₂ (wrapM_closesA O T hA entryL) (wrapM3_closesA O T hA entryL) hD hw hcl hk hmd h1 h2 hr

/-- **`MachineClosesAtStart0` of `topshareQ` DERIVED** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_closes0`; the plain callee's `MachineClosesAtA` and interface are DERIVED, the memory-bearing callee's are premises). -/
theorem topshareQ_closes0_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_closes0 O T hA hR0 hcl entry₁ entry₂ (wrapQ_closesA O T hA hR0 hcl) (fun y h => wrapQ_ifaceP O T hR0 hcl entry₂ h)

/-- **`MachineRunJQC` of `topshareQ` at depth 1** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_machineRun`). -/
theorem topshareQ_machineRun_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_machineRun O T hA hR0 hcl entry₁ entry₂ (wrapQ_closesA O T hA hR0 hcl) (fun y h => wrapQ_ifaceP O T hR0 hcl entry₂ h) entryP hw hcore

/-- **The parent's own run of `topshareQ`** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_entry_run`). -/
theorem topshareQ_entry_run_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld}
    {y : Res}
    (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational ``topshareQ) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = csQ.length ∧
      closeLets topshareQ.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareQ.machineData.shape) topshareQ.machineData.shape.insts.length
        topshareQ.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareQ.machineData.shape.insts.map (·.2.1))
        topshareQ.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareQ.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < csQ.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (csQ[j]).c = some y) ∧
      (∀ i (hi : i < csQ.length) j (hj : j < csQ.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < csQ.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (csQ[j]).d.shape.insts.length),
          (∃ md, ((csQ[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((csQ[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((csQ[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((csQ[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? ((csQ[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < csQ.length) j (hj : j < csQ.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (csQ[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (csQ[j]).d.shape.insts.length),
          ((csQ[i]).d.shape.insts[k₁]).1 = ((csQ[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? (((csQ[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((csQ[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_entry_run O T hA hR0 hcl entry₁ entry₂ (wrapQ_closesA O T hA hR0 hcl) (fun y h => wrapQ_ifaceP O T hR0 hcl entry₂ h) entryP hw h

/-- **The shared-leaf DESIGN CLAUSE for the pair `wrapP`, `wrapQ`** (NEW, the premises `closes`/`iface` of the callees with a memory child are DERIVED; hand-applied `nm_closing`): the plain leaf `leafP`'s cache entry is a module of BOTH callee designs (the callee `wrapQ` also holds a memory child). -/
theorem topshareQ_shared_leaf_derived (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl0 : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    {D : Nat}
    (hD : D ≠ 0)
    {t m₀ : Sparkle.IR.AST.Module}
    {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hcl : CacheClosedNM (cv w))
    (hk : KeyTop (cv w))
    (hmd : MemDet (cv w))
    (h1 : (cv w).get? ``wrapP = none)
    (h2 : (cv w).get? ``wrapQ = none)
    (hr : RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules :=
  Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_shared_leaf O T hA hR0 hcl0 entry₁ entry₂ (wrapQ_closesA O T hA hR0 hcl0) hD hw hcl hk hmd h1 h2 hr

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_closesA
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_ifaceP
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_closesA
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM3_closesA
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_ifaceP
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM3_ifaceP
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_closesA
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_ifaceP
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_closes0_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_machineRun_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_entry_run_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_shared_leaf_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_closes0_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_machineRun_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_entry_run_derived
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_shared_leaf_derived
end
