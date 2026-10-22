import Tests.Compiler.SharedLeafMemKidTest
import Tools.ShippingMemLeafRun
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SRM1): t3 exit 0 (dev run); the final-SHA rebuild is in REPORT-SRM1.md.
-- SCOPE (SRM1, step 2): the memory-aware run layer of `Tools/ShippingMemLeafRun.lean` HAND-APPLIED to the example of `Tests/Compiler/SharedLeafMemKidTest.lean`: the shared leaf `leafM` (ONE memory child, the
-- synchronous 4/8 memory), the callees `wrapM`, `wrapM3` (each calls the leaf twice), the parent `topshareM`.  What is applied: the one-step contract `StepNM` of the leaf (`memLeaf_stepNM`; the leaf's
-- `MachineClosesAtA` is DERIVED from decided data), of each callee (`calleeOverLeaf_stepNM`; `MachineClosesAtA` of the callee is a PREMISE: residue R1), and the parent's closing over the two callees
-- (`closing_nm`: `CacheCoh` of the end cache from `CacheClosedNM` + `KeyTop` + `MemDet`).  NOT applied (residue, see REPORT-SRM1.md): the interface / `KidFactsA` / `seq_child_runN` side of a machine with a
-- memory child on the `RealChildA` boundary; the parent's endpoint.  The example does not make the class complete.  `RealChildA` / `JQC` are histories of past synthesis results, not semantic correctness.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.SharedLeafMemKidRunTest
open Tests.Compiler.SharedLeafMemKidTest
open Tools.ShippingMemLeafRun Tools.ShippingMemLeafCache
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Tools.ShippingSharedLeafHit Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA

/-! ## the decided data of the memory leaf `leafM` (nDecl 4, memory 4/8, synchronous read) -/

theorem leafM_entry : ∀ (k : Nat) (hk : k < leafM.machineData.shape.insts.length),
    (leafM.machineData.shape.insts[k]).1 = Sparkle.Compiler.MachMemory.memChildName false 4 8 := by
  first | decide | decide +kernel

theorem mem_isMem_sync : Sparkle.Compiler.MachMemory.memChild? (Sparkle.Compiler.MachMemory.memChildName false 4 8) =
    some (Sparkle.Compiler.MachMemory.memModule false 4 8) := by first | rfl | decide

theorem leafM_outChars : ∀ o ∈ leafM.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem leafM_memOnly : Tools.ShippingMemOnly.MemOnlyData leafM.machineData 4 4 8 :=
  Tools.ShippingMemOnly.MemOnlyData.mk leafM.machine_ok leafM.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k hk => Exists.intro false ((congrArg Sparkle.Compiler.MachMemory.memChild? (leafM_entry k hk)).trans mem_isMem_sync))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (leafM_outChars o ho))
    (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)

theorem leafM_closeData : Tools.ShippingMemOnlyCloses.MemOnlyCloseData leafM.machineData :=
  Tools.ShippingMemOnlyCloses.MemOnlyCloseData.mk (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)

theorem leafM_cne : ∀ k (hk : k < leafM.machineData.shape.insts.length), (leafM.machineData.shape.insts[k]).1 ≠ ``leafM := by
  first | decide | decide +kernel

/-! ## the decided data of the callees -/

theorem wrapM_tags : ∀ x ∈ wrapM.machineData.shape.instTagged, x.2.child? = none ∧ x.1 = ``leafM := by
  first | decide | decide +kernel
theorem wrapM3_tags : ∀ x ∈ wrapM3.machineData.shape.instTagged, x.2.child? = none ∧ x.1 = ``leafM := by
  first | decide | decide +kernel
theorem wrapM_cne : ∀ k (hk : k < wrapM.machineData.shape.insts.length), (wrapM.machineData.shape.insts[k]).1 ≠ ``wrapM := by
  first | decide | decide +kernel
theorem wrapM3_cne : ∀ k (hk : k < wrapM3.machineData.shape.insts.length), (wrapM3.machineData.shape.insts[k]).1 ≠ ``wrapM3 := by
  first | decide | decide +kernel
theorem wrapM_calls : wrapM.machineData.callsOk 4 = true := by first | decide | decide +kernel
theorem wrapM3_calls : wrapM3.machineData.callsOk 4 = true := by first | decide | decide +kernel
theorem wrapM_slots : wrapM.machineData.ss.length = wrapM.machineData.shape.layout.slots.length := by first | decide | decide +kernel
theorem wrapM3_slots : wrapM3.machineData.ss.length = wrapM3.machineData.shape.layout.slots.length := by first | decide | decide +kernel
theorem wrapM_domB : ∀ b ∈ wrapM.machineData.shape.binders.drop 4, b.2 ≠ .domain := by first | decide | decide +kernel
theorem wrapM3_domB : ∀ b ∈ wrapM3.machineData.shape.binders.drop 4, b.2 ≠ .domain := by first | decide | decide +kernel

/-- the names a callee's step may add: the leaf and its memory placeholder -/
def Gs0 : List Lean.Name := [``leafM, Sparkle.Compiler.MachMemory.memChildName false 4 8]

theorem wrapM_notin : ``wrapM ∉ leafM.machineData.shape.insts.map (·.1) := by first | decide | decide +kernel
theorem wrapM3_notin : ``wrapM3 ∉ leafM.machineData.shape.insts.map (·.1) := by first | decide | decide +kernel

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## the one-step contracts (hand-applied) -/

theorem leafM_step (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D ``leafM (leafM.machineData.shape.insts.map (·.1)) :=
  memLeaf_stepNM O T hA leafM_memOnly leafM_closeData leafM_cne entry

theorem wrapM_step (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D ``wrapM
      (wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1)) :=
  calleeOverLeaf_stepNM O hA _ wrapM_notin wrapM.machineData wrapM.machine_ok wrapM.machine_body wrapM_calls wrapM_slots wrapM_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide)) (fun h0 => absurd (congrArg List.length h0) (by decide))
    wrapM_tags (leafM_step O T hA entryL) wrapM_cne entry closes

theorem wrapM3_step (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D ``wrapM3
      (wrapM3.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1)) :=
  calleeOverLeaf_stepNM O hA _ wrapM3_notin wrapM3.machineData wrapM3.machine_ok wrapM3.machine_body wrapM3_calls wrapM3_slots wrapM3_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide)) (fun h0 => absurd (congrArg List.length h0) (by decide))
    wrapM3_tags (leafM_step O T hA entryL) wrapM3_cne entry closes

theorem topshareM_tags : ∀ x ∈ topshareM.machineData.shape.instTagged, x.2.child? = none ∧ (x.1 = ``wrapM ∨ x.1 = ``wrapM3) := by
  first | decide | decide +kernel
theorem wrapM_sub : ∀ x ∈ wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1), x ∈ Gs0 := by
  first | decide | decide +kernel
theorem wrapM3_sub : ∀ x ∈ wrapM3.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1), x ∈ Gs0 := by
  first | decide | decide +kernel

/-- **The parent's closing over the two callees of the memory leaf**, hand-applied `closing_nm`. -/
theorem topshareM_closing (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape)
    {D : Nat} (hD : D ≠ 0) {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w) (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w))
    (hr : RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields children (m₀, d₀) ∧
      children.length = topshareM.machineData.shape.insts.length ∧
      (∀ k (hk : k < topshareM.machineData.shape.insts.length), ∃ y, children[k]? = some y ∧
        (cv w').get? (topshareM.machineData.shape.insts[k]).1 = some y) ∧
      JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      CacheExtends (cv w) (cv w') ∧
      (∀ i (_hi : i < children.length) j (_hj : j < children.length) (y y' : Res), children[i]? = some y →
        children[j]? = some y' → ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) :=
  closing_nm O hA Gs0 (fun x hx => by
    obtain ⟨h1, h2⟩ := topshareM_tags x hx
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · rw [h2]; exact (wrapM_step O T hA entryL entry₁ closes₁ D hD).mono wrapM_sub
    · rw [h2]; exact (wrapM3_step O T hA entryL entry₂ closes₂ D hD).mono wrapM3_sub) hw hcl hk hmd hr

/-! ## the FULL forall-types, written by hand and compared with `isDefEq`; type-correct mutations are REJECTED -/

/-- expected full type of `leafM_step` -/
@[reducible] def LeafStepWith (cn : Lean.Name) (gs : List Lean.Name) (hyp : Nat → Prop) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    ∀ D, hyp D → StepNM (mref := mref) (cref := cref) O mctx cctx D cn gs

@[reducible] def LeafStepFull : Prop := LeafStepWith ``leafM (leafM.machineData.shape.insts.map (·.1)) (· ≠ 0)
/-- MUTATION: the step is for `wrapM` -/
@[reducible] def LeafStepName : Prop := LeafStepWith ``wrapM (leafM.machineData.shape.insts.map (·.1)) (· ≠ 0)
/-- MUTATION: empty growth set -/
@[reducible] def LeafStepGs : Prop := LeafStepWith ``leafM [] (· ≠ 0)
/-- MUTATION: depth 0 -/
@[reducible] def LeafStepD0 : Prop := LeafStepWith ``leafM (leafM.machineData.shape.insts.map (·.1)) (· = 0)
/-- MUTATION: the reflection premise is for `wrapM` -/
@[reducible] def LeafStepEntry : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``wrapM leafM.machineData.shape →
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D ``leafM (leafM.machineData.shape.insts.map (·.1))
/-- MUTATION: the reflection premise dropped -/
@[reducible] def LeafStepNoEntry : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True → ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D ``leafM (leafM.machineData.shape.insts.map (·.1))

/-- expected full type of `wrapM_step` (the callee's `MachineClosesAtA` is a named premise) -/
@[reducible] def WrapStepWith (cn : Lean.Name) (gs : List Lean.Name) (hyp : Nat → Prop) (closesDecl : Lean.Name) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx closesDecl wrapM.machineData.shape →
    ∀ D, hyp D → StepNM (mref := mref) (cref := cref) O mctx cctx D cn gs

@[reducible] def WrapStepFull : Prop := WrapStepWith ``wrapM (wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1)) (· ≠ 0) ``wrapM
/-- MUTATION: growth set without the leaf -/
@[reducible] def WrapStepGs : Prop := WrapStepWith ``wrapM (wrapM.machineData.shape.insts.map (·.1)) (· ≠ 0) ``wrapM
/-- MUTATION: the closing premise is for `wrapM3` -/
@[reducible] def WrapStepCloses : Prop := WrapStepWith ``wrapM (wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1)) (· ≠ 0) ``wrapM3
/-- MUTATION: depth 0 -/
@[reducible] def WrapStepD0 : Prop := WrapStepWith ``wrapM (wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1)) (· = 0) ``wrapM
/-- MUTATION: the step is for `wrapM3` -/
@[reducible] def WrapStepName : Prop := WrapStepWith ``wrapM3 (wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1)) (· ≠ 0) ``wrapM
/-- MUTATION: the closing premise dropped -/
@[reducible] def WrapStepNoCloses : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    True → ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D ``wrapM
      (wrapM.machineData.shape.insts.map (·.1) ++ leafM.machineData.shape.insts.map (·.1))

/-- expected full type of `topshareM_closing` -/
@[reducible] def ClosingWith (stClass : Nat → Prop) (clN : Lean.Name) (cohP : Std.HashMap Lean.Name Res → Prop) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx clN wrapM3.machineData.shape →
    ∀ {D : Nat}, stClass D → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
      {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld},
      JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) →
      RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' →
      ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
          topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
          topshareM.machineData.shape.instFields children (m₀, d₀) ∧
        children.length = topshareM.machineData.shape.insts.length ∧
        (∀ k (hk : k < topshareM.machineData.shape.insts.length), ∃ y, children[k]? = some y ∧
          (cv w').get? (topshareM.machineData.shape.insts[k]).1 = some y) ∧
        JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ cohP (cv w') ∧
        CacheExtends (cv w) (cv w') ∧
        (∀ i (_hi : i < children.length) j (_hj : j < children.length) (y y' : Res), children[i]? = some y →
          children[j]? = some y' → ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b)

@[reducible] def ClosingFull : Prop := ClosingWith (· ≠ 0) ``wrapM3 CacheCoh
/-- MUTATION: depth 0 -/
@[reducible] def ClosingD0 : Prop := ClosingWith (· = 0) ``wrapM3 CacheCoh
/-- MUTATION: the second closing premise is for `wrapM` -/
@[reducible] def ClosingCloses : Prop := ClosingWith (· ≠ 0) ``wrapM CacheCoh
/-- MUTATION: no coherence in the conclusion -/
@[reducible] def ClosingNoCoh : Prop := ClosingWith (· ≠ 0) ``wrapM3 (fun _ => True)

end Tests.Compiler.SharedLeafMemKidRunTest

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let N := `Tests.Compiler.SharedLeafMemKidRunTest
  let pairs : List (Name × Name × List (Name × String)) :=
    [(N ++ `leafM_step, N ++ `LeafStepFull, [(N ++ `LeafStepName, "step for wrapM"), (N ++ `LeafStepGs, "empty growth set"), (N ++ `LeafStepD0, "depth 0"),
        (N ++ `LeafStepEntry, "reflection of wrapM"), (N ++ `LeafStepNoEntry, "reflection dropped")]),
     (N ++ `wrapM_step, N ++ `WrapStepFull, [(N ++ `WrapStepGs, "growth set without the leaf"), (N ++ `WrapStepCloses, "closing premise of wrapM3"), (N ++ `WrapStepD0, "depth 0"),
        (N ++ `WrapStepName, "step for wrapM3"), (N ++ `WrapStepNoCloses, "closing premise dropped")]),
     (N ++ `topshareM_closing, N ++ `ClosingFull, [(N ++ `ClosingD0, "depth 0"), (N ++ `ClosingCloses, "second closing premise of wrapM"),
        (N ++ `ClosingNoCoh, "no CacheCoh in the conclusion")])]
  for (thm, full, muts) in pairs do
    let gt ← instantiateMVars (← getConstInfo thm).type
    for (e, what) in [(gt, "the theorem's type"), (mkConst full, "the expected full type")] ++ muts.map fun (c, w) => (mkConst c, s!"mutation {w}") do
      if e.hasMVar || e.hasFVar then throwError "SRM1 AUDIT FAILED: metavariables / free variables in {what}"
      Meta.check e
    unless (← withReducible (isDefEq gt (mkConst full))) do
      throwError "SRM1 AUDIT FAILED: the FULL type of {thm} is not definitionally the hand-written {full}"
    for (c, w) in muts do
      if (← withReducible (isDefEq gt (mkConst c))) then throwError "SRM1 AUDIT FAILED: the mutated full type of {thm} ({w}) was ACCEPTED"
    stdAxioms thm
    logInfo m!"SRM1 AUDIT: the full forall-type of {thm} is isDefEq to {full}; {muts.length} type-correct mutations are REJECTED; standard axioms only"

/-! ## closure audit: the memory-aware run layer, no old boundary, no `CacheClosed` clause -/

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let N := `Tests.Compiler.SharedLeafMemKidRunTest
  for thm in [N ++ `leafM_step, N ++ `wrapM_step, N ++ `topshareM_closing] do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM1 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM1 AUDIT FAILED: old boundary / CacheClosed in the closure of {thm}: {bad2}"
    let must : List Name := [``Tools.ShippingMemLeafRun.synthesizeChild_miss_nm, ``Tools.ShippingMemLeafRun.closeLoop_gen, ``Tools.ShippingMemLeafCache.MemDet,
      ``Tools.ShippingLeafMissCoh.CacheClosedNM, ``Tools.ShippingCallsMemA.machineClosesAtA_of_memOnlyData_names]
    for m in (if thm == N ++ `topshareM_closing then ``Tools.ShippingMemLeafRun.closing_nm :: ``Tools.ShippingMemLeafCache.cacheCoh_of_nm :: must else must) do
      unless cl.contains m do throwError "SRM1 AUDIT FAILED: {m} not in the closure of {thm}"
    logInfo m!"SRM1 CLOSURE AUDIT: {thm}: standard axioms; closure {cl.size} constants; no old RefLaws boundary, no `CacheClosed`, no ChildBnd / GenKid / KidFacts; the memory-aware lemmas are in it"

#print axioms Tests.Compiler.SharedLeafMemKidRunTest.leafM_step
#print axioms Tests.Compiler.SharedLeafMemKidRunTest.wrapM_step
#print axioms Tests.Compiler.SharedLeafMemKidRunTest.topshareM_closing

end
