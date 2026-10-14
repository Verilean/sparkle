import Tests.Compiler.GateConeDesignNamesTest
import Tools.ShippingGateTypedFinal

/-! # The seven gate-route parents: `hierTyped` and `designSideB3` derived (worker N, round 14)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignTypedTest`;
not in `Tests.AllTests`). The per-parent walks are written from the round-13
`…_namW` proofs (node for node); the `…_gate_designSVN3` statements are
GENERATED from the round-13 `…_gate_designSVN2` statements (the two
antecedents removed); the old theorems are kept.

Per parent:

* `…_typW` — the typed walk's contract `TypW` of the instantiated body
  (`Tools.ShippingGateTypedWalk`) under a typing `τ` of its sub-expressions:
  `fun _ => 8` (every node is a `BitVec 8` signal) for six parents,
  `cmpτ` (`1` on the comparison root, `8` elsewhere) for `parentCmp`. Input
  leaves by `typW_fvar` with the leaf's typed input port
  (`prepare_lookup_hitB`); `typW_inst` with the callee's port widths from
  `ChildW8` (both input ports and the output port of `childAdd` are 8 bits
  wide: `childAdd_w8`, from `GateChildPorts`);
* `…_walk3` — `DesW ∧ NamW ∧ TypW`;
* `…_gate_designSVN3` — `…_gate_designSVN2` with the antecedents
  `hierTyped (childMap design.modules) b` and `designSideB3 design.modules b`
  REMOVED, derived by `Tools.ShippingGateParentRun.gate_typedFacts` (the
  child facts of every `childAdd` entry incl. `GateChildPorts`,
  `Tools.ShippingFirstGateChild.first_real_ports`).

Premises: exactly those of `…_gate_cone_runK'` (the run, `GateDefines` NOT
ALLOWED, `ChildBnd`, `EntryDefines childAdd`). Antecedent left on the design
part: `DesignSideR` (inputs fit, start-state bounds, children's start states:
run-level width premises, not checks). -/
namespace Sparkle.Tests.Compiler.GateConeDesignTypedTest

section walks
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeTagTest
open Sparkle.Tests.Compiler.GateConeKidTest
open Sparkle.Tests.Compiler.GateConeEntryTest
open Tools.ShippingUnifiedSource
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild RefLaws)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingMixedEntrySoundness (prepare start)

/-- The port widths of `childAdd`: both inputs and the output 8 bits wide. -/
def ChildW8 (m : Sparkle.IR.AST.Module) : Prop :=
  (∀ p ∈ m.inputs, p.ty.bitWidth = 8) ∧ (∀ p ∈ m.outputs, p.ty.bitWidth = 8)

/-- `childAdd`'s port widths, from its `GateChildPorts` facts. -/
theorem childAdd_w8 {m : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGatePorts.GateChildPorts ``childAdd
      (Tools.ShippingFirstGateChild.firstBs `dom [`x, `y] 8) 8 m) : ChildW8 m := by
  refine ⟨fun p hp => ?_, fun p hp => (h.outWidth p hp).2⟩
  have h1 : p.ty ∈ m.inputs.map (·.ty) := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [h.inTys, Tools.ShippingFirstGateChild.firstBs_filter] at h1
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h1
  obtain ⟨nm, -, hnm⟩ := List.mem_map.mp hq
  rw [← hqe, ← hnm]
  try rfl

/-- **The child facts `gate_typedFacts` asks of every `childAdd` entry** of a
`CacheInv` cache (`childAdd_kidN`'s and `first_real_ports`). -/
theorem childAdd_kidT {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {f : Lean.Name}
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue)
    (hne : ``childAdd ≠ f) :
    ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? ``childAdd = some y →
      InstLeafOk (ChildGN ``childAdd mF) 2 y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        Tools.ShippingGatePorts.GateChildPorts ``childAdd
          (Tools.ShippingFirstGateChild.firstBs `dom [`x, `y] 8) 8 y.1 := by
  intro mF hcache y hy
  obtain ⟨h1, h2, h3, -⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.childAdd_kidN centry hne mF hcache y hy
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨h1, h2, h3,
    Tools.ShippingFirstGateChild.first_real_ports centry childAdd_fe_wf (by decide) hreal⟩

/-- `ScalT` of an 8-bit port. -/
theorem scal8 : ScalT (.bitVector 8) 8 := ⟨by decide, Or.inr rfl⟩

/-- The width premise of `typW_inst` for a call of `childAdd`. -/
theorem inst8 {τ : Lean.Expr → Nat} {mF : Std.HashMap Lean.Name Res}
    {argsE : List Lean.Expr} {e : Lean.Expr}
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (hτa : ∀ a ∈ argsE, τ a = 8) (hτe : τ e = 8) :
    ∀ y : Res, mF.get? ``childAdd = some y →
      (∀ pe ∈ y.1.inputs.zip argsE, τ pe.2 = pe.1.ty.bitWidth) ∧
      ∀ p ∈ y.1.outputs, p.ty.bitWidth = τ e := by
  intro y hy
  refine ⟨fun pe hpe => ?_, fun p hp => ?_⟩
  · rw [hτa pe.2 (mem_zip_partsT hpe).2, (hwd y hy).1 pe.1 (mem_zip_partsT hpe).1]
  · rw [hτe]
    exact (hwd y hy).2 p hp

/-- The typing of `parentCmp`'s cone: `1` on the comparison (four arguments),
`8` on the calls (three) and the binders (none). -/
def cmpτ (e : Lean.Expr) : Nat := if e.getAppNumArgs = 4 then 1 else 8

/-! ## The per-parent typed walks -/

theorem parentMix_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentMixBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentMixBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))).context
      G (prepPortsT parentMixBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentMix))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) := by
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentMixBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))
    `a 8 i1 nd (by simp [parentMixBinders])
  obtain ⟨z2, hz2, hz2P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentMixBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))
    `b 8 i2 nd (by simp [parentMixBinders])
  have h2 : 2 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 2) + 1 + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h2).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentMixBody =
      quote (.fvar i0) (fun _ => .fvar i0) (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2))
        parentMixTerm := rfl
  have ck := Tools.ShippingEntrySoundness.op_checks .add (.fvar i0)
    (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
    (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1) 8
  rw [hbody, hfl]
  show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _ _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1))
  refine typW_binary (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_ rfl rfl rfl (by decide) ⟨.add, rfl⟩
  · rw [ck.2.2.2.2.1]
    show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _ _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
    refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf
      (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
    exact absurd ha List.not_mem_nil
  · rw [ck.2.2.2.2.2.1]
    show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _ _
      (.fvar i1)
    exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _

theorem parentMix_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentMixBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentMixBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentMix)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentMixBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))).context
      G (prepInsN parentMixBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentMix))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentMixBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))).context
      G (prepPortsT parentMixBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentMix))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentMix_walk2 L hD tagR hleaf cache ids nd
      len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentMix_walk2 L hD tagR hleaf cache ids nd
      len).2,
    parentMix_typW L hD tagR hleaf hwd cache ids nd len⟩

section twoCalls
open Sparkle.Tests.Compiler.GateConeTwoCallsTest

theorem parentTwoCalls_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentTwoCallsBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (prepPortsT parentTwoCallsBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) := by
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentTwoCallsBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
    `a 8 i1 nd (by simp [parentTwoCallsBinders])
  obtain ⟨z2, hz2, hz2P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentTwoCallsBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
    `b 8 i2 nd (by simp [parentTwoCallsBinders])
  have h2 : 2 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 2) + 1 + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h2).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentTwoCallsBody =
      quote (.fvar i0) (fun _ => .fvar i0) (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2))
        parentMixTerm := rfl
  have ck := Tools.ShippingEntrySoundness.op_checks .add (.fvar i0)
    (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
    (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1) 8
  rw [hbody, hfl]
  show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _ _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1))
  refine typW_binary (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_ rfl rfl rfl (by decide) ⟨.add, rfl⟩
  · rw [ck.2.2.2.2.1]
    show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _ _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
    refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf
      (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
    exact absurd ha List.not_mem_nil
  · rw [ck.2.2.2.2.2.1]
    show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _ _
      (instEN ``childAdd [] (.fvar i0) [.fvar i2, .fvar i1])
    refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i2, .fvar i1]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf
      (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
    exact absurd ha List.not_mem_nil

theorem parentTwoCalls_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentTwoCallsBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (prepInsN parentTwoCallsBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (prepPortsT parentTwoCallsBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentTwoCalls_walk2 L hD tagR hleaf cache ids
      nd len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentTwoCalls_walk2 L hD tagR hleaf cache ids
      nd len).2,
    parentTwoCalls_typW L hD tagR hleaf hwd cache ids nd len⟩

end twoCalls

section repeatS
open Sparkle.Tests.Compiler.GateConeRepeatTest

theorem parentRepeat_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentRepeatBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepPortsT parentRepeatBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) := by
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentRepeatBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
    `a 8 i1 nd (by simp [parentRepeatBinders])
  obtain ⟨z2, hz2, hz2P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentRepeatBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
    `b 8 i2 nd (by simp [parentRepeatBinders])
  have h2 : 2 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 2) + 1 + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h2).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentRepeatBody =
      quote (.fvar i0) (fun _ => .fvar i0) (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2))
        repeatTerm := rfl
  have ck := Tools.ShippingEntrySoundness.op_checks .add (.fvar i0)
    (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
    (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0) 8
  have leafT : TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip [i0, i1, i2])
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepPortsT parentRepeatBinders [i0, i1, i2] cache
        (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
      (fun _ => 8)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) := by
    refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf
      (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
    exact absurd ha List.not_mem_nil
  rw [hbody, hfl]
  show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _ _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0))
  refine typW_binary (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_ rfl rfl rfl (by decide) ⟨.add, rfl⟩
  · rw [ck.2.2.2.2.1]
    exact leafT
  · rw [ck.2.2.2.2.2.1]
    exact leafT

theorem parentRepeat_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentRepeatBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentRepeat)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepInsN parentRepeatBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepPortsT parentRepeatBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentRepeat_walk2 L hD tagR hleaf cache ids
      nd len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentRepeat_walk2 L hD tagR hleaf cache ids
      nd len).2,
    parentRepeat_typW L hD tagR hleaf hwd cache ids nd len⟩

end repeatS

section cmp
open Sparkle.Tests.Compiler.GateConeCmpTest

theorem parentCmp_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentCmpBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentCmpBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).context
      G (prepPortsT parentCmpBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentCmp)) cmpτ
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) := by
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentCmpBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
    `a 8 i1 nd (by simp [parentCmpBinders])
  obtain ⟨z2, hz2, hz2P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentCmpBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
    `b 8 i2 nd (by simp [parentCmpBinders])
  have h2 : 2 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 2) + 1 + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h2).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentCmpBody =
      Tools.ShippingBoolSourceSoundness.compareE .ult (.fvar i0) 8
        (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
        (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1) := rfl
  -- the typing: `8` on the call and the binder, `1` on the comparison
  have hτ1 : cmpτ (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) = 8 := rfl
  have hτf1 : cmpτ (.fvar i1) = 8 := rfl
  have hτf2 : cmpτ (.fvar i2) = 8 := rfl
  have hτc : cmpτ (Tools.ShippingBoolSourceSoundness.compareE .ult (.fvar i0) 8
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1)) = 1 := rfl
  have hs1 : ScalT (.bitVector 8) (cmpτ (.fvar i1)) := by
    rw [hτf1]
    exact scal8
  have hs2 : ScalT (.bitVector 8) (cmpτ (.fvar i2)) := by
    rw [hτf2]
    exact scal8
  rw [hbody, hfl]
  refine typW_compare (tenv := envR) L hD (translateFuelLimit - 2 + 1) ?_ ?_ hτ1 hτf1 hτc
  · show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _ _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
    refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf
      (inst8 hwd ?_ hτ1) ?_
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hτf1
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hτf2
      exact absurd ha List.not_mem_nil
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact typW_fvar (tenv := envR) L hz1 hz1P hs1 _
      rcases List.mem_cons.mp ha with rfl | ha
      · exact typW_fvar (tenv := envR) L hz2 hz2P hs2 _
      exact absurd ha List.not_mem_nil
  · show TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _ _
      (.fvar i1)
    exact typW_fvar (tenv := envR) L hz1 hz1P hs1 _

theorem parentCmp_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentCmpBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentCmpBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentCmp)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentCmpBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).context
      G (prepInsN parentCmpBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentCmpBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).context
      G (prepPortsT parentCmpBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentCmp)) cmpτ
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentCmp_walk2 L hD tagR hleaf cache ids nd
      len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentCmp_walk2 L hD tagR hleaf cache ids nd
      len).2,
    parentCmp_typW L hD tagR hleaf hwd cache ids nd len⟩

end cmp

section use
open Sparkle.Tests.Compiler.GateConeUseTest
open Sparkle.Tests.Compiler.GateParentRunGTest (parentUseBody)

theorem parentUse_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentUseBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentUseBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))).context
      G (prepPortsT parentUseBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentUse))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) := by
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentUseBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))
    `a 8 i1 nd (by simp [parentUseBinders])
  obtain ⟨z2, hz2, hz2P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentUseBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))
    `b 8 i2 nd (by simp [parentUseBinders])
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentUseBody =
      instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2] := rfl
  rw [hbody, hfl]
  refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 1) rfl rfl rfl tagR hleaf
    (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
  exact absurd ha List.not_mem_nil

theorem parentUse_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentUseBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentUseBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentUse)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentUseBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))).context
      G (prepInsN parentUseBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentUse))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentUseBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))).context
      G (prepPortsT parentUseBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentUse))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentUse_walk2 L hD tagR hleaf cache ids nd
      len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentUse_walk2 L hD tagR hleaf cache ids nd
      len).2,
    parentUse_typW L hD tagR hleaf hwd cache ids nd len⟩

end use

section wrap
open Sparkle.Tests.Compiler.GateConeWrapAddTest

theorem wrapAdd_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapAddBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapAddBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).context
      G (prepPortsT wrapAddBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  obtain ⟨z0, hz0, hz0P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (wrapAddBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
    `a 8 i0 nd (by simp [wrapAddBinders])
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (wrapAddBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
    `b 8 i1 nd (by simp [wrapAddBinders])
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1].map Lean.Expr.fvar).toArray 0 wrapAddBody =
      instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain [])
        [.fvar i0, .fvar i1] := rfl
  rw [hbody, hfl]
  refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := [])
    (dom := .const ``Sparkle.Core.Domain.defaultDomain []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR hleaf
    (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz0 hz0P scal8 _
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
  exact absurd ha List.not_mem_nil

theorem wrapAdd_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapAddBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapAddBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).context
      G (Sparkle.IR.ModuleName.ofDecl ``wrapAdd)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapAddBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).context
      G (prepInsN wrapAddBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapAddBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).context
      G (prepPortsT wrapAddBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.wrapAdd_walk2 L hD tagR hleaf cache ids nd
      len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.wrapAdd_walk2 L hD tagR hleaf cache ids nd
      len).2,
    wrapAdd_typW L hD tagR hleaf hwd cache ids nd len⟩

end wrap

section nested
open Sparkle.Tests.Compiler.GateConeNestedTest

theorem parentNested_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentNestedBinders.length) :
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepPortsT parentNestedBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentNested))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) := by
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentNestedBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))
    `a 8 i1 nd (by simp [parentNestedBinders])
  obtain ⟨z2, hz2, hz2P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (parentNestedBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))
    `b 8 i2 nd (by simp [parentNestedBinders])
  have h2 : 2 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 2) + 1 + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h2).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentNestedBody =
      instEN ``childAdd [] (.fvar i0)
        [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2] := rfl
  have inner : TypW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip [i0, i1, i2])
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepPortsT parentNestedBinders [i0, i1, i2] cache
        (Sparkle.IR.ModuleName.ofDecl ``parentNested))
      (fun _ => 8)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) := by
    refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf
      (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz1 hz1P scal8 _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
    exact absurd ha List.not_mem_nil
  rw [hbody, hfl]
  refine typW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2]) L hD
    (translateFuelLimit - 2 + 1) rfl rfl rfl tagR hleaf
    (inst8 (e := Lean.Expr.bvar 0) hwd (fun _ _ => rfl) rfl) ?_
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact inner
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz2 hz2P scal8 _
  exact absurd ha List.not_mem_nil

theorem parentNested_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``childAdd = some y → ChildW8 y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentNestedBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentNested)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepInsN parentNestedBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentNested))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) ∧
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepPortsT parentNestedBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentNested))
      (fun _ => 8)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) :=
  ⟨(Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentNested_walk2 L hD tagR hleaf cache ids
      nd len).1,
    (Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentNested_walk2 L hD tagR hleaf cache ids
      nd len).2,
    parentNested_typW L hD tagR hleaf hwd cache ids nd len⟩

end nested

end walks

/-! ## The design level (generated) -/

section svn3
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeKidTest
open Sparkle.Tests.Compiler.GateConeEntryTest
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingGateDesignLift (DesignHasChild PostKeeps OptKeepsOut DesignSide
  gate_designSV_of_steps)

/-- **`parentMix` at the design level, `hierTyped` and `designSideB3` derived**:
`parentMix_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `(fun _ => 8)`). Left: `DesignSideR`. -/
theorem parentMix_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentMix) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentMix parentMixBinders parentMixBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentMixObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (parentMixBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentMix)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentMixBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentMix))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentMixBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentMix))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentMix aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentMix_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      parentMix_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeTagTest.parentMix_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

/-- **`parentTwoCalls` at the design level, `hierTyped` and `designSideB3` derived**:
`parentTwoCalls_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `(fun _ => 8)`). Left: `DesignSideR`. -/
theorem parentTwoCalls_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentTwoCalls) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentTwoCalls Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders
      Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeTwoCallsTest.ParentTwoCallsObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentTwoCalls aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentTwoCalls_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      parentTwoCalls_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

/-- **`parentRepeat` at the design level, `hierTyped` and `designSideB3` derived**:
`parentRepeat_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `(fun _ => 8)`). Left: `DesignSideR`. -/
theorem parentRepeat_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentRepeat) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentRepeat Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders
      Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeRepeatTest.ParentRepeatObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentRepeat)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentRepeat aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentRepeat_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      parentRepeat_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeat_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

/-- **`parentCmp` at the design level, `hierTyped` and `designSideB3` derived**:
`parentCmp_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `cmpτ`). Left: `DesignSideR`. -/
theorem parentCmp_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentCmp) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentCmp Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders
      Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeCmpTest.ParentCmpObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentCmp)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val j)) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentCmp_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    cmpτ hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      parentCmp_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

/-- **`parentUse` at the design level, `hierTyped` and `designSideB3` derived**:
`parentUse_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `(fun _ => 8)`). Left: `DesignSideR`. -/
theorem parentUse_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentUse) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentUse parentUseBinders
      Sparkle.Tests.Compiler.GateParentRunGTest.parentUseBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeUseTest.ParentUseObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (parentUseBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentUse)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentUseBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentUse))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentUseBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentUse))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentUse aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentUse_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      parentUse_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeUseTest.parentUse_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

/-- **`wrapAdd` at the design level, `hierTyped` and `designSideB3` derived**:
`wrapAdd_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `(fun _ => 8)`). Left: `DesignSideR`. -/
theorem wrapAdd_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapAdd) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapAdd wrapAddBinders
      Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAddBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeWrapAddTest.WrapAddObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ (aS bS : Signal defaultDomain (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (wrapAddBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapAdd)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (wrapAddBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).bits i0 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (wrapAddBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).bits i1 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((wrapAdd aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.wrapAdd_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      wrapAdd_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

/-- **`parentNested` at the design level, `hierTyped` and `designSideB3` derived**:
`parentNested_gate_designSVN2` with both antecedents discharged
(`Tools.ShippingGateParentRun.gate_typedFacts`, typing `(fun _ => 8)`). Left: `DesignSideR`. -/
theorem parentNested_gate_designSVN3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentNested) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentNested parentNestedBinders
      Sparkle.Tests.Compiler.GateConeNestedTest.parentNestedBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ Sparkle.Tests.Compiler.GateConeNestedTest.ParentNestedObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ {D : DomainConfig} (aS bS : Signal D (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (parentNestedBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentNested)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentNestedBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentNested))).bits i1 =
              some ⟨8, aS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (parentNestedBinders.zip [i0, i1, i2])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``parentNested))).bits i2 =
              some ⟨8, bS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          ∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((parentNested aS bS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD⟩ :=
    Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentNested_gate_designSVN2 hr gdef bnd centry
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFacts (c := ``childAdd) (n := 2)
    (fun _ => 8) hr gdef bnd (childAdd_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      parentNested_walk3 L' hD' (Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => childAdd_w8 (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, hD hty hDB⟩

end svn3

end Sparkle.Tests.Compiler.GateConeDesignTypedTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentMix_gate_designSVN3
#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentTwoCalls_gate_designSVN3
#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentRepeat_gate_designSVN3
#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentCmp_gate_designSVN3
#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentUse_gate_designSVN3
#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.wrapAdd_gate_designSVN3
#print axioms Sparkle.Tests.Compiler.GateConeDesignTypedTest.parentNested_gate_designSVN3
