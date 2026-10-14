import Tests.Compiler.GateConeDesignCombTest
import Tools.ShippingGateNamesFinal

/-! # The seven gate-route parents: `combSideB` narrowed to `hierTyped` (worker N, round 13)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignNamesTest`;
not in `Tests.AllTests`). The per-parent parts are GENERATED from the
round-11 `…_desW` proofs (`Tests/Compiler/GateConeDesignWalkTest.lean`) and
the round-12 `…_gate_designSVN` statements
(`Tests/Compiler/GateConeDesignCombTest.lean`); the old theorems are kept.

Per parent:

* `…_namW` — the naming walk's contract `NamW` of the instantiated body
  (`Tools.ShippingGateNamesWalk`), node for node the round-11 `…_desW`
  (input leaves by `namW_fvar` with the leaf's input port,
  `prepare_lookup_hitI`; `namW_inst`, `namW_binary`, `namW_compare`);
* `…_walk2` — `DesW ∧ NamW` (the round-11 `…_desW` and `…_namW`);
* `…_gate_designSVN2` — `…_gate_designSVN` with the antecedent
  `combSideB design.modules b` REPLACED by its sixth conjunct
  `hierTyped (childMap design.modules) b`: the other five (`linkedWF`,
  distinct instance names, `noSelfRead`, `outsExtracted`, `kidsComb`) are
  derived from the run by `Tools.ShippingGateParentRun.gate_combFacts`; and
  `designSideB` REPLACED by `designSideB3` (its fourth conjunct, the
  children's check `kidsPass … (kidCheck … 0)`, derived: every instance's
  child is the cache's `childAdd` entry, a first-gate child,
  `Tools.ShippingFirstGateChild.first_child_kidK`).

Premises: exactly those of `…_gate_cone_runK'` (the run, `GateDefines` NOT
ALLOWED, `ChildBnd`, `EntryDefines childAdd`). Antecedents left on the design
part: `hierTyped`, `designSideB3` (`seqCheck`, `seqNames` widths of `b`,
`portsMatchB` of the shipped module), `DesignSideR` (all outside ALLOWED). -/
namespace Sparkle.Tests.Compiler.GateConeDesignNamesTest

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
open Tools.ShippingFirstGateKid (ownChild kidFacts_of_first')
open Tools.ShippingGateDesignLift (DesignHasChild)
open Tools.ShippingMixedEntrySoundness (prepare start)

/-- **The child facts `gate_combFacts` asks of every `childAdd` entry** of a
`CacheInv` cache (`childAdd_leafOk`, `first_child_combN`,
`childAdd_name_ne`). -/
theorem childAdd_kidN {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {f : Lean.Name}
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue)
    (hne : ``childAdd ≠ f) :
    ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? ``childAdd = some y →
      InstLeafOk (ChildGN ``childAdd mF) 2 y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (k : Nat),
          Tools.ShippingChecksDesign.kidCheck C k y.1 = true := by
  intro mF hcache y hy
  have hl := Sparkle.Tests.Compiler.GateConeDesignWalkTest.childAdd_leafOk centry hcache y hy
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  refine ⟨⟨⟨y, hy, rfl⟩, hl.2⟩, ?_,
    Sparkle.Tests.Compiler.GateConeDesignWalkTest.childAdd_name_ne centry hreal hne, ?_⟩
  · exact first_child_combN centry childAdd_fe_wf (by decide) hreal
  · exact Tools.ShippingFirstGateChild.first_child_kidK centry childAdd_fe_wf (by decide) hreal

/-! ## The per-parent naming walks (generated) -/

theorem parentMix_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentMixBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentMixBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))).context
      G (prepInsN parentMixBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentMix))
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
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentMixBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))
    `a (.bits 8) i1 nd (by simp [parentMixBinders]) (by decide)
  obtain ⟨z2, hz2, hz2I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentMixBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))
    `b (.bits 8) i2 nd (by simp [parentMixBinders]) (by decide)
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
  show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1))
  refine namW_binary (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_
  · rw [ck.2.2.2.2.1]
    show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
    refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · rcases k with _ | k
      · exact namW_fvar (tenv := envR) L hz2 hz2I _
      · exact absurd hk (by simp)
  · rw [ck.2.2.2.2.2.1]
    show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (.fvar i1)
    exact namW_fvar (tenv := envR) L hz1 hz1I _

theorem parentMix_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
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
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentMix_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    parentMix_namW L hD tagR hleaf cache ids nd len⟩

section twoCalls
open Sparkle.Tests.Compiler.GateConeTwoCallsTest

theorem parentTwoCalls_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentTwoCallsBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (prepInsN parentTwoCallsBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
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
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentTwoCallsBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
    `a (.bits 8) i1 nd (by simp [parentTwoCallsBinders]) (by decide)
  obtain ⟨z2, hz2, hz2I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentTwoCallsBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
    `b (.bits 8) i2 nd (by simp [parentTwoCallsBinders]) (by decide)
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
  show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1))
  refine namW_binary (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_
  · rw [ck.2.2.2.2.1]
    show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
    refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · rcases k with _ | k
      · exact namW_fvar (tenv := envR) L hz2 hz2I _
      · exact absurd hk (by simp)
  · rw [ck.2.2.2.2.2.1]
    show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i2, .fvar i1])
    refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i2, .fvar i1]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz2 hz2I _
    · rcases k with _ | k
      · exact namW_fvar (tenv := envR) L hz1 hz1I _
      · exact absurd hk (by simp)

theorem parentTwoCalls_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentTwoCallsBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (prepInsN parentTwoCallsBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentTwoCalls_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    parentTwoCalls_namW L hD tagR hleaf cache ids nd len⟩

end twoCalls

section repeatS
open Sparkle.Tests.Compiler.GateConeRepeatTest

theorem parentRepeat_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentRepeatBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepInsN parentRepeatBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
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
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentRepeatBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
    `a (.bits 8) i1 nd (by simp [parentRepeatBinders]) (by decide)
  obtain ⟨z2, hz2, hz2I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentRepeatBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
    `b (.bits 8) i2 nd (by simp [parentRepeatBinders]) (by decide)
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
  have leafW : NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip [i0, i1, i2])
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepInsN parentRepeatBinders [i0, i1, i2] cache (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) := by
    refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · rcases k with _ | k
      · exact namW_fvar (tenv := envR) L hz2 hz2I _
      · exact absurd hk (by simp)
  rw [hbody, hfl]
  show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0))
  refine namW_binary (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_
  · rw [ck.2.2.2.2.1]
    exact leafW
  · rw [ck.2.2.2.2.2.1]
    exact leafW

theorem parentRepeat_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentRepeatBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentRepeat)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (prepInsN parentRepeatBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentRepeat_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    parentRepeat_namW L hD tagR hleaf cache ids nd len⟩

end repeatS

section cmp
open Sparkle.Tests.Compiler.GateConeCmpTest

theorem parentCmp_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentCmpBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentCmpBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).context
      G (prepInsN parentCmpBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
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
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentCmpBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
    `a (.bits 8) i1 nd (by simp [parentCmpBinders]) (by decide)
  obtain ⟨z2, hz2, hz2I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentCmpBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
    `b (.bits 8) i2 nd (by simp [parentCmpBinders]) (by decide)
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
  rw [hbody, hfl]
  refine namW_compare (tenv := envR) L hD (translateFuelLimit - 2 + 1)
    ?_ ?_
  · show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
    refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · rcases k with _ | k
      · exact namW_fvar (tenv := envR) L hz2 hz2I _
      · exact absurd hk (by simp)
  · show NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (.fvar i1)
    exact namW_fvar (tenv := envR) L hz1 hz1I _

theorem parentCmp_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
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
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentCmp_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    parentCmp_namW L hD tagR hleaf cache ids nd len⟩

end cmp

section use
open Sparkle.Tests.Compiler.GateConeUseTest
open Sparkle.Tests.Compiler.GateParentRunGTest (parentUseBody)

theorem parentUse_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentUseBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentUseBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))).context
      G (prepInsN parentUseBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentUse))
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
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentUseBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))
    `a (.bits 8) i1 nd (by simp [parentUseBinders]) (by decide)
  obtain ⟨z2, hz2, hz2I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentUseBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))
    `b (.bits 8) i2 nd (by simp [parentUseBinders]) (by decide)
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
  refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 1) rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact namW_fvar (tenv := envR) L hz1 hz1I _
  · rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz2 hz2I _
    · exact absurd hk (by simp)

theorem parentUse_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
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
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentUse_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    parentUse_namW L hD tagR hleaf cache ids nd len⟩

end use

section wrap
open Sparkle.Tests.Compiler.GateConeWrapAddTest

theorem wrapAdd_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapAddBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapAddBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).context
      G (prepInsN wrapAddBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  obtain ⟨z0, hz0, hz0I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (wrapAddBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
    `a (.bits 8) i0 nd (by simp [wrapAddBinders]) (by decide)
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (wrapAddBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
    `b (.bits 8) i1 nd (by simp [wrapAddBinders]) (by decide)
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
  refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := [])
    (dom := .const ``Sparkle.Core.Domain.defaultDomain []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact namW_fvar (tenv := envR) L hz0 hz0I _
  · rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · exact absurd hk (by simp)

theorem wrapAdd_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
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
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.wrapAdd_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    wrapAdd_namW L hD tagR hleaf cache ids nd len⟩

end wrap

section nested
open Sparkle.Tests.Compiler.GateConeNestedTest

theorem parentNested_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentNestedBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepInsN parentNestedBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentNested))
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
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentNestedBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))
    `a (.bits 8) i1 nd (by simp [parentNestedBinders]) (by decide)
  obtain ⟨z2, hz2, hz2I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (parentNestedBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))
    `b (.bits 8) i2 nd (by simp [parentNestedBinders]) (by decide)
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
  have inner : NamW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip [i0, i1, i2])
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepInsN parentNestedBinders [i0, i1, i2] cache (Sparkle.IR.ModuleName.ofDecl ``parentNested))
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) := by
    refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · rcases k with _ | k
      · exact namW_fvar (tenv := envR) L hz2 hz2I _
      · exact absurd hk (by simp)
  rw [hbody, hfl]
  refine namW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2]) L hD
    (translateFuelLimit - 2 + 1) rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact inner
  · rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz2 hz2I _
    · exact absurd hk (by simp)

theorem parentNested_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentNestedBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentNested)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (prepInsN parentNestedBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``parentNested))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) :=
  ⟨Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentNested_desW L hD tagR (fun y hy => (hleaf y hy).1)
      cache ids nd len,
    parentNested_namW L hD tagR hleaf cache ids nd len⟩

end nested

end walks

/-! ## The design level (generated) -/

section svn
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

/-- **`parentMix` at the design level, `combSideB` narrowed to `hierTyped`**: `parentMix_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem parentMix_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.parentMix_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentMix_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeTagTest.parentMix_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

/-- **`parentTwoCalls` at the design level, `combSideB` narrowed to `hierTyped`**: `parentTwoCalls_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem parentTwoCalls_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.parentTwoCalls_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentTwoCalls_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

/-- **`parentRepeat` at the design level, `combSideB` narrowed to `hierTyped`**: `parentRepeat_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem parentRepeat_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.parentRepeat_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentRepeat_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeat_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

/-- **`parentCmp` at the design level, `combSideB` narrowed to `hierTyped`**: `parentCmp_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem parentCmp_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.parentCmp_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentCmp_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

/-- **`parentUse` at the design level, `combSideB` narrowed to `hierTyped`**: `parentUse_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem parentUse_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.parentUse_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentUse_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeUseTest.parentUse_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

/-- **`wrapAdd` at the design level, `combSideB` narrowed to `hierTyped`**: `wrapAdd_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem wrapAdd_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.wrapAdd_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.wrapAdd_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

/-- **`parentNested` at the design level, `combSideB` narrowed to `hierTyped`**: `parentNested_gate_designSVN` with five of its six `combSideB` conjuncts derived and `designSideB` narrowed to `designSideB3` (the children's check derived,
`Tools.ShippingFirstGateChild.first_child_kidK`; `Tools.ShippingGateParentRun.gate_combFacts`). -/
theorem parentNested_gate_designSVN2 {mctx : Lean.Meta.Context}
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
      (Tools.ShippingHierTyped.hierTyped
          (Tools.ShippingMachineLinked.childMap design.modules) b = true →
        Tools.ShippingGateParentRun.designSideB3 design.modules b = true →
        ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
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
    Sparkle.Tests.Compiler.GateConeDesignCombTest.parentNested_gate_designSVN hr gdef bnd centry
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``childAdd)
    (n := 2) hr gdef bnd (childAdd_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentNested_walk2 L' hD' (Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_tag hacc) hleaf
        cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB,
    fun hty hDB => hD (Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty)
      (Tools.ShippingGateParentRun.designSideB_of3 hDB h6)⟩

end svn

end Sparkle.Tests.Compiler.GateConeDesignNamesTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentMix_gate_designSVN2
#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentUse_gate_designSVN2
#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.wrapAdd_gate_designSVN2
#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentTwoCalls_gate_designSVN2
#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentRepeat_gate_designSVN2
#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentCmp_gate_designSVN2
#print axioms Sparkle.Tests.Compiler.GateConeDesignNamesTest.parentNested_gate_designSVN2
