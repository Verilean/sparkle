import Tests.Compiler.GateConeEntryTest
import Tests.Compiler.GateConeUseTest
import Tests.Compiler.GateConeWrapAddTest
import Tests.Compiler.GateConeTwoCallsTest
import Tests.Compiler.GateConeRepeatTest
import Tests.Compiler.GateConeCmpTest
import Tests.Compiler.GateConeNestedTest
import Tools.ShippingGateDesignRun

/-! # Obstacle (A) discharged for the seven gate-route parents (worker N, round 11)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeDesignWalkTest`;
not in `Tests.AllTests`).

Per parent:

* `…_desW` — the walk's contract `DesW` of the instantiated body, for the
  design predicate `G` of any child cache `mF` whose `childAdd` entries
  satisfy `InstLeafOk G 2` (input leaves by `desW_fvar` — the prepared
  context binds them, `prepare_lookup_hit` —, instance calls by `desW_inst`,
  `+` by `desW_binary`, `<ᵤ` by `desW_compare`; the fuel split as in the
  round-6..9 `…_entryWN`).
* `…_gate_designA` — the round-6..9 `…_gate_cone_runK'` conclusion (from the
  design-conjunct copies `gate_cone_runGED` / `GCED` / `GERD`, the SAME run
  and cache) AND obstacle (A) `DesignHasChild design.modules y` AND the core
  module's `ModOk` (the facts obstacle (B) needs; `Tools.ShippingGateDesignPost`).

The design predicate is `ChildG mF` ("is `mF`'s entry of `childAdd`"); every
`childAdd` entry is a first-gate child's full-entry result (`CacheInv`,
`kidFacts_of_first'`), which gives `InstLeafOk` (`childAdd_leafOk`); its
module is named `ofDecl childAdd` (`first_child_name`), not the parent's.

Premises: exactly those of `…_gate_cone_runK'` (the run, `GateDefines` NOT
ALLOWED, `ChildBnd`, `EntryDefines childAdd`). -/
namespace Sparkle.Tests.Compiler.GateConeDesignWalkTest
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

/-! ## The child `childAdd` -/

/-- The design predicate: `mF`'s entry of `childAdd`. -/
def ChildG (mF : Std.HashMap Lean.Name Res) (x : Sparkle.IR.AST.Module) : Prop :=
  ∃ y : Res, mF.get? ``childAdd = some y ∧ x = y.1

theorem childG_eq {mF : Std.HashMap Lean.Name Res} {y : Res}
    (hy : mF.get? ``childAdd = some y) : ∀ x, ChildG mF x → x = y.1 := by
  intro x hx
  obtain ⟨y', hy', hx'⟩ := hx
  rw [hy] at hy'
  cases hy'
  exact hx'

/-- **Every `childAdd` entry of a `CacheInv` cache satisfies the instance
leaf's requirements** (from its `KidFacts`, a first-gate child). -/
theorem childAdd_leafOk {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {mF : Std.HashMap Lean.Name Res}
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue)
    (hcache : CacheInv mref cref mF) :
    ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk (ChildG mF) 2 y := by
  intro y hy
  obtain ⟨cwe, outName, wOut, hdc, hnoclk, -, houts, -, hlen, hwidth, -, -⟩ :=
    kidFacts_of_first' centry childAdd_fe_wf (by decide) (hcache ``childAdd y hy) addSem
      (.bits 8 0) rfl addSem_spec
  have hw8 : wOut = 8 := hwidth.symm
  refine ⟨⟨y, hy, rfl⟩, hdc, hnoclk, hlen, outName, wOut, houts, ?_⟩
  rw [hw8]
  decide

/-- `childAdd`'s module is not named like the parent. -/
theorem childAdd_name_ne {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {y : Res} {f : Lean.Name}
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue)
    (hreal : RealChild mref cref ``childAdd y) (hne : ``childAdd ≠ f) :
    y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f := by
  rw [first_child_name centry childAdd_fe_wf (by decide) hreal]
  exact Tools.ShippingModuleName.ofDecl_ne hne

/-! ## `parentMix` (`childAdd a b + a`) -/

theorem parentMix_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentMixBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentMixBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentMix)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) true := by
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
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (parentMixBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix))
    `a (.bits 8) i1 nd (by simp [parentMixBinders]) (by decide)
  obtain ⟨z2, hz2⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1)) true
  refine desW_binary (tenv := envR) (ha := true) (hb := false) L hD (translateFuelLimit - 2 + 1)
    (by decide) ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_ (Or.inl rfl)
  · rw [ck.2.2.2.2.1]
    show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) true
    refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · rcases k with _ | k
      · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
      · exact absurd hk (by simp)
  · rw [ck.2.2.2.2.2.1]
    show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (.fvar i1) false
    exact desW_fvar (tenv := envR) L hz1 _

/-- **`parentMix`: the round-6 cone conclusion, obstacle (A), and the core
module's `ModOk`.** -/
theorem parentMix_gate_designA {mctx : Lean.Meta.Context}
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
      DesignHasChild design.modules y ∧ ModOk (Sparkle.IR.ModuleName.ofDecl ``parentMix) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGED hr gdef bnd
  have tagR := parentMix_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentMix_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      parentMix_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    parentMix_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

/-! ## `parentTwoCalls` (`childAdd a b + childAdd b a`) -/

section twoCalls
open Sparkle.Tests.Compiler.GateConeTwoCallsTest

theorem parentTwoCalls_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentTwoCallsBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentTwoCallsBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) true := by
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
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (parentTwoCallsBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls))
    `a (.bits 8) i1 nd (by simp [parentTwoCallsBinders]) (by decide)
  obtain ⟨z2, hz2⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1)) true
  refine desW_binary (tenv := envR) (ha := true) (hb := true) L hD (translateFuelLimit - 2 + 1)
    (by decide) ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_ (Or.inl rfl)
  · rw [ck.2.2.2.2.1]
    show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) true
    refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · rcases k with _ | k
      · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
      · exact absurd hk (by simp)
  · rw [ck.2.2.2.2.2.1]
    show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i2, .fvar i1]) true
    refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i2, .fvar i1]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
    · rcases k with _ | k
      · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
      · exact absurd hk (by simp)

theorem parentTwoCalls_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentTwoCalls) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentTwoCalls parentTwoCallsBinders
      parentTwoCallsBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentTwoCallsObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧
      ModOk (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGED hr gdef bnd
  have tagR := parentTwoCalls_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentTwoCalls_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      parentTwoCalls_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    parentTwoCalls_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

end twoCalls

/-! ## `parentRepeat` (`childAdd a b + childAdd a b`) -/

section repeatS
open Sparkle.Tests.Compiler.GateConeRepeatTest

theorem parentRepeat_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentRepeatBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentRepeat)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentRepeatBody) true := by
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
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (parentRepeatBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))
    `a (.bits 8) i1 nd (by simp [parentRepeatBinders]) (by decide)
  obtain ⟨z2, hz2⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  have leafW : DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
      (prepare (fun _ => false) (fun _ _ => 0) (parentRepeatBinders.zip [i0, i1, i2])
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentRepeat))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentRepeat)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) true := by
    refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · rcases k with _ | k
      · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
      · exact absurd hk (by simp)
  rw [hbody, hfl]
  show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1)) _ G _
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (repeatLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)) true
  refine desW_binary (tenv := envR) (ha := true) (hb := true) L hD (translateFuelLimit - 2 + 1)
    (by decide) ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ?_ ?_ (Or.inl rfl)
  · rw [ck.2.2.2.2.1]
    exact leafW
  · rw [ck.2.2.2.2.2.1]
    exact leafW

theorem parentRepeat_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentRepeat) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentRepeat parentRepeatBinders parentRepeatBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentRepeatObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧
      ModOk (Sparkle.IR.ModuleName.ofDecl ``parentRepeat) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGED hr gdef bnd
  have tagR := parentRepeat_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentRepeat_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      parentRepeat_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    parentRepeat_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

end repeatS

/-! ## `parentCmp` (`Signal.ult (childAdd a b) a`) -/

section cmp
open Sparkle.Tests.Compiler.GateConeCmpTest

theorem parentCmp_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentCmpBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentCmpBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentCmp)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) true := by
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
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (parentCmpBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp))
    `a (.bits 8) i1 nd (by simp [parentCmpBinders]) (by decide)
  obtain ⟨z2, hz2⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  refine desW_compare (tenv := envR) (ha := true) (hb := false) L hD (translateFuelLimit - 2 + 1)
    ?_ ?_ (Or.inl rfl)
  · show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) true
    refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · rcases k with _ | k
      · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
      · exact absurd hk (by simp)
  · show DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1)) _ G _
      (.fvar i1) false
    exact desW_fvar (tenv := envR) L hz1 _

theorem parentCmp_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentCmp) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentCmp parentCmpBinders parentCmpBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentCmpObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ ModOk (Sparkle.IR.ModuleName.ofDecl ``parentCmp) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGCED hr gdef bnd
  have tagR := parentCmp_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentCmp_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      parentCmp_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    parentCmp_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

end cmp

/-! ## `parentUse` (`childAdd a b`) -/

section use
open Sparkle.Tests.Compiler.GateConeUseTest
open Sparkle.Tests.Compiler.GateParentRunGTest (parentUseBody)

theorem parentUse_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentUseBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentUseBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentUse)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) true := by
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
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (parentUseBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse))
    `a (.bits 8) i1 nd (by simp [parentUseBinders]) (by decide)
  obtain ⟨z2, hz2⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 1) rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
  · rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
    · exact absurd hk (by simp)

theorem parentUse_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentUse) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentUse parentUseBinders parentUseBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentUseObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ ModOk (Sparkle.IR.ModuleName.ofDecl ``parentUse) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGED hr gdef bnd
  have tagR := parentUse_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentUse_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      parentUse_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    parentUse_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

end use

/-! ## `wrapAdd` (`childAdd a b` at `defaultDomain`) -/

section wrap
open Sparkle.Tests.Compiler.GateConeWrapAddTest

theorem wrapAdd_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapAddBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapAddBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))).context
      G (Sparkle.IR.ModuleName.ofDecl ``wrapAdd)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) true := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  obtain ⟨z0, hz0⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (wrapAddBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd))
    `a (.bits 8) i0 nd (by simp [wrapAddBinders]) (by decide)
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := [])
    (dom := .const ``Sparkle.Core.Domain.defaultDomain []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact ⟨false, desW_fvar (tenv := envR) L hz0 _⟩
  · rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · exact absurd hk (by simp)

theorem wrapAdd_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapAdd) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapAdd wrapAddBinders wrapAddBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ WrapAddObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ ModOk (Sparkle.IR.ModuleName.ofDecl ``wrapAdd) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGED hr gdef bnd
  have tagR := wrapAdd_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => wrapAdd_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      wrapAdd_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    wrapAdd_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

end wrap

/-! ## `parentNested` (`childAdd (childAdd a b) b`) -/

section nested
open Sparkle.Tests.Compiler.GateConeNestedTest

theorem parentNested_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (hleaf : ∀ y : Res, mF.get? ``childAdd = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = parentNestedBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentNested)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) true := by
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
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (parentNestedBinders.zip [i0, i1, i2])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested))
    `a (.bits 8) i1 nd (by simp [parentNestedBinders]) (by decide)
  obtain ⟨z2, hz2⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
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
  have inner : DesW L mF D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
      (prepare (fun _ => false) (fun _ _ => 0) (parentNestedBinders.zip [i0, i1, i2])
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``parentNested))).context
      G (Sparkle.IR.ModuleName.ofDecl ``parentNested)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) true := by
    refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR hleaf ?_
    intro k hk
    rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · rcases k with _ | k
      · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
      · exact absurd hk (by simp)
  rw [hbody, hfl]
  refine desW_inst (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2]) L hD
    (translateFuelLimit - 2 + 1) rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact ⟨true, inner⟩
  · rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz2 _⟩
    · exact absurd hk (by simp)

theorem parentNested_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentNested) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentNested parentNestedBinders parentNestedBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      mF.get? ``childAdd = some y ∧ ParentNestedObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧
      ModOk (Sparkle.IR.ModuleName.ofDecl ``parentNested) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGERD hr gdef bnd
  have tagR := parentNested_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentNested_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  have fin := hdes (ChildG mF)
    (fun L' _ hD cache ids nd len =>
      parentNested_desW L' hD tagR (childAdd_leafOk centry hcache) cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    parentNested_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec),
    designHasChild_of_final fin (childG_eq hy) (childAdd_name_ne centry hreal (by decide)) hmods,
    fin.mod⟩

end nested

end Sparkle.Tests.Compiler.GateConeDesignWalkTest

#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentMix_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentTwoCalls_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentRepeat_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentCmp_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentUse_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.wrapAdd_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeDesignWalkTest.parentNested_gate_designA
