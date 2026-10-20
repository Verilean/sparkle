import Tests.Compiler.GateConeKidTest
import Tools.ShippingGateConeEntry

/-! # `parentMix`: the cache entry of `childAdd` EXISTS (worker N, round 6)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeEntryTest`;
not in `Tests.AllTests`).

`parentMix_gate_cone_runK` (round 5) concluded the observation for EVERY
entry `y` of `childAdd` in the run's final child cache `mF` — vacuous if
there were none. `parentMix_gate_cone_runK'` concludes that the entry EXISTS
and the observation holds against it:

* `parentMix_entryWN`: the body instantiated at any three fresh ids is a
  canonical `+` whose first operand is the instance leaf `childAdd a b`
  (designated at the run's environment); the harness translates the body with
  `named = true` (no lookup at the root); so every such run ends with
  `childAdd` in the child cache (`binary_entryWN` over `inst_entryW`).
* `gate_cone_runGE` (the copy of `gate_cone_runG` with the entry conjunct)
  turns that into `∃ y, mF.get? ``childAdd = some y`.

Premises of `parentMix_gate_cone_runK'`: exactly those of
`parentMix_gate_cone_runK` — the run, `GateDefines` (NOT ALLOWED, ruling
pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd`
(ALLOWED). The old theorems are kept. -/
namespace Sparkle.Tests.Compiler.GateConeEntryTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeTagTest
open Sparkle.Tests.Compiler.GateConeKidTest
open Tools.ShippingHierarchySoundness
open Tools.ShippingUnifiedSource
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx Tools.ShippingInstanceLeaf Tools.ShippingHierTermSoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo FExpr evalFE quoteDecl)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild RefLaws)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild kidFacts_of_first')

/-- **Every lookup-free run of the translator on `parentMix`'s instantiated
body ends with `childAdd` in the child cache.** -/
theorem parentMix_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (ids : List FVarId) (len : ids.length = parentMixBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentMixBody) ``childAdd := by
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
  show EntryWN L D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1))
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1)) ``childAdd
  refine binary_entryWN (tenv := envR) L hD (translateFuelLimit - 2 + 1) ck.1 ck.2.1 ck.2.2.1
    ck.2.2.2.1 (Or.inl ?_)
  rw [ck.2.2.2.2.1]
  show EntryW L D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
    (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) ``childAdd
  exact inst_entryW (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR

/-- **`parentMix_gate_cone_runK` with the cache entry concluded.** Same
binders: the run, `GateDefines` (NOT ALLOWED, ruling pending — unchanged),
`ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED). Conclusion:
the shipped module is the cleanup (or merge) of `M`, the final child cache
`mF` is `CacheInv`, `childAdd` is tagged at the run's environment, and `mF`
HAS an entry `y` of `childAdd`, against which `M`'s linked evaluation
observes `parentMix`. -/
theorem parentMix_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentMix) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentMix parentMixBinders parentMixBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      ∃ y : Res, mF.get? ``childAdd = some y ∧ ParentMixObservesC (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGE hr gdef bnd
  have tagR := parentMix_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentMix_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    parentMix_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)⟩

end Sparkle.Tests.Compiler.GateConeEntryTest

#print axioms Sparkle.Tests.Compiler.GateConeEntryTest.parentMix_entryWN
#print axioms Tools.ShippingGateParentRun.gate_cone_runGE
#print axioms Sparkle.Tests.Compiler.GateConeEntryTest.parentMix_gate_cone_runK'
