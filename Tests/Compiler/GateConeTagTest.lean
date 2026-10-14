import Tests.Compiler.GateConeRunTest
import Tools.ShippingGateConeTag

/-! # `parentMix`: the leaf tag discharged from the gate's acceptance (worker N, round 4)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeTagTest`;
not in `Tests.AllTests`).

`parentMix_gate_cone_runG` (round 3) concluded `ParentMixObserves M` under
three antecedents about the run's own values: (a) `isHardwareModule envR
``childAdd = true`, (b) `mF`'s entry `y` of `childAdd` has `y.1 =
childModule`, (c) `y.2.modules = []`.

* (a) is DISCHARGED here: `parentMix_leafSel` (pure, by evaluation — the
  gate refuses `parentMix`'s body under any predicate that does not
  designate the leaf `childAdd dom a b`) + the general
  `Tools.ShippingGateConeTag.gate_leaf_tag'` at the acceptance
  `gate_cone_runG` exposes.
* (b), (c) are NOT discharged (see the worker record §16): `childAdd` is a
  FIRST-gate declaration (`certifiedShape?` accepts `x + y`), so the built
  gate-child facts (`childFull_of_real`, `gate_real_ports`: mixed gate) do
  not apply to it, and no theorem pins the TEXT of a full-entry module, so
  `y.1 = childModule` is not derivable from `RealChild` at all.

`parentMix_gate_cone_runG'`: the round-3 theorem with (a) removed from the
antecedents (and stated as a conjunct of the conclusion). Binders unchanged:
the run, `GateDefines` (NOT ALLOWED until ruled), `ChildBnd`. -/
namespace Sparkle.Tests.Compiler.GateConeTagTest
open Lean Sparkle.Compiler.Elab
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingGateDefines (GateDefines mixedGateCond)
open Tools.ShippingGateConeTag
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res)

/-- The leaf as the recogniser names it. -/
theorem parentMix_leaf_eq : bvarCallE ``childAdd [0, 1, 2] =
    instEN ``childAdd [] (inputExpr parentMixBinders.length 0)
      ([1, 2].map (inputExpr parentMixBinders.length)) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **The gate refuses `parentMix`'s body under the predicate that refuses
its leaf** (every `isInst` elsewhere). The two disjuncts that consult the
predicate on the body itself are false by their (closed) spines; the rest is
evaluation. -/
theorem parentMix_leafSel : ∀ (isInst : Lean.Expr → Bool) (sc : Bool),
    mixedGateCond (fun e => !bvarCall ``childAdd [0, 1, 2] e && isInst e)
      (parentMixBinders.map (·.2)).toArray parentMixBody sc = false := by
  intro isInst sc
  have hs1 : (unifiedInstanceSpine (parentMixBinders.map (·.2)).toArray parentMixBody ||
      unifiedProjSpine (parentMixBinders.map (·.2)).toArray parentMixBody) = false := rfl
  have hs2 : hierInstSpine (fun e => !bvarCall ``childAdd [0, 1, 2] e && isInst e)
      (parentMixBinders.map (·.2)).toArray parentMixBody = false := rfl
  unfold mixedGateCond unifiedInstanceRoot hierInstRoot
  simp only [hs1, hs2, Bool.and_false, Bool.false_and]
  all_goals rfl

/-- **(a): the leaf's callee is tagged at the run's environment**, from the
gate's acceptance at that environment. -/
theorem parentMix_tag {envR : Environment}
    (hacc : ∃ dv : DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (instancePredicate envR) = some (parentMixBinders, parentMixBody)) :
    Sparkle.Compiler.isHardwareModule envR ``childAdd = true := by
  have h0 := gateLeafSel_of (kinds := (parentMixBinders.map (·.2)).toArray)
    (body := parentMixBody) parentMix_leafSel
  rw [parentMix_leaf_eq] at h0
  exact gate_leaf_tag' (mn := ``childAdd) (lvls := []) (dE := inputExpr parentMixBinders.length 0)
    (n := parentMixBinders.length) (poss := [1, 2]) hacc (List.cons_ne_nil _ _) h0

/-- **`gate_cone_runG` on `parentMix`, the tag discharged.** Binders: the
run, `GateDefines` (NOT ALLOWED until ruled), `ChildBnd`. Remaining
antecedents (b), (c): facts of the run's own child `y` (worker record §16). -/
theorem parentMix_gate_cone_runG' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentMix) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentMix parentMixBinders parentMixBody)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      (∀ y : Res, mF.get? ``childAdd = some y → y.1 = childModule → y.2.modules = [] →
        ParentMixObserves M) := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone⟩ :=
    Tools.ShippingGateParentRun.gate_cone_runG hr gdef bnd
  have tagR := parentMix_tag hacc
  exact ⟨M, envR, mF, hpost, hcache, tagR,
    fun y hy hy1 hy2 => parentMix_coneK hcone tagR hy hy1 hy2⟩

end Sparkle.Tests.Compiler.GateConeTagTest

#print axioms Sparkle.Tests.Compiler.GateConeTagTest.parentMix_tag
#print axioms Sparkle.Tests.Compiler.GateConeTagTest.parentMix_gate_cone_runG'
