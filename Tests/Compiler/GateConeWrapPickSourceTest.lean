import Tests.Compiler.GateConeWrapPickTest

/-! # `wrapPick` against its SOURCE (worker W, round 2)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeWrapPickSourceTest`;
not in `Tests.AllTests`).

`Tests/Compiler/GateConeWrapPickTest.lean` proves the cone with `out` equal to
`pick`'s GATE TERM on the inputs (`pickF`). Here the one remaining step to the
Signal source, in the shape of `wrapAdd_gate_cone_runK'`:

* `pickF_source` — the gate term of `pick` on the numbers of `s`, `x` is
  `pick`'s Signal semantics on the constant signals `s`, `x`, by definitional
  unfolding (the same unfolding the generated `pick.gate_child` closes with
  `fun _ _ => rfl`: the gate's term IS `pick`'s body read back), after
  `BitVec.ofNat w v.toNat = v`;
* **`wrapPick_gate_cone_runK'`** — the run's own child cache has `pick`'s
  entry and the linked evaluation of the compiled module drives `out` with
  `((wrapPick sS xS).val t).toNat`.

Premises: the run, `GateDefines` (NOT ALLOWED, ruling pending — unchanged),
`ChildBnd` (ALLOWED), `EntryDefines` of `pick` (ALLOWED). -/
namespace Sparkle.Tests.Compiler.GateConeWrapPickSourceTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineInstTest (pick)
open Sparkle.Tests.Compiler.SlotlessParentProbeTest (wrapPick)
open Sparkle.Tests.Compiler.GateConeWrapPickTest
open Tools.ShippingHierarchySoundness
open Tools.ShippingHierTermSoundness
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **`pick`'s gate term is `pick`** on constant signals (definitional
unfolding, then `BitVec.ofNat w v.toNat = v`). -/
theorem pickF_source (s : BitVec 2) (x : BitVec 8) :
    pickF [s.toNat, x.toNat] =
      ((pick (Signal.pure s) (Signal.pure x) : Signal defaultDomain (BitVec 8)).val 0).toNat := by
  have h : pickF [s.toNat, x.toNat] =
      ((pick (Signal.pure (BitVec.ofNat 2 s.toNat)) (Signal.pure (BitVec.ofNat 8 x.toNat)) :
        Signal defaultDomain (BitVec 8)).val 0).toNat := rfl
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- What `M`'s linked evaluation against `children` observes: `wrapPick`
(the text of `WrapAddObservesC`, at `wrapPick`). -/
def WrapPickObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (sS : Signal defaultDomain (BitVec 2)) (xS : Signal defaultDomain (BitVec 8))
    (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (wrapPickBinders.zip [i0, i1]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (wrapPickBinders.zip [i0, i1]) a →
  p.bits i0 = some ⟨2, sS.val t⟩ → p.bits i1 = some ⟨8, xS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = ((wrapPick sS xS).val t).toNat) ∧
  InstsLinked children M

/-- The gate-term observation is the source observation. -/
theorem wrapPickObservesC_of_T {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {M : Sparkle.IR.AST.Module} (h : WrapPickObservesT children M) :
    WrapPickObservesC children M := by
  obtain ⟨i0, i1, cache, h⟩ := h
  refine ⟨i0, i1, cache, ?_⟩
  intro bools bits initial sS xS t mems a p adm hs0 hx0
  obtain ⟨⟨result, hev, hout⟩, linked⟩ := h bools bits initial sS xS t mems adm hs0 hx0
  refine ⟨⟨result, hev, ?_⟩, linked⟩
  rw [hout, pickF_source, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  try rfl

/-- **`wrapPick`: the cache entry of `pick` exists and the observation holds
against it** — `out` is `((wrapPick sS xS).val t).toNat`. Binders: the run,
`GateDefines` (NOT ALLOWED, ruling pending — unchanged), `ChildBnd`
(ALLOWED), `EntryDefines` of `pick` (ALLOWED). -/
theorem wrapPick_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapPick) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapPick wrapPickBinders wrapPickBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``pick = true ∧
      ∃ y : Res, mF.get? ``pick = some y ∧ WrapPickObservesC (ownChild y) M := by
  obtain ⟨M, envR, mF, hpost, hcache, tagR, y, hy, obs⟩ :=
    wrapPick_gate_cone_runKT hr gdef bnd centry
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy, wrapPickObservesC_of_T obs⟩

end Sparkle.Tests.Compiler.GateConeWrapPickSourceTest

#print axioms Sparkle.Tests.Compiler.GateConeWrapPickSourceTest.pickF_source
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickSourceTest.wrapPick_gate_cone_runK'
