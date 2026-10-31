import Tools.ShippingGen4FbPPRun
import Tools.ShippingGen4FbDzRun
import Tools.ShippingFirstGateChild
set_option autoImplicit false
-- BUILT IN POD ONLY (unit FB-21): `kjob lake build Tools.ShippingGen4FbFrag` exit 0 (705 jobs) in the Pod; NOT a clean issue-linked build. Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §31.3 (freeze 713c9645, approved, committed before this file).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # FB-21: real-run `PostReady` / `instFree` for a first-gate fragment, and `ChildRunN` transport on the clean-up arm

Partial supply. Conditional on `EntryDefines` and `WF` (existing hypothesis predicates), first-gate fragments only; it does
not say which arm of `PPRel` holds. `ChildRunN … M` for the core module stays a hypothesis. -/

namespace Tools.ShippingGen4FbFrag

theorem postReady_instFree {M : Sparkle.IR.AST.Module} {n : Nat}
    (h : Tools.ShippingEntrySoundness.PostReady M n) :
    Tools.ShippingHierStateG.instFree M.body := by
  intro st hst
  obtain ⟨l, r, rfl, -⟩ := h.2.2.1 st hst
  rfl

theorem synthesizeCombinational_fragment_dz {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (h : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (M', D') w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      Tools.ShippingGen4FbPP.PPRel M D M' D' ∧
      Tools.ShippingEntrySoundness.PostReady M n ∧
      Tools.ShippingHierStateG.instFree M.body ∧
      (0 < n → M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M →
        ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
          {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {m : Nat}
          {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
          {outsC : List Sparkle.IR.Machine.OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
        Tools.ShippingGen2.ChildRunN ch₁ dsn₁ m M bsC outsC S →
        Tools.ShippingGen2.ChildRunN ch₂ dsn₂ m M' bsC outsC S) := by
  obtain ⟨M, D, w1, hcore, hpp⟩ := Tools.ShippingGen4FbPPRun.synthesizeCombinational_ppRel h
  have hpr : Tools.ShippingEntrySoundness.PostReady M n :=
    Tools.ShippingFirstGateChild.first_core_postReady hcore entry hwf
  have hinst := postReady_instFree hpr
  refine ⟨M, D, w1, hcore, hpp, hpr, hinst, ?_⟩
  intro hn hM' ch₁ ch₂ dsn₁ dsn₂ m bsC outsC S hcr
  subst hM'
  exact Tools.ShippingGen4FbDzRun.childRunN_dz_postReady hn hpr hinst hcr

end Tools.ShippingGen4FbFrag
