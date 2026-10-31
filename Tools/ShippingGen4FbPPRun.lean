import Tools.ShippingGen4FbPPLookup
import Tools.ShippingMachineDepthRunR
set_option autoImplicit false
-- BUILT (unit FB-18): kjob lake build Tools.ShippingGen4FbPPRun exit 0 (703 jobs, Pod build at e9fc8213); clean issue-linked build fb18v-e9fc8213 exit 0 (815 jobs, dirty=false; approved at e9fc8213, scope-limited to the two theorems). Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §27.3 (committed before this file).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # FB-18: T-PP-RUN — a real run of the full entry gives `PPRel`

Same proof text as `synthesizeCombinational_design`, keeping the design equation. Partial supply: it does not transport
the run conjunct of `ChildRunN` and says nothing about what `(M, D)` computes. -/

namespace Tools.ShippingGen4FbPPRun
open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen4FbPP Tools.ShippingGen4FbPPLookup

theorem synthesizeCombinational_ppRel {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      Tools.ShippingGen4FbPP.PPRel M D M' D' := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact Or.inl ⟨rfl, rfl⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact Or.inr ⟨rfl, rfl⟩

theorem synthesizeCombinational_lookup {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      Tools.ShippingGen4FbPP.PPRel M D M' D' ∧
      (Sparkle.IR.Machine.moduleByName D.modules M.name = some M →
        Sparkle.IR.Machine.moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        Sparkle.IR.Machine.moduleByName D'.modules y = Sparkle.IR.Machine.moduleByName D.modules y) := by
  obtain ⟨M, D, w1, hcore, hpp⟩ := synthesizeCombinational_ppRel h
  exact ⟨M, D, w1, hcore, hpp, fun hr => ppRel_lookup_self hpp hr, ppRel_lookup_other hpp⟩

end Tools.ShippingGen4FbPPRun
