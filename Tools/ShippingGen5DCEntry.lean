import Tools.ShippingPostSoundness
set_option autoImplicit false
-- NOT BUILT (U-POST, scripts/gen5/DC_CONNECT_SUPPLY_SURVEY.md §4)

/-! # DC-CONNECT U-POST: the default entry satisfies the `T1Stmt` post-processing relation

Design only about the default route (`synthesizeCombinational`); no parametric route, no `ReflectsAll`, no O2/O3,
no relation between the core's design `D` and the returned `D'`, no connection of O3's arbitrary `raw` to the
core witness's `raw`. -/

open Lean Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)

namespace Tools.ShippingGen5DCEntry

/-- the post-processing relation of the default entry: the text of `T1Stmt`'s hypothesis (Tools/ShippingGen2Defs.lean:362-364) -/
def PostT1 (b raw : Sparkle.IR.AST.Module) : Prop :=
  b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
  b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)

theorem synthesizeCombinational_postT1 {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w') :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧
      PostT1 b raw := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  rcases Tools.ShippingEntrySoundness.RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inl this.1
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inr this.1

/-- O1 of `FG_CONNECT` on the default route at `Post := PostT1` -/
theorem o1_default {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w') :
    ∃ raw, PostT1 b raw :=
  let ⟨raw, _, _, _, hp⟩ := synthesizeCombinational_postT1 h
  ⟨raw, hp⟩

end Tools.ShippingGen5DCEntry
