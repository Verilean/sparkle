import Tools.ShippingGen5DCEntry
set_option autoImplicit false
-- Built: issue-linked build dc11v-4523f2e9 (`kjob lake build Tests.Gen5.DCEntryDCheck`, which includes this file) exit 0, 747 jobs, approved at 4523f2e9 (incremental build, source=base=end, dirty=false). U-POSTD, scripts/gen5/DC_CONNECT_SUPPLY_SURVEY.md §9 (freeze 3e5b5add approved)

/-! # DC-CONNECT U-POSTD: the module and the returned design of the default entry, in the same branch

Concerns only the default route (`synthesizeCombinational`). States the relation of the core's design `D` and the returned
design `D'` (the top module is rewritten by name), tied to the same branch as `b`. Does NOT transport `TopShips` from `D` to `D'`,
does NOT connect O3's arbitrary `raw` to the core witness's `raw`, does not adopt `Post`. -/

open Lean Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)

namespace Tools.ShippingGen5DCEntryD

/-- the `top` of `synthesizeCombinationalWith`: rewrite the module named like `m` -/
def topMap (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (m : Sparkle.IR.AST.Module)
    (d : Sparkle.IR.AST.Design) : Sparkle.IR.AST.Design :=
  { d with modules := d.modules.map fun x => if x.name == m.name then f x else x }

/-- module and design of the default entry, in the SAME branch -/
def PostEntry (b raw : Sparkle.IR.AST.Module) (D D' : Sparkle.IR.AST.Design) : Prop :=
  (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∧
    D' = topMap Sparkle.IR.ZeroWidth.dropZeroWidthModule raw D) ∨
  (b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ∧
    D' = topMap Sparkle.IR.RefineCheck.mergeChecked raw (topMap Sparkle.IR.ZeroWidth.dropZeroWidthModule raw D))

theorem synthesizeCombinational_postEntry {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w') :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧
      PostEntry b raw D D' := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  rcases Tools.ShippingEntrySoundness.RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inl ⟨this.1, this.2⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inr ⟨this.1, this.2⟩

theorem postEntry_postT1 {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : PostEntry b raw D D') : Tools.ShippingGen5DCEntry.PostT1 b raw :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

end Tools.ShippingGen5DCEntryD
