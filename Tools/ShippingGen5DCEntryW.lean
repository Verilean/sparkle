import Tools.ShippingGen5FG
import Tools.ShippingGen5DCEntryD
set_option autoImplicit false
-- NOT BUILT: U-ENTRYW, scripts/gen5/DC_CONNECT_NEXT_UNIT_FREEZE.md §3 (freeze 38259f62 approved). Build is the coder's.

/-! # DC-CONNECT U-ENTRYW: reading an `EntryWitness`

`EntryWitness` gives `Start`, one of the two routes, and `ReflectsAll`. This unit only READS a witness: `Start` together with the
default-route core run tied to `PostEntry`, or the parametrised run kept as it is. Does NOT supply an `EntryWitness` or
`ReflectsAll`, does not transport `TopShips`/`ResetNk` from `D` to `D'`, does not treat the parametrised route's post-processing,
does not adopt `Post`. -/

open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5DCEntryD (PostEntry)

namespace Tools.ShippingGen5DCEntryW

theorem entryWitness_postEntry {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D') :
    Start L mctx cctx w ∧
    ((∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
        RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w') := by
  obtain ⟨hS, hr, -⟩ := h
  refine ⟨hS, ?_⟩
  rcases hr with hr | hr
  · exact Or.inl (Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr)
  · exact Or.inr hr

theorem entryWitness_left_postEntry {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w') :
    Start L mctx cctx w ∧
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D' :=
  ⟨h.1, Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hl⟩

end Tools.ShippingGen5DCEntryW
