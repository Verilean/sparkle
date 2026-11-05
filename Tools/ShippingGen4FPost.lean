import Tools.ShippingGen4ParamIface
import Tools.ShippingMachineDepthRunR
set_option autoImplicit false

/-! # F-post (scripts/gen4/FPOST_FREEZE.md): post-processing keeps `parameters` and `name`

Field-preservation lemmas for the post-processing of `synthesizeCombinationalWithParameters`, and the form the
`LegalBinding` assembly takes from a returning run. No equivalence claim about the passes. -/

namespace Tools.ShippingGen4FPost
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness
open Tools.ShippingGen4ParamEntry (Tsyn)

theorem dropZW_parameters (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).parameters = m.parameters := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule; split <;> rfl

theorem mergeDuplicates_parameters (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates m).parameters = m.parameters := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates Sparkle.IR.RegDedup.mergeDuplicatesRaw
  dsimp only
  repeat' split
  all_goals rfl

theorem mergeDuplicates_name (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates m).name = m.name := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates Sparkle.IR.RegDedup.mergeDuplicatesRaw
  dsimp only
  repeat' split
  all_goals rfl

theorem mergeChecked_parameters (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.RefineCheck.mergeChecked m).parameters = m.parameters := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases m with h | h <;> rw [h]
  exact mergeDuplicates_parameters m

theorem topMap_keys (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (N : String)
    (hn : ∀ x, (f x).name = x.name) (hp : ∀ x, (f x).parameters = x.parameters) (l : List Sparkle.IR.AST.Module) :
    (l.map fun x => if x.name == N then f x else x).map (·.parameters) = l.map (·.parameters) ∧
    (l.map fun x => if x.name == N then f x else x).map (·.name) = l.map (·.name) := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.map_cons]
    by_cases hx : (x.name == N) = true
    · simp only [hx, if_true, hn, hp, ih.1, ih.2, and_self]
    · have hx' : (x.name == N) = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ↓reduceIte, ih.1, ih.2, and_self]

theorem fpost_run {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters)
      mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      M'.parameters = M.parameters ∧ M'.name = M.name ∧
      D'.modules.map (·.parameters) = D.modules.map (·.parameters) ∧
      D'.modules.map (·.name) = D.modules.map (·.name) := by
  unfold synthesizeCombinationalWithParameters at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  have hd := topMap_keys Sparkle.IR.ZeroWidth.dropZeroWidthModule M.name
    Tools.ShippingMachineDepthRun.dropZW_name dropZW_parameters D.modules
  have hm := topMap_keys Sparkle.IR.RefineCheck.mergeChecked M.name
    Tools.ShippingMachineDepthRun.mergeChecked_name mergeChecked_parameters
    (D.modules.map fun x => if x.name == M.name then Sparkle.IR.ZeroWidth.dropZeroWidthModule x else x)
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact ⟨dropZW_parameters M, Tools.ShippingMachineDepthRun.dropZW_name M, hd.1, hd.2⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (mergeChecked_parameters _).trans (dropZW_parameters M)
    · exact (Tools.ShippingMachineDepthRun.mergeChecked_name _).trans
        (Tools.ShippingMachineDepthRun.dropZW_name M)
    · exact hm.1.trans hd.1
    · exact hm.2.trans hd.2

end Tools.ShippingGen4FPost
