import Tools.ShippingKidsChildIface
import Tools.ShippingGateChildComb
import Tools.ShippingMachineDepthRunR

/-! # The full entry's design IS the core run's design, decided on the full entry's OWN result (G1, round par/a-7)

The endpoints quantify `∃ raw D`, the result of the CORE run the full entry
`synthesizeCombinational f` contains, and state their check premises on
`childMap D.modules`. The full entry returns `(b, design)` and discards
`(raw, D)`. `Tools.ShippingKidsChildIface.synthesizeCombinational_designL`
(built) gives `design.modules = D.modules` under a condition on `D` and
`raw` (`∀ x ∈ D.modules, x.name ≠ raw.name`), which a test holding only
`(b, design)` cannot evaluate.

`fullEntry_sameDesign` states the same equation under the condition on what
the full entry RETURNS: no module of `design` is named as `b`. So a check
evaluated on `(b, design)` of ONE run of the full entry, after evaluating
that condition on the same pair, is a check on exactly the `(b, D)` the
endpoint's statement speaks of (review of 7fa6a19f, point 3).

The proof is `synthesizeCombinational_designL`'s (the full entry's wrapper
only: a `bind`, an `ite`, two `pure`s — no translator run is opened), plus
`map_top_no`: the top-module rewrite preserves names, so a module named as
the top in `D` would still be one in `design`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutSameRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness
open Sparkle.IR.RefineCheck (mergeChecked)

/-- If no module of the rewritten list is named `N`, none of the original
list is: the rewrite `g` keeps names. -/
theorem map_top_no (N : String) (g : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module)
    (hg : ∀ x, (g x).name = x.name) (l : List Sparkle.IR.AST.Module)
    (h : ∀ y ∈ l.map (fun x => if x.name == N then g x else x), y.name ≠ N) :
    ∀ x ∈ l, x.name ≠ N := by
  intro x hx hxe
  have hb : (x.name == N) = true := by
    rw [hxe]
    exact beq_self_eq_true N
  have he : (if (x.name == N) = true then g x else x) = g x := if_pos hb
  have hm : g x ∈ l.map (fun x => if x.name == N then g x else x) :=
    List.mem_map.mpr ⟨x, hx, he⟩
  exact h (g x) hm ((hg x).trans hxe)

/-- **The full entry's design has the core run's modules, when no module of
the RETURNED design is named as the RETURNED module.** -/
theorem fullEntry_sameDesign {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (hno : ∀ x ∈ design.modules, x.name ≠ b.name) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      design.modules = D.modules := by
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
    have hD : ∀ x ∈ D.modules, x.name ≠ M.name :=
      map_top_no M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule
        Tools.ShippingGateChildComb.dropZeroWidth_name D.modules
        (fun y hy hye => hno y hy
          (hye.trans (Tools.ShippingGateChildComb.dropZeroWidth_name M).symm))
    exact ⟨Or.inl rfl, Tools.ShippingKidsChildIface.map_other M.name _ D.modules hD⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    have hbn : (mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)).name = M.name :=
      (Tools.ShippingMachineDepthRun.mergeChecked_name _).trans
        (Tools.ShippingGateChildComb.dropZeroWidth_name M)
    have h1' : ∀ y ∈ D.modules.map (fun x =>
        if x.name == M.name then Sparkle.IR.ZeroWidth.dropZeroWidthModule x else x),
        y.name ≠ M.name :=
      map_top_no M.name mergeChecked Tools.ShippingMachineDepthRun.mergeChecked_name
        (D.modules.map (fun x =>
          if x.name == M.name then Sparkle.IR.ZeroWidth.dropZeroWidthModule x else x))
        (fun y hy hye => hno y hy (hye.trans hbn.symm))
    have hD : ∀ x ∈ D.modules, x.name ≠ M.name :=
      map_top_no M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule
        Tools.ShippingGateChildComb.dropZeroWidth_name D.modules h1'
    refine ⟨Or.inr rfl, ?_⟩
    show (D.modules.map _).map _ = _
    rw [Tools.ShippingKidsChildIface.map_other M.name _ D.modules hD,
      Tools.ShippingKidsChildIface.map_other M.name _ D.modules hD]

end Tools.ShippingOneOutSameRun
