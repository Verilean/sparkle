import Tools.ShippingDesignWriter
import Tools.ShippingKidsChildIface
import Tools.ShippingModuleNames
import Tools.ShippingGateChildComb
import Tools.ShippingMachineDepthRunR

/-! # The print call and the endpoints, from ONE run (finding D; isolated branch `fix/design-writer`)

`#synthesizeVerilogDesign` / `#writeVerilogDesign` / `#writeDesign` print
`toVerilogDesignChecked (← synthesizeHierarchical n)`. The design endpoints
take a run `hr` of the full entry `synthesizeCombinational n` returning
`(b, design)` and speak about `checkedOptimize b` over
`childMap D.modules`, `D` the design of the core run the full entry contains.

`writer_prints_endpoint_artifact`: for a run of `synthesizeHierarchical n`,
a run of the full entry and a run of the core entry, all in the SAME contexts
and state references and from the SAME world (so they are the runs the
hierarchical run contains — a run is a function of its start), the modules
the writer prints are `D.modules ++ [checkedOptimize b]`, its text is the join
of their emitted texts, and the endpoints' child lookup is the lookup in the
printed modules — under two data conditions on the core run's design:

* `hno`: no module of `D` is named as the core module (measured: 37 of 37);
* `htop`: `D.topModule` is the core module's name (measured: 37 of 37;
  `CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)` sets both).

Neither is derived here from the run.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingDesignWriterRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.Backend.Verilog (emitModule designArtifact toVerilogDesignChecked)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingDesignWriter

/-- A run in fixed contexts and references from a fixed world has one result. -/
theorem runsTo_det {α : Type} {m : MetaM α} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w1 w2 : Void IO.RealWorld} {a a' : α}
    (h : RunsTo m mctx mref cctx cref w a w1) (h' : RunsTo m mctx mref cctx cref w a' w2) :
    a = a' := by
  unfold RunsTo at h h'
  rw [h] at h'
  cases h'
  rfl

/-- `synthesizeHierarchical` is the full entry, then `hierDesign` (the name
check returns its argument or throws). -/
theorem synthesizeHierarchical_run {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {dH : Design}
    (h : RunsTo (synthesizeHierarchical declName) mctx mref cctx cref w dH w') :
    ∃ (b : Sparkle.IR.AST.Module) (design : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w1 ∧
      dH = hierDesign b design := by
  unfold synthesizeHierarchical at h
  obtain ⟨⟨b, design⟩, w1, hcomb, h⟩ := RunsTo.bind h
  have hv := (Tools.ShippingModuleNames.validateDesignNames_returns h.mreturns).1
  exact ⟨b, design, w1, hcomb, hv⟩

/-- **The full entry's design has the core design's top field, and its
modules when no module of it is named as the core module**
(`Tools.ShippingKidsChildIface.synthesizeCombinational_designL` with the
`topModule` field added). -/
theorem synthesizeCombinational_designTop {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      D'.topModule = D.topModule ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules) := by
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
    exact ⟨Or.inl rfl, rfl,
      fun hx => Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    refine ⟨Or.inr rfl, rfl, fun hx => ?_⟩
    show (D.modules.map _).map _ = _
    rw [Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx,
      Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx]

/-- The full entry's module is named as the core module. -/
theorem fullEntry_name {b raw : Sparkle.IR.AST.Module}
    (h : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    b.name = raw.name := by
  rcases h with h | h
  · rw [h]
    exact Tools.ShippingGateChildComb.dropZeroWidth_name raw
  · rw [h, Tools.ShippingMachineDepthRun.mergeChecked_name]
    exact Tools.ShippingGateChildComb.dropZeroWidth_name raw

/-- **The print call and the endpoints use the same artifact.** For the
design `dH` a run of `synthesizeHierarchical` returns, the full entry's
result `(b, design)` and the core entry's result `(raw, D)` from the same
start: the modules `toVerilogDesignChecked dH` prints are the modules of
`D`, as they are and in their order, then `checkedOptimize b`; its text is
the join of their emitted texts; and wherever the endpoints' child map
`childMap D.modules` is defined, the printed modules give the same child. -/
theorem writer_prints_endpoint_artifact {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' w1 w2 : Void IO.RealWorld}
    {dH design D : Design} {b raw : Sparkle.IR.AST.Module}
    (h : RunsTo (synthesizeHierarchical declName) mctx mref cctx cref w dH w')
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w1)
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (raw, D) w2)
    (hno : ∀ x ∈ D.modules, x.name ≠ raw.name)
    (htop : D.topModule = raw.name) :
    designArtifact dH = D.modules ++ [checkedOptimize b] ∧
    toVerilogDesignChecked dH =
      String.intercalate "\n"
        (D.modules.map emitModule ++ [emitModule (checkedOptimize b)]) ∧
    ∀ mn r, childMap D.modules mn = some r → childMap (designArtifact dH) mn = some r := by
  obtain ⟨b0, design0, w3, hr0, hdH⟩ := synthesizeHierarchical_run h
  have e : (b0, design0) = (b, design) := runsTo_det hr0 hr
  have eb : b0 = b := (Prod.mk.inj e).1
  have ed : design0 = design := (Prod.mk.inj e).2
  rw [eb, ed] at hdH
  obtain ⟨M, D0, w4, hcore0, hpost, htopD, hmods⟩ := synthesizeCombinational_designTop hr
  have e2 : (M, D0) = (raw, D) := runsTo_det hcore0 hcore
  have eM : M = raw := (Prod.mk.inj e2).1
  have eD : D0 = D := (Prod.mk.inj e2).2
  rw [eM] at hpost
  rw [eM, eD] at hmods
  rw [eD] at htopD
  have hno' : ∀ x ∈ D.modules, x.name ≠ D.topModule :=
    fun x hx hxe => hno x hx (hxe.trans htop)
  have hbt : b.name = D.topModule := (fullEntry_name hpost).trans htop.symm
  have hart : designArtifact (hierDesign b design) = D.modules ++ [checkedOptimize b] :=
    hier_artifact (hmods hno) htopD hno' hbt
  rw [hdH]
  refine ⟨hart, toVerilogDesignChecked_hier (hmods hno) htopD hno' hbt, ?_⟩
  intro mn r hk
  rw [hart]
  exact childMap_artifact_kid hk

end Tools.ShippingDesignWriterRun
