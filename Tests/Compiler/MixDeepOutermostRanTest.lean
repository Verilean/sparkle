import Tests.Compiler.MixDeepOutermostTest
import Tools.ShippingMachineRan
import Tools.ShippingFinalGoalCommand
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `mixDeep` at outermost starts: the consumed end, in the form the design-level consumers take

WRITTEN, NOT BUILT (par/a-43). Target-only; not in `Tests.AllTests`. No
existing endpoint, premise, generator or count changes.

## What is here, and what is NOT

* `mixDeep_machineRan_outermost`: for a run of the FULL entry
  `synthesizeCombinational mixDeep` from a depth-0 start (`Start0`), with the
  five reflections: the core run, its post-processing, and
  `MachineRan … mixDeep … M D` — the machine synthesis that run performed
  returned its result. NO `MachineClosesAt`.
* `mixDeep_kids_self_outermost`: ONE design-level consumer at that start,
  with no `MachineClosesAt`: `core_kids_self`'s conclusion (the run's design
  resolves the real children's modules to themselves), through
  `Tools.ShippingMachineRan.core_kids_self_ran`.
* **NOT here: `mixDeep.machine_design_noPortsNR2_outermost`.** The
  design-level chain takes `closes : MachineClosesAt …` and uses it in
  thirteen base lemmas whose proofs do not factor through `MachineRan`
  (`Tools/ShippingMachineRan.lean`, `docs/parallel/A-outermost-form.md`).
  The `DesignSV` conclusion at outermost starts needs those thirteen tails
  restated over `MachineRan`; one of them is done as an example. Nothing in
  this file is that endpoint, and `mixDeep` is not covered by it.

## The start premise and the classifier

`Start0 mref cref w` is `∃ L, L.sval w = some synthesizeChild ∧ L.dval w = 0
∧ L.quiet w`: `ChildBnd` with its depth-0 disjunct chosen
(`Start0.childBnd`). The run command below lists every proposition binder of
`mixDeep_machineRan_outermost` with the label the EXISTING classifier
`Tools.ShippingFinalGoalCommand.allowed` gives it:

    OUTERMOST PREMISE <head>: <ALLOWED|NOT ALLOWED>
    OUTERMOST: … the depth-0 start premise is <ALLOWED|NOT ALLOWED> by the existing classifier

PREDICTED: the run and the five reflections `ALLOWED`; `Start0`
**NOT ALLOWED** (the classifier knows `RunsTo`, `MachineDefines`,
`EntryDefines`, `ChildBnd` and conjunctions of them; `Start0` is none of
these, and it is NOT added to the list). The command throws if the statement
mentions `MachineClosesAt`. -/
namespace Tests.Compiler.MixDeepOutermostRanTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingMachineRan (Start0 MachineRan machineRan_outermost core_kids_self_ran)
open Tests.Compiler.MixDeepOutermostTest (mixDeep_closes_prov)

/-- **`mixDeep`, a full-entry run from a depth-0 start**: the machine
synthesis that run performed returned its result. Premises: the run, the
five reflections, `Start0`. -/
theorem mixDeep_machineRan_outermost {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational
        ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep)
      mctx mref cctx cref w (b, design) w')
    (hRg : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hR2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (h0 : Start0 mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore
          ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep [] false)
        mctx mref cctx cref w (M, D) w1 ∧
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      MachineRan mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
        (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape M D := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ :=
    Tools.ShippingGateChildComb.synthesizeCombinational_parts hr
  exact ⟨M, D, w1, hcore, hpost,
    machineRan_outermost hcore hRg h0
      (fun L bb w9 r w10 hw9 hd9 hp9 hrun =>
        mixDeep_closes_prov L hR2 hRm hRr hRc bb w9 r w10 hw9 hd9 hp9 hrun)⟩

theorem mixDeep_hasCalls :
    (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts ≠ [] := by
  first | decide | decide +kernel

theorem mixDeep_noMem :
    ∀ x ∈ (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true := by
  first | decide | decide +kernel

/-- **One design-level consumer at a depth-0 start, with no
`MachineClosesAt`**: the design of `mixDeep`'s core run resolves its real
children's modules, and the modules of their designs, to themselves. -/
theorem mixDeep_kids_self_outermost {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational
        ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep)
      mctx mref cctx cref w (b, design) w')
    (hRg : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hR2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (h0 : Start0 mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      ∀ g ∈ D.modules, ∃ (k : Nat)
        (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts.length)
        (y : Tools.ShippingChildInv.Res),
        Tools.ShippingChildInv.RealChild mref cref
          ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts[k]).1 y ∧
        (g = y.1 ∨ g ∈ y.2.modules) ∧
        Sparkle.IR.Machine.moduleByName D.modules y.1.name = some y.1 ∧
        ∀ g2 ∈ y.2.modules, Sparkle.IR.Machine.moduleByName D.modules g2.name = some g2 := by
  obtain ⟨M, D, w1, -, hpost, ran⟩ := mixDeep_machineRan_outermost hr hRg hR2 hRm hRr hRc h0
  exact ⟨M, D, hpost,
    core_kids_self_ran Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body (nDecl := 1)
      (by decide) (by decide) (by decide) mixDeep_hasCalls mixDeep_noMem ran⟩

#check @mixDeep_machineRan_outermost
#print axioms mixDeep_machineRan_outermost
#print axioms mixDeep_kids_self_outermost
#print axioms Tools.ShippingMachineRan.core_kids_self_of_closes

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  IO.eprintln "OUTERMOST START: the premises of mixDeep_machineRan_outermost, by the existing classifier"
  (← IO.getStderr).flush
  let n := ``Tests.Compiler.MixDeepOutermostRanTest.mixDeep_machineRan_outermost
  let some info := (← Lean.getEnv).find? n | throwError "{n}: missing"
  for c in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses] do
    if (info.type.find? (·.isConstOf c)).isSome then
      throwError "{n}: its statement mentions {c}"
  let (lines, startLabel) ← Lean.Meta.forallTelescope info.type fun xs _ => do
    let mut lines : Array String := #[]
    let mut startLabel : String := "absent"
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then
        let ok := Tools.ShippingFinalGoalCommand.allowed t
        let label : String := if ok then "ALLOWED" else "NOT ALLOWED"
        let head : String := match t.getAppFn with
          | .const nm _ => toString nm
          | _ => "?"
        lines := lines.push s!"OUTERMOST PREMISE {head}: {label}"
        if t.isAppOf ``Tools.ShippingMachineRan.Start0 then startLabel := label
    pure (lines, startLabel)
  for l in lines do Lean.logInfo m!"{l}"
  Lean.logInfo m!"OUTERMOST: {n} has {lines.size} proposition binders; no MachineClosesAt; the depth-0 start premise (Start0) is {startLabel} by the existing classifier Tools.ShippingFinalGoalCommand.allowed — it was not added to the allowed list. This theorem is NOT a design-level endpoint: its conclusion is MachineRan, not DesignSV."

end Tests.Compiler.MixDeepOutermostRanTest
