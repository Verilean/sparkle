import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingFinalGoalCommand
import Tools.ShippingShipsFreeMaskedCommand

/-! # The depth SV endpoint with `designCheck` as its only check (branch `fix/opt-fallback`)

`#machine_no_ships_masked f n` on `parent` and `chained`
(`Tests/Compiler/ShippingMachineSeqTest.lean`): the generated
`f.machine_maskedG` (the children's bound from the core run, by the masks
guard of `mergeChecked`), `f.machine_design_noShipsNoMaskedNR1` and its
`_closed` form: `∃ raw D, … ∧ (designCheck → Bnd → …)`.

`#machine_goal_gap_of` on the closed forms logs the `GOALGAP` lines. Then,
as errors otherwise: standard axioms only; no statement mentions
`shipsHierCheck`, `hierCheck`, `outsCheck` or `kidsMaskedN`; the gap theorem
of each has EXACTLY the gap hypothesis `gap_designCheck`.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_no_ships_masked Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

set_option maxHeartbeats 0 in
#machine_no_ships_masked Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noShipsNoMaskedNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noShipsNoMaskedNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_noShipsNoMaskedNR1_closed

namespace Tests.Compiler.ShipsFreeMaskedTest
open Lean Meta Elab Command

/-- The names of the `gap_…` hypotheses of a gap theorem, in order. -/
def gapNames (thm : Name) : MetaM (List String) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : List String := []
    for x in xs do
      let nm := (← x.fvarId!.getUserName).toString
      if nm.startsWith "gap_" then out := out ++ [nm]
    return out

run_cmd liftTermElabM do
  let mut lines : Array String := #[]
  for n in [``Tools.ShippingShipsFreeMasked.machine_design_noShips_noBd,
      ``Tools.ShippingChecksMaskedLeaf.leaf_real_kidM,
      ``Tools.ShippingClosedMasked.closedBody_masked_of_run,
      ``Sparkle.IR.RefineCheck.mergeChecked_masks] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  for f in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained] do
    let made := [f ++ `machine_runFacts, f ++ `machine_outsG1, f ++ `machine_maskedG,
      f ++ `machine_design_noShipsNoMaskedNR1, f ++ `machine_design_noShipsNoMaskedNR1_closed,
      f ++ `machine_design_noShipsNoMaskedNR1_closed_gap]
    for n in made do
      unless (← getEnv).contains n do throwError "{n}: not generated"
      for ax in ← Lean.collectAxioms n do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{n} uses a non-standard axiom: {ax}"
    for n in [f ++ `machine_design_noShipsNoMaskedNR1,
        f ++ `machine_design_noShipsNoMaskedNR1_closed,
        f ++ `machine_design_noShipsNoMaskedNR1_closed_gap] do
      let ci ← getConstInfo n
      for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
          ``Tools.ShippingHierPremisesBase.hierCheck,
          ``Tools.ShippingDesignSVBack.outsCheck,
          ``Tools.ShippingMachineShipsDepth.kidsMaskedN] do
        if (ci.type.find? (·.isConstOf c)).isSome then
          throwError "{n}: the statement mentions {c}"
    let gaps ← gapNames (f ++ `machine_design_noShipsNoMaskedNR1_closed_gap)
    unless gaps == ["gap_designCheck"] do
      throwError "{f}: the gap hypotheses are {gaps}, expected [gap_designCheck]"
    lines := lines.push s!"{f}: gap hypotheses {gaps}"
  logInfo m!"SHIPSFREEMASKED: parent and chained — machine_runFacts, machine_outsG1, machine_maskedG, machine_design_noShipsNoMaskedNR1, its _closed form and its gap theorem on standard axioms; no statement mentions shipsHierCheck, hierCheck, outsCheck or kidsMaskedN; {lines}"

end Tests.Compiler.ShipsFreeMaskedTest
