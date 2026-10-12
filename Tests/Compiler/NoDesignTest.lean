import Tests.Compiler.ShipsFreeMaskedTest
import Tools.ShippingFinalGoalCommand
import Tools.ShippingNoDesignCommand

/-! # The depth SV endpoint without `designCheck` (branch `fix/opt-fallback`)

`#machine_no_design f n` on `parent` and `chained`
(`Tests/Compiler/ShippingMachineSeqTest.lean`): the generated
`f.machine_designG1` (`designCheck` of the shipped module from the core run,
the connection widths and the children's check; the data conditions on the
output ports decided), `f.machine_design_noDesignNR1` and its `_closed`
form: `∃ raw D, … ∧ (portsMatchB … → kidsPass … → Bnd → …)`.

`#machine_goal_gap_of` on the closed forms logs the `GOALGAP` lines. Then,
as errors otherwise: standard axioms only; no statement mentions
`designCheck`, `shipsHierCheck`, `hierCheck`, `outsCheck` or `kidsMaskedN`;
the gap theorem of each has EXACTLY the gap hypotheses `gap_portsMatchB` and
`gap_kidsPass` (the reporter's `allowed` is a white list — `RunsTo`,
`MachineDefines`, `EntryDefines`, `ChildBnd` and conjunctions of them — so
both are logged `NOT ALLOWED`).

`run facts`, `machine_outsG1` and `machine_maskedG` of the two declarations
come from the imported `Tests/Compiler/ShipsFreeMaskedTest.lean` (the
generators return the existing theorems).

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_no_design Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

set_option maxHeartbeats 0 in
#machine_no_design Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_designG1
#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noDesignNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noDesignNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_noDesignNR1_closed

namespace Tests.Compiler.NoDesignTest
open Lean Meta Elab Command

run_cmd liftTermElabM do
  let mut lines : Array String := #[]
  for n in [``Tools.ShippingNoDesign.machine_design_noDesign,
      ``Tools.ShippingTextShipped.core_designCheck_run] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  for f in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained] do
    let made := [f ++ `machine_designG1,
      f ++ `machine_design_noDesignNR1, f ++ `machine_design_noDesignNR1_closed,
      f ++ `machine_design_noDesignNR1_closed_gap]
    for n in made do
      unless (← getEnv).contains n do throwError "{n}: not generated"
      for ax in ← Lean.collectAxioms n do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{n} uses a non-standard axiom: {ax}"
    for n in [f ++ `machine_design_noDesignNR1,
        f ++ `machine_design_noDesignNR1_closed,
        f ++ `machine_design_noDesignNR1_closed_gap] do
      let ci ← getConstInfo n
      for c in [``Tools.ShippingDesignSV.designCheck,
          ``Tools.ShippingHierPremisesBase.shipsHierCheck,
          ``Tools.ShippingHierPremisesBase.hierCheck,
          ``Tools.ShippingDesignSVBack.outsCheck,
          ``Tools.ShippingMachineShipsDepth.kidsMaskedN] do
        if (ci.type.find? (·.isConstOf c)).isSome then
          throwError "{n}: the statement mentions {c}"
    let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames
      (f ++ `machine_design_noDesignNR1_closed_gap)
    unless gaps == ["gap_portsMatchB", "gap_kidsPass"] do
      throwError "{f}: the gap hypotheses are {gaps}, expected [gap_portsMatchB, gap_kidsPass]"
    lines := lines.push s!"{f}: gap hypotheses {gaps}"
  logInfo m!"NODESIGN TEST: parent and chained — machine_designG1, machine_design_noDesignNR1, its _closed form and its gap theorem on standard axioms; no statement mentions designCheck, shipsHierCheck, hierCheck, outsCheck or kidsMaskedN; {lines}"

end Tests.Compiler.NoDesignTest
