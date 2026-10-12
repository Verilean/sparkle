import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingFinalGoalCommand
import Tools.ShippingShipsFreeCommand

/-! # The depth SV endpoint without `shipsHierCheck`, applied (branch `fix/opt-fallback`)

`#machine_no_ships f n` on `parent` (two entries of one call of the leaf
`cnt`) and `chained` (three entries of `cnt`)
(`Tests/Compiler/ShippingMachineSeqTest.lean`; their depth endpoints and
closings are generated in `Tests/Compiler/ShippingCallsCloseTest.lean`):

* `f.machine_runFacts`, `f.machine_outsG1` (generated, standard axioms);
* `f.machine_design_noShipsNR1` and `f.machine_design_noShipsNR1_closed`:
  `∃ raw D, … ∧ (designCheck → Bnd → kidsMaskedN → …)`.

`#machine_goal_gap_of` on the closed forms logs the `GOALGAP` lines and adds
`…_closed_gap`. Then, as errors otherwise:

* an axiom audit of everything generated here (standard axioms only);
* no generated statement mentions the constant `shipsHierCheck`, `hierCheck`
  or `outsCheck`;
* the gap theorem of each has EXACTLY the gap hypotheses `gap_designCheck`
  and `gap_kidsMaskedN` (on main the endpoint `machine_design_noOutsNR1_closed`
  has three: these and `gap_shipsHierCheck`).

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_no_ships Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

set_option maxHeartbeats 0 in
#machine_no_ships Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noShipsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noShipsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_noShipsNR1_closed

namespace Tests.Compiler.ShipsFreeTest
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
  for f in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained] do
    let made := [f ++ `machine_runFacts, f ++ `machine_outsG1,
      f ++ `machine_design_noShipsNR1, f ++ `machine_design_noShipsNR1_closed,
      f ++ `machine_design_noShipsNR1_closed_gap]
    for n in made do
      unless (← getEnv).contains n do throwError "{n}: not generated"
      for ax in ← Lean.collectAxioms n do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{n} uses a non-standard axiom: {ax}"
    -- the endpoint, its closed form and its gap do not mention the checkers
    for n in [f ++ `machine_design_noShipsNR1, f ++ `machine_design_noShipsNR1_closed,
        f ++ `machine_design_noShipsNR1_closed_gap] do
      let ci ← getConstInfo n
      for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
          ``Tools.ShippingHierPremisesBase.hierCheck,
          ``Tools.ShippingDesignSVBack.outsCheck] do
        if (ci.type.find? (·.isConstOf c)).isSome then
          throwError "{n}: the statement mentions {c}"
    -- the remaining not-allowed antecedents, exactly
    let gaps ← gapNames (f ++ `machine_design_noShipsNR1_closed_gap)
    if gaps.any (fun g => (g.splitOn "shipsHierCheck").length > 1) then
      throwError "{f}: a gap hypothesis mentions shipsHierCheck: {gaps}"
    unless gaps == ["gap_designCheck", "gap_kidsMaskedN"] do
      throwError "{f}: the gap hypotheses are {gaps}, expected [gap_designCheck, gap_kidsMaskedN]"
    lines := lines.push s!"{f}: gap hypotheses {gaps}"
  logInfo m!"SHIPSFREE: parent and chained — machine_runFacts, machine_outsG1, machine_design_noShipsNR1, its _closed form and its gap theorem on standard axioms; no statement mentions shipsHierCheck, hierCheck or outsCheck; {lines}"

end Tests.Compiler.ShipsFreeTest
