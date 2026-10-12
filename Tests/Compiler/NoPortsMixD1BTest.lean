import Tests.Compiler.NoPortsMixD1Test
import Tests.Compiler.NoPortsGrandHBTest

/-! # `mixD1`: the boundary of the closed check-free endpoint, reduced to `ChildBnd` (G1, round par/a-14)

`mixD1.machine_design_noPortsNR1_closed` (`NoPortsMixD1Test`, WRITTEN) has,
BY READING of the generator (`Tools/ShippingMachineDepthCommandR.lean`
302–336, 553–559; not a log), the one antecedent

    ChildBnd mref cref w ∧
      (MachineDefines … midH … ∧ names(midH) ∧
        ∀ mctx' cctx', ChildRanIn mref cref `midH mctx' cctx' →
          ∀ wc raw D, ChildBnd mref cref wc →
            ChildBnd mref cref wc ∧ EntryDefines mctx' mref cctx' cref `rcH rcH.gateValue) ∧
      MachineDefines … cnt …

(`names(midH)` is `True` in `grandH`'s BUILT statement; ASSUMED the same
here: the same child, the same generator) and the reflection binders of
`mixD1`, `midH`, `cnt` (`MachineDefines`) and `rcH` (`EntryDefines`).

`#machine_boundary_close` adds `mixD1.machine_design_noPortsNR1_closedB`
(antecedent `ChildBnd mref cref w` only, the same binders), and
`#machine_goal_gap_of` its `_gap`.

| endpoint | premise of `mixD1.machine_design_noPortsNR1_closed` | predicted state |
|---|---|---|
| `mixD1.machine_design_noPortsNR1_closedB` | antecedent conjuncts `MachineDefines midH`, `MachineDefines cnt` (binders too), `True` | WRITTEN, NOT BUILT — predicted absent from the antecedent, pending build |
| | antecedent conjunct `∀ mctx' cctx', ChildRanIn … midH … → …` (NOT ALLOWED) | predicted absent, pending build |
| | `ChildBnd mref cref w` | STAYS |
| | binders | STAY, none added |
| `…_closedB_gap` | gap hypotheses | predicted NONE, 0 NOT ALLOWED |

UNVERIFIED at the time of writing: this file was not built (and it depends
on two files that were not built). -/

set_option maxHeartbeats 0 in
#machine_boundary_close
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closedB

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
  let closed := g ++ `machine_design_noPortsNR1_closed
  let closedB := g ++ `machine_design_noPortsNR1_closedB
  let gap := g ++ `machine_design_noPortsNR1_closedB_gap
  let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  Lean.logInfo m!"NOPORTS MIXD1 BOUNDARY {g}: {closedB} (from {closed} by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and {gap} on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; {lines.size} binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsMixD1Test; the run, the reflections of mixD1 / midH / cnt / rcH at the run's contexts and ChildBnd at the start world remain premises."
