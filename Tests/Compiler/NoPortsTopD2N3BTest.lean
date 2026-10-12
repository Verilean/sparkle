import Tests.Compiler.NoPortsTopD2N3Test
import Tests.Compiler.NoPortsGrandHBTest

/-! # `topD2` at depth 3: the boundary of the closed check-free endpoint, reduced to `ChildBnd` (G1, unit U3, round par/a-16)

`topD2.machine_design_noPortsNR3_closed` (`NoPortsTopD2N3Test`, WRITTEN)
inherits the boundary of `topD2.machine_design_svNR3`.

MEASURED on the BASE closed endpoint (`verification-a14.md` 134–138,
`BoundaryCloseBaseProbe`): on `topD2.machine_design_svNR3_closed`
`#machine_boundary_close` KEEPS only the four check premises — every
conjunct of the depth-3 boundary is DERIVED from the four reflection binders
(`topD2`, `mid2`, `midH`, `rcH`). The closed form of this round has the same
four reflection binders (asserted by the audit of `NoPortsTopD2N3Test`), so
the same derivation is predicted; the audit here THROWS if a conjunct is
kept.

| endpoint | premise of `topD2.machine_design_noPortsNR3_closed` | predicted state |
|---|---|---|
| `topD2.machine_design_noPortsNR3_closedB` | antecedent conjuncts other than `ChildBnd` (reflections, the nested ∀-contexts conjuncts) | WRITTEN, NOT BUILT — predicted absent from the antecedent, pending build |
| | `ChildBnd mref cref w` | STAYS (the one antecedent) |
| | binders (run, `MachineDefines topD2 / mid2 / midH`, `EntryDefines rcH`) | STAY, none added |
| `…_closedB_gap` | gap hypotheses | predicted NONE, 0 NOT ALLOWED |

UNVERIFIED at the time of writing: this file was not built (and it depends
on a file that was not built). -/

set_option maxHeartbeats 0 in
#machine_boundary_close
  Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let closed := g ++ `machine_design_noPortsNR3_closed
  let closedB := g ++ `machine_design_noPortsNR3_closedB
  let gap := g ++ `machine_design_noPortsNR3_closedB_gap
  let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  Lean.logInfo m!"NOPORTS TOPD2 N3 BOUNDARY {g}: {closedB} (from {closed} by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and {gap} on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; {lines.size} binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsTopD2N3Test (depth 3); the run, the reflections of topD2 / mid2 / midH / rcH at the run's contexts and ChildBnd at the start world remain premises."
