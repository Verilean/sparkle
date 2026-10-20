import Tests.Compiler.NoPortsTopD2Test
import Tests.Compiler.NoPortsGrandHBTest

/-! # `topD2`: the boundary of the closed check-free depth-2 endpoint, reduced to `ChildBnd` (G1, unit U3, round par/a-15)

`topD2.machine_design_noPortsNR2_closed` (`NoPortsTopD2Test`, WRITTEN)
inherits the boundary of `topD2.machine_design_svNR2` — BY READING of the
generator (`Tools/ShippingMachineDepthCommandR.lean` 85–100, 276–336; not a
log of this statement):

    ChildBnd mref cref w ∧
      MachineDefines … mid2 … ∧ names(mid2) ∧
        ∀ mctx' cctx', ChildRanIn mref cref `mid2 mctx' cctx' →
          ∀ wc raw D, ChildBnd mref cref wc → Bnd_mid2 mctx' cctx' wc raw D

with `names(mid2)` the reflection of `rcH` at the run's contexts (INFERRED:
the premise of `mid2`'s closing about a descendant that is not a direct
child) and `Bnd_mid2` holding `midH`'s reflection and `midH`'s own boundary
(`EntryDefines rcH` in the contexts `midH` is synthesised in) one level
deeper. The binders of the closed form: the run and the reflections of
`topD2`, `mid2`, `midH`, `rcH`.

MEASURED on the BASE closed endpoint (`verification-a14.md` 129–133,
`BoundaryCloseBaseProbe`): on `topD2.machine_design_svNR2_closed` the same
command KEEPS only the four check premises — every conjunct of the boundary
is DERIVED from the same four reflection binders there (no
`MachineClosesAt mid2` conjunct is kept: the question left open in
`A-remaining.md` §6.2 is answered by that log). The audit THROWS if a
conjunct is kept here.

| endpoint | premise of `topD2.machine_design_noPortsNR2_closed` | predicted state |
|---|---|---|
| `topD2.machine_design_noPortsNR2_closedB` | antecedent conjuncts other than `ChildBnd` (reflections, the two nested ∀-contexts conjuncts) | WRITTEN, NOT BUILT — predicted absent from the antecedent, pending build |
| | `ChildBnd mref cref w` | STAYS (the one antecedent) |
| | binders (run, `MachineDefines topD2 / mid2 / midH`, `EntryDefines rcH`) | STAY, none added |
| `…_closedB_gap` | gap hypotheses | predicted NONE, 0 NOT ALLOWED |

UNVERIFIED at the time of writing: this file was not built (and it depends
on files that were not built). -/

set_option maxHeartbeats 0 in
#machine_boundary_close
  Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let closed := g ++ `machine_design_noPortsNR2_closed
  let closedB := g ++ `machine_design_noPortsNR2_closedB
  let gap := g ++ `machine_design_noPortsNR2_closedB_gap
  let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  Lean.logInfo m!"NOPORTS TOPD2 BOUNDARY {g}: {closedB} (from {closed} by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and {gap} on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; {lines.size} binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsTopD2Test (depth 2 only); the run, the reflections of topD2 / mid2 / midH / rcH at the run's contexts and ChildBnd at the start world remain premises."
