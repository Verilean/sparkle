import Tests.Compiler.NoPortsGrandTest
import Tests.Compiler.NoPortsGrandHBTest

/-! # `grand`: the boundary of the closed check-free depth-2 endpoint, reduced to `ChildBnd` (G1, unit U3, round par/a-15)

`grand.machine_design_noPortsNR2_closed` (`NoPortsGrandTest`, WRITTEN) has,
BY READING of the generator (`Tools/ShippingMachineDepthCommandR.lean`
276–336; not a log of this statement), the one antecedent

    ChildBnd mref cref w ∧
      MachineDefines … mid … ∧ names(mid) ∧
        ∀ mctx' cctx', ChildRanIn mref cref `mid mctx' cctx' →
          ∀ wc raw D, ChildBnd mref cref wc → Bnd_mid mctx' cctx' wc raw D

where `Bnd_mid` is `mid`'s own boundary (INFERRED: `ChildBnd wc ∧
MachineDefines mctx' … cnt …` — `cnt` is a leaf whose closing is proved) and
`names(mid)` is `True` (INFERRED: every reflection premise of
`mid.closes_deep` is of a DIRECT child of `mid`), and the reflection binders
of `grand`, `mid`, `cnt`.

MEASURED on the BASE closed endpoint (`verification-a14.md` 146–150,
`BoundaryCloseBaseProbe`): on `grand.machine_design_svNR2_closed` the same
command KEEPS only the four check premises — the boundary's conjuncts are
all DERIVED from the binders there. The check-free closed endpoint has the
same boundary and the same reflection binders, so the same derivation is
expected; the audit THROWS if a conjunct is kept.

| endpoint | premise of `grand.machine_design_noPortsNR2_closed` | predicted state |
|---|---|---|
| `grand.machine_design_noPortsNR2_closedB` | antecedent conjuncts `MachineDefines mid`, `True` | WRITTEN, NOT BUILT — predicted absent from the antecedent, pending build |
| | antecedent conjunct `∀ mctx' cctx', ChildRanIn … mid … → …` (NOT ALLOWED) | predicted absent, pending build |
| | `ChildBnd mref cref w` | STAYS (the one antecedent) |
| | binders (run, `MachineDefines grand`, `MachineDefines mid`, `MachineDefines cnt`) | STAY, none added |
| `…_closedB_gap` | gap hypotheses | predicted NONE, 0 NOT ALLOWED |

UNVERIFIED at the time of writing: this file was not built (and it depends
on files that were not built). -/

set_option maxHeartbeats 0 in
#machine_boundary_close
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
  let closed := g ++ `machine_design_noPortsNR2_closed
  let closedB := g ++ `machine_design_noPortsNR2_closedB
  let gap := g ++ `machine_design_noPortsNR2_closedB_gap
  let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  Lean.logInfo m!"NOPORTS GRAND BOUNDARY {g}: {closedB} (from {closed} by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and {gap} on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; {lines.size} binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsGrandTest; the run, the reflections of grand / mid / cnt at the run's contexts and ChildBnd at the start world remain premises."
