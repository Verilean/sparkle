import Tests.Compiler.ShippingCallsCloseDeepTest
import Tests.Compiler.NoPortsTest
import Tools.ShippingBoundaryClose

/-! # PROBE (logs only): `#machine_boundary_close` on the BASE depth endpoints (round par/a-14)

The base family `f.machine_design_svNR{n}(_closed)` keeps its four check
premises; this probe only measures what `Tools/ShippingBoundaryClose.lean`
does to their BOUNDARY antecedent. Nothing is asserted: every command is
the `_try` form (`BOUNDARY CLOSE` with one line per conjunct — `DERIVED` /
`KEPT` — or `BOUNDARY CLOSE REFUSED` / `ABSENT`), and the last `run_cmd`
logs the premise listing of each `…B` theorem that was added.

PREDICTIONS BY READING (`docs/parallel/A-remaining.md` §6.2), none built:

* `grandH.machine_design_svNR1_closed`, `…NR2_closed`: boundary → `ChildBnd`.
* `mixD1.machine_design_svNR1_closed`, `…NR2_closed`: boundary → `ChildBnd`.
* `topD2.machine_design_svNR2_closed`, `…NR3_closed`: boundary → `ChildBnd`
  IF `mid2`'s conjunct has no `MachineClosesAt mid2` and its name conjuncts
  are `True` (not read off a statement); otherwise the `mid2` conjunct is KEPT.
* `mixDeep.machine_design_svNR2` (NO closed form: `#machine_closes_deep
  mixDeep` was never run): the ∀-contexts conjuncts are KEPT — the
  reflections of `midH`, `rcH` at the run's contexts are not binders.
* `grand.machine_design_svNR2_closed`: child `mid` (general closing over the
  leaf `cnt`); not read — measured here.

TARGET-BUILT ONLY, not for `Tests/AllTests.lean`: it leaves `…B` constants
under the base endpoints' names.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR1_closed
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2_closed
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR1_closed
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2_closed
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR2_closed
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3_closed
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_svNR2
set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_svNR2_closed

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for e in [``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH ++ `machine_design_svNR1_closedB,
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH ++ `machine_design_svNR2_closedB,
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 ++ `machine_design_svNR1_closedB,
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 ++ `machine_design_svNR2_closedB,
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 ++ `machine_design_svNR2_closedB,
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 ++ `machine_design_svNR3_closedB,
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep ++ `machine_design_svNR2B,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand ++ `machine_design_svNR2_closedB] do
    if (← Lean.getEnv).contains e then
      let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines e
      Lean.logInfo m!"BOUNDARY PROBE {e}: {lines.size} premises, {bad.size} NOT ALLOWED (the four check premises are expected among them)\n{String.intercalate "\n" lines.toList}"
    else
      Lean.logInfo m!"BOUNDARY PROBE {e}: not added"
