import Tests.Compiler.NoPortsMemOnlyAtLib
import Tests.Compiler.NoPortsMemOnlyTwoTest

/-! # `twoMems` under `MachineClosesAt`: the depth-0 endpoint of a MEMORY-ONLY parent without the four check premises (G1, unit U4, round par/b-15)

`twoMems`: a `Signal.loop` parent with two register slots and TWO combinational-read memories of one placeholder (aw 4, dw 8).
Its data theorem `twoMems_data : MemOnlyData …` and the four run-hypothesis
theorems `twoMems_runFacts / _outsG0 / _kidsMemG / _designP0` are the BUILT
ones of `Tests.Compiler.NoPortsMemOnlyTwoTest` (they take `MachineClosesAt` already); this file only
runs the built generator in its at-form and audits the result. Shared
pieces and the statement of what the endpoint is:
`Tests/Compiler/NoPortsMemOnlyAtLib.lean`.

The import also brings the exchange endpoint `twoMems.machine_design_noPorts0`
(all-worlds closing `MachineCloses`, which cannot be discharged:
`Tools/ShippingMemOnlyAtAll.lean`); it is not what is audited here.

## EXPECTED (stated before the build; the audit THROWS otherwise)

BASE: `twoMems.machine_design_sv0` (there is no `twoMems.machine_design_svR0`).
The endpoint is a NEW statement, not the base with premises removed
(`Tests/Compiler/NoPortsMemOnlyAtLib.lean`, differences 1–5).

| endpoint | premise | predicted state |
|---|---|---|
| `twoMems.machine_design_noPortsR0` | `shipsHierCheck (childMap D.modules) b` (of the base) | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` (of the base) | predicted absent, pending build |
| | the base's boundary `True` | REPLACED by `ChildBnd mref cref w` — ADDED antecedent (allowed by the classifier) |
| | the base's `MachineCloses twoMems` (all worlds, every logger) | REPLACED by `MachineClosesAt twoMems` — STILL A PREMISE, the one premise NOT ALLOWED; no closed form |
| | `hr`, `MachineDefines twoMems` | stay |

SCOPE: one declaration, depth 0, data conditions decided per declaration
(`MemOnlyData`: conditions, not reductions), compiler guards with fallback,
`DesignSV` of the module list — not the SV string, not `#sim`. The run, the
reflection, `ChildBnd` and `MachineClosesAt` stay premises. The closing is
NOT worked on here.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyAt.logData
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems 3
    [Sparkle.Compiler.MachMemory.memChildName true 4 8]

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
  let name ← Tests.Compiler.NoPortsMemOnlyAt.generateAt f
    ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_runFacts
    ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_outsG0
    ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_kidsMemG
    ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_designP0
  Lean.logInfo m!"NOPORTS MEMONLY AT [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent under MachineClosesAt and ChildBnd, without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents of {f}.machine_design_sv0 — a NEW statement (its closing premise is the at-form, its boundary ChildBnd is added); MachineClosesAt is STILL a binder, no closing is proved"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyAt.auditAt
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
    [``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_entry,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_data,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_runFacts,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_outsG0,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_designP0]
