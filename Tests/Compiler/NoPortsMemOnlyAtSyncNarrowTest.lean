import Tests.Compiler.NoPortsMemOnlyAtLib
import Tests.Compiler.NoPortsMemOnlySyncTest

/-! # `syncNarrow` under `MachineClosesAt`: the depth-0 endpoint of a MEMORY-ONLY parent without the four check premises (G1, unit U4, round par/b-15)

`syncNarrow`: a `Signal.loop` parent with two register slots and ONE synchronous-read memory (aw 3, dw 5).
Its data theorem `syncNarrow_data : MemOnlyData …` and the four run-hypothesis
theorems `syncNarrow_runFacts / _outsG0 / _kidsMemG / _designP0` are the BUILT
ones of `Tests.Compiler.NoPortsMemOnlySyncTest` (they take `MachineClosesAt` already); this file only
runs the built generator in its at-form and audits the result. Shared
pieces and the statement of what the endpoint is:
`Tests/Compiler/NoPortsMemOnlyAtLib.lean`.

The import also brings the exchange endpoint `syncNarrow.machine_design_noPorts0`
(all-worlds closing `MachineCloses`, which cannot be discharged:
`Tools/ShippingMemOnlyAtAll.lean`); it is not what is audited here.

## EXPECTED (stated before the build; the audit THROWS otherwise)

BASE: `syncNarrow.machine_design_sv0` (there is no `syncNarrow.machine_design_svR0`).
The endpoint is a NEW statement, not the base with premises removed
(`Tests/Compiler/NoPortsMemOnlyAtLib.lean`, differences 1–5).

| endpoint | premise | predicted state |
|---|---|---|
| `syncNarrow.machine_design_noPortsR0` | `shipsHierCheck (childMap D.modules) b` (of the base) | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` (of the base) | predicted absent, pending build |
| | the base's boundary `True` | REPLACED by `ChildBnd mref cref w` — ADDED antecedent (allowed by the classifier) |
| | the base's `MachineCloses syncNarrow` (all worlds, every logger) | REPLACED by `MachineClosesAt syncNarrow` — STILL A PREMISE, the one premise NOT ALLOWED; no closed form |
| | `hr`, `MachineDefines syncNarrow` | stay |

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
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow 3
    [Sparkle.Compiler.MachMemory.memChildName false 3 5]

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
  let name ← Tests.Compiler.NoPortsMemOnlyAt.generateAt f
    ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_runFacts
    ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_outsG0
    ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_kidsMemG
    ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_designP0
  Lean.logInfo m!"NOPORTS MEMONLY AT [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent under MachineClosesAt and ChildBnd, without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents of {f}.machine_design_sv0 — a NEW statement (its closing premise is the at-form, its boundary ChildBnd is added); MachineClosesAt is STILL a binder, no closing is proved"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyAt.auditAt
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
    [``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_entry,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_data,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_runFacts,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_outsG0,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_designP0]
