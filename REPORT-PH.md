# REPORT-PH — first PARENT head on the new boundary (branch par/u-ph, base d93bc4ad)

## Scope (exact)
PROVED: the CHECK level of one concrete parent, `callerMix` (two DISTINCT one-output gate children `pick`, `pickD`),
on the new boundary: `designCheck (childMap D.modules) 0 (checkedOptimize b) = true`, `RunFactsH`, `outsCheck`,
`portsMatchB` (raw and shipped), `hierTyped` — the statements of the generated `callerMix.machine_{factsH,outsH,
portsRawH,portsShippedH,hierTypedH,designFullH}`. This is NOT a parent semantic-equivalence head and NOT the endpoint
`callerMix.machine_design_svH_full`: its semantic part (`machine_composedRA` / `ServedReal` / `soundL`) still takes
`ChildBnd` — OPEN (not attempted). Not runtime fit; not general hierarchical preservation.

## Old theorem and where ChildBnd / MachineClosesAt / ChildrenReal were consumed
Old: `callerMix.machine_designFullH` = `core_designCheckH` (ShippingOneOutFacts) at `callerMix.machineData`, binders
`hcore hpost entry (closes : MachineClosesAt) (hB : ChildBnd) hR0 hR1`. Consumption: every base lemma of the chain
(`core_kids_facts`, `core_linkedWF`, `core_closed_typedIn`, `core_hierGate_any`, `core_closeInsts`, `core_rst_any`,
`core_calls_ports₁`, `core_callConns₁`, …) starts with `machine_run_of_core hcore entry hB` + `closes …` +
`synthesizeMachineCertified_runs` (old `InvW` → `ChildrenReal`); per-child facts are stated on `RealChild`.

## What was done
* `Tools/ShippingParentRanA.lean`: `MachineRanA O mctx cctx c shape M D` (the machine synthesis returned `some (M,D)`,
  harness/`closeLets`/closing exposed, children `ChildrenRealA O`) and `machineRanA_main` (from `O`, `hA`, `T`,
  `hw : JQ O.quiet D₀ w` (+`CacheInvA` if `D₀≠0`), run, `MachineDefines`, `MachineClosesAtA`) via G's
  `machine_run_of_coreA`, G2's `bodyStepC_of_tele`/`htr_of_tele`, G's `synthesizeMachineCertified_runsA`.
* `Tools/ShippingParentTailsA.lean`, `ShippingParentDesignA.lean`, `ShippingParentPortsA.lean`: the `_ran` tails (and
  the non-`_ran` lemmas rewritten to the same shape) of the old chain, with `MachineRan` → `MachineRanA O`,
  `RealChild mref cref` → `RealChildA O`, `ChildrenReal` → `ChildrenRealA O`, hypothesis block
  `hB hcore entry closes` → `ran`. Generated mechanically by `.cluster/logs/gen_ph.py` (not committed: git-ignored
  scratch; proofs verbatim except the head, each compiled). Main: `core_designCheckHA`, `core_runFactsHA`,
  `core_portsMatch_raw₁A`, `core_hierTyped₁A`, `core_outsCheck_all_gate_ranA`.
* `Tools/ShippingParentGateA.lean`: `gate_real_portsA`, `gate_real_kidKA` (the old ones unpack `RealChild` with
  `h.inv`; these `cases` the `RealChildA` run).
* `Tests/Compiler/ParentDesignCheckATest.lean`: `callerMix_closesA` — `MachineClosesAtA` DISCHARGED by CA's
  `machineClosesAtA_of_gateKids` (RESTRICTED to distinct callees: `hnodup` is `decide`d for `[pick, pickD]`) — and the
  six check theorems `callerMix_{factsHA,outsHA,portsRawHA,portsShippedHA,hierTypedHA,designFullHA}`; audit
  (`auditParentA`, THROWS) and conclusion `isDefEq` check against the six generated old theorems (`sameConclusionA`,
  THROWS) are in the same file. Registered in Tests/AllTests.lean; all new theorems added to
  `ChildVertAuditTest.audited` (review items 2, 3 applied; item 1: scope wording in headers, ledger L8c, here).

## Remaining premises of the concrete theorems (callerMix_designFullHA etc.)
* `O : RefLawsAOps MkRefd mref cref` — PREMISE (law family; runtime fit OPEN; inconsistency NOT PROVEN).
* `T : RefLawsATele O.quiet mref cref` — PREMISE, ADDED unproved boundary (enters via `BodyStepC`/`htr`, G2). Never
  premise-free.
* `hA : AdmCtx O.quiet mctx cctx` — PREMISE (real command context OPEN).
* `hw : JQ O.quiet 0 w` — PREMISE (start world OPEN, L9). No `cv w = {}`, no `ChildBnd`.
* the run `hcore`, `hpost`, `entry : MachineDefines callerMix` — PREMISES (as in the old theorem).
* `hR0 : EntryDefines pick`, `hR1 : EntryDefines pickD` — PREMISES (as in the old theorem).
* PROVED inside: `MachineClosesAtA` (restricted: distinct callees), `ChildrenRealA`, `RunFactsH` parts, all
  `callerMix.oneout_*` data conditions (decided, generated earlier), `outTy`/`outScalar` (reader).
`RealChildA`/`ChildrenRealA` are histories of past synthesis results, not freshness or correctness in the current
environment. Nothing filled by axiom/opaque/sorry/native_decide. No new law/field.

## OPEN / missing
* The endpoint `callerMix.machine_design_svH_full` (semantic `DesignSV` conclusion): `machine_composedRA`,
  `ServedReal`, `soundL` take `ChildBnd`; not ported.
* Repeated-callee parents (`callerTwice`, `callerRep`, `callerABA`): `hnodup` excludes them (CA).
* Machine-leaf callees (`callerL`, `callerLN`), memory/general-closing (`instFields ≠ []`) parents: not ported.
* The `hports`-free `portsShipped` for other parents needs the same per-callee `gate_*A` helpers (done for `pick`,
  `pickD` in the test only).

## Builds (all through ./.cluster/qbuild.sh)
ph1 RanA exit 1 (unknown `profLogIO`); ph2 RanA exit 0; ph3 TailsA exit 1 (missing `open Tools.ShippingHierOpen`);
ph4 TailsA exit 0; ph5 DesignA exit 0; ph6 PortsA exit 1 (missing opens `closeMachine_inputs`, `callArgsOk`);
ph7 PortsA exit 0; ph8 GateA exit 0; ph9 test (kids lemmas) exit 0; ph10 test exit 1 (ident/namespace fixes);
ph11 test (six check theorems) exit 0; ph12 test+audit exit 1 (premise counts, hygienic binder names);
ph13 test+audit+conclusion checks exit 0; ph14 ChildVertAuditTest exit 0 (all 18 new theorems audited, no RefLaws…
in closure); ph15 final rebuild of ParentDesignCheckATest + ChildVertAuditTest after header edits exit 0.
Tests.AllTests not built (integrator only).

## #print axioms
`callerMix_designFullHA`, `callerMix_closesA`: propext, Classical.choice, Quot.sound (printed in ph13/ph15 logs;
audit `stdAxioms` THROWS otherwise for all seven callerMix theorems and all 18 audited Tools theorems).
Structural boundary counts (opaque/extern/implemented_by) are not a runtime-fit proof.

## Commits
See `git log par/u-ph` (explicit-path commits; no trailers).
