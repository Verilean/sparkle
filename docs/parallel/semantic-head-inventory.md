# Semantic-head inventory — what a parent SEMANTIC head still takes from the OLD boundary (unit SR, base int-r12 e5831ec0)

Words: **PROVED** (kernel-checked, built), **PREMISE** (hypothesis), **OPEN**. Read from the proofs, not the names.
Nothing here is runtime fit, CI, or general semantic preservation. `RealChildA` is a history of past
synthesis results, `JQC` is not freshness, `MkRefd` is a history.

## 0. Summary

| piece | where | old-boundary use | portable by | status |
|---|---|---|---|---|
| `ServedReal` (def) | Tools/ShippingMachineTraceX.lean:418/438/453 (`ServedRealG`, `ServedReal1`, `ServedReal`) | statement mentions `Tools.ShippingChildInv.RealChild mref cref callee (mc, Dc)` (old inductive, ShippingChildInv.lean:453) | replace by `RealChildA O` | **PROVED** `Tools.ShippingServedRealA.ServedRealA` (+ `realChildA_inv`, `machineRunJQC_of_closesA`; own def `MachineRunJQC`, distinct from unit PH's `MachineRanA`) |
| `ServedReal` (proof) | `synthesizeCombinationalCore_machine_soundRA_ran` (TraceX:468) | ONE use: `synthesizeMachineCertified_runs hw9 hrun` (ShippingChildRun.lean:538) which needs `InvW mref cref w9` (old RefLaws witness inside, `invV_of_invW`). The `MachineRan` start world `InvW ∧ DepthPos` | run fact: G's `machine_run_of_coreA` + `synthesizeMachineCertified_runsA` (premises `BodyStepC O`, `htr` at `JQC O n`), `MachineClosesAtA` | **PROVED** `…_machine_soundRA_ranA`, `…_soundRA_A`, `…_soundRA_main` (from `T`; sr3, sr8 exit 0) |
| trace `soundL` for a LEAF | premise of `leaf_sat_design_closed5` (ShippingLeafInputWidths.lean:317), same in `machine_ships_wired` (ShippingMachineShipsW.lean:47) | NONE: statement quantifies over all runs/worlds with `MachineCloses` (all-worlds), has no `ChildBnd`/`InvW`; proof is `synthesizeCombinationalCore_machine_sound` (ShippingMachineEntry.lean:2318, no boundary binder) | nothing to port | already boundary-free (read: no `ChildBnd`, `RefLaws`, `InvW` in the statement) |
| trace `soundL` for a PARENT (`MachineTraceLBX (ServedReal …)`) | `machine_trace_lets_of_streamBRA(_ran)` TraceX:575/733, `…BR` :787 | `hsyn : ChildBnd mref cref w` -> `machineRan_of_closes` (`machine_run_of_core`); type carries `ServedReal` | same as above | **PROVED** `Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA`, `…_A`, `…_main` (premises `O`,`hA`,`T`; sr5, sr8 exit 0). Scope: a trace WITH child history (`MachineTraceLBX (ServedRealA …)`), NOT composed-parent semantic equivalence |
| consumer 1 of `ServedReal`'s `RealChild`: `machineRunNC_of_real` | Tools/ShippingMachineDepthRunR.lean:247 | `hreal : RealChild …`, `hreal.ranIn` (`InvW`), `ChildBnd.of_invW`, `hctx : ChildRanIn → ChildBnd w → Bnd …`, `machine_children_realA` (old, needs `ChildBnd`, `MachineClosesAt`) | run facts of the child's own run: `realChildA_inv` (data of the start world: `AdmCtx`, cache half, `sv`, `quiet`) + `machine_children_realA'` | **PROVED (unit SR2)** `Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real(_main)`; premises: child's `hctx`/`hcl` (`MachineClosesAtA`) |
| consumer 2: the `hrc.inv` step in `machine_linkedT_callsRN` | TraceX-user files ShippingMachineCallsLinkedTNR.lean:290, ShippingMachineCallsLinkedTR.lean:~239/287, ShippingMachineCallsLinkedTG.lean:~505/557, ShippingComposedGW.lean:~92/148 | `RealChild.inv` -> `InvW w`, hypothesis `hrunN`/`hcl` quantified over `InvW mref cref w` and `ChildRanIn` | restate with `realChildA_inv`'s data and `ChildRanIn` replaced by an `AdmCtx`-form | **PROVED for TNR (unit SR2)** `machine_linkedT_callsRNA`; TR/TG/ComposedGW still OPEN |
| consumer 3: `core_kids_self` etc. | ShippingKidsSelf.lean:95,148,153,180,238,245,277,309,312 | `RealChild … y`, `ChildBnd mref cref w` (consumed through `machine_run_of_core`/`machineRan_of_closes`) | `RealChildA`, `MachineRanA` | **OPEN** |
| composed-semantics heads | ShippingMachineComposeR, SeqLinkedR (`hsyn : ChildBnd`, lines 88,179,241,279,…), NestR, TeleNestR; commands DepthCommandR, ComposeRCommand, SeqCommandR, DepthMemKidCommand, OutermostCommand | `ChildBnd` as the start premise, passed to `machine_trace_lets_of_streamBR` (ServedReal) and to `ChildRanIn`/`CtxBnd` data | the same two ports above (these files only pass `hsyn` down) | **OPEN** |

## 1. ServedReal — read of the proof

`ServedRealG`/`ServedReal1` (TraceX:418–458): for each call `k`, the instance serving it has as module either the
origin-built child of the shape (memory module) or `RealChild mref cref (shape.insts[k]).1 (mc, Dc)` plus
`Dc.modules` consistent with the parent design. The `RealChild` constructor (ShippingChildInv.lean:453) keeps:
contexts `mctx cctx`, start world `w`, `cache : every entry of cv w is RealChild`, `synth : SynthAt w`,
`quiet : ∃ L : RefLaws, L.quiet w`, the run. The NEW `RealChildA` (ShippingChildCacheA.lean:105) keeps
`adm : AdmCtx O.quiet mctx cctx`, `cache : CacheInvA`, `synth : sv w = some synthesizeChild`, `quiet : O.quiet w`, run.

Proof (`…_soundRA_ran`, TraceX:468–541): the only old-boundary object is the world invariant obtained by
`MachineRan`'s `InvW mref cref w9 ∧ DepthPos` fed to `synthesizeMachineCertified_runs`, whose `ChildrenReal`
conclusion gives the `RealChild`. Everything after (`synthesizeMachineCertified_soundX`, `closeInsts_serves`,
`closeInstsG_serves`, `closeInsts(G)_acyclic`, `closeInstsG_names`) is boundary-free (they take only the closing's
`CloseCalls`). So `ServedReal` is a RUN fact about the machine synthesis' start world: portable via G
(`machine_run_of_coreA` gives `JQC O (D+1) w9`) and G's `synthesizeMachineCertified_runsA`. Memory-origin children
(`child? = some md`) need no boundary.

## 2. What the new `ServedRealA` costs (premises)

`O`, `hA : AdmCtx O.quiet mctx cctx`, `BodyStepC O` (ComposeC `bodyStepC_of_tele`, from `T`), `htr` at `JQC O n`
(G2 `htr_of_tele`), `MachineClosesAtA` (PREMISE; CA/CN2/CT/CM/GMP prove it for restricted shapes), `MachineDefines`, the
start `JQ O.quiet D w` (+ `CacheInvA O (cv w)` if `D ≠ 0`). A leaf (`insts = []`) never reaches the closing: `ServedRealA`
is vacuous there (both conjuncts are about `instFields`/`insts`), consistent with L8a needing no `BodyStepC`.

## 3. Missing conditions found / next pieces

* Nothing in `ServedReal` needs a fact the new boundary does not give.
* `machineRunNC_of_real` (next on the path, all heads with calls use it through `hcl`/`hctx`): it re-runs the CHILD's
  core entry and needs the child's start world as a **`JQ`-form** world. `RealChildA` does NOT record the depth of its
  start world `w` (only `quiet`, `sv`, `CacheInvA`); `machine_run_of_coreA` needs `JQ O.quiet D w`, so take `D := dv w`
  (`JQ` is `quiet ∧ sv ∧ dv = D`: available). The cache half is exactly `CacheInvA O (cv w)` — available. So no missing
  condition; but the child's `BodyStepC`, `htr`, and `MachineClosesAtA` for the CHILD are new premises per call
  (the old head had `hcl : … → MachineClosesAt`), and the boundary hypothesis `hctx` must be re-stated over
  `AdmCtx ∧ JQ ∧ CacheInvA` worlds instead of `ChildBnd mref cref w`.
* `ChildRanIn` (old, ShippingChildInv.lean:846) is stated with `InvW` at the start world; an `…A` version is needed
  for the `hcl` hypotheses of CallsLinkedTR/TG/GW.

## 4. Ledger row (for docs/parallel/main-theorem-connection.md, L8c)

L8c (unit SR): `ServedReal` and the parent trace theorem on the new boundary — `Tools.ShippingServedRealA` (`ServedRealA`, `realChildA_inv`, `machineRunJQC_of_closesA`, `synthesizeCombinationalCore_machine_soundRA_ranA/_A/_main`) and `Tools.ShippingServedRealATrace` (`machine_trace_lets_of_streamBRA_ranA/_A/_main`). PROVED relative to `O`, `hA`, `T` (for `_main`; `BodyStepC`/`htr` explicit for `_A`), `MachineDefines`, `MachineClosesAtA` (PREMISE), start `JQ O.quiet D w` (+ `CacheInvA` if `D ≠ 0`). Built sr3/sr5/sr8 exit 0; audit sr8: no RefLaws/RefLawsCore/toAOps/toA in closure. A trace with child history, not composed-parent semantic equivalence; `RealChildA` is a history; not runtime fit. OPEN: `machineRunNC_of_real`, the `hrc.inv` consumers (CallsLinkedTR/TG/TNR, ComposedGW), `core_kids_self` family, `ChildRanIn`, command heads.
