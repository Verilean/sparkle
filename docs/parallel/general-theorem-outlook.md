# Outlook toward the general theorem (integrator, par/int-r23; reviewer's grouping)

Status words: PROVED / PREMISE / OPEN. Progress is NOT measured by theorem or build counts. Nothing below is runtime
fit, CI, or general semantic preservation. Rows refer to docs/parallel/main-theorem-connection.md.

What is in hand (PROVED relative to the stated premises, cluster-verified):
* The compiler's own run keeps its state invariant on the new boundary (JQ / JQC triples) from `O`, `AdmCtx`, the start
  world and two telescope laws (`telescope`, `lamTelescope`; `localDecl`/`letDecl` PROVED from `O`).
* Run decomposition, children as `RealChildA` histories, closing of calls (`MachineClosesAtA` from `LetsClose` +
  `CallsPureA`; cache pin PROVED, repeated callees covered), machine/legacy outcome split with the original end world.
* Concrete heads on the new boundary: leaf `dead7` (design level), parent `callerMix` entry → `ComposedH` in one chain
  (hfn/hcalls/trace/closes discharged), a non-memory two-field parent up to the design endpoint with mask/facts/outs/
  designCheck supplied.

What blocks the general theorem, by kind:

| # | kind | open items (rows) | what would close it |
|---|---|---|---|
| 1 | real reader correspondence | `TwinCoverAt`; `RootFloatAgrees`, `LiftAgrees`, `Inst1Agrees` (C++ externs); `letsAliasOk` for real shapes (L6c–L6c7) | a kernel-provable reader definition (unit LC8 prototype: `partial_fixpoint` from FM.step/compact_step, acceptance `prototype = some r ↔ ∃ fuel, readF = some r`), then a reviewed production switch or a proved refinement; externs stay premises (evidence by C++ reading) |
| 2 | real world / environment / initial conditions | `O.quiet` and a non-empty `quiet` witness; `StartContents` at load and across non-entry code; `EnvSnapshot` (w1, w2) and env preservation through Lean's `whnf`/`inferType`/…; `EnvDefines` all-world consistency; runtime fit / joint satisfiability of `O` and the two telescope laws (L9–L9b, L8m–L8o, runtime-contract-OT.md) | a runtime model of `O` (heap model → `ST`), or explicit per-command premises kept as the theorem's boundary; env preservation needs a law about `Core.State` or a model of the Lean API calls |
| 3 | machine-route child semantic composition | parent `soundL` / `composed` for machine-route children (`cnt`), `MachineRunNCA`→composed beyond `callerMix`, remaining ServedReal consumers (L8e–L8q; unit SR3h) | one theorem from a machine child's `RealChildA` + `MachineRanA` + its own trace to the parent's `soundL`/`composed`, then a generator for the class |
| 4 | input shape / quote / reflection | `LetOk 0` of the declaration body (input condition), the Expr → typed `letFields` / `quote` link, loose-bvar scoping, `EnvTypesFVarFree` (L6c2–L6c5) | reader specification lemmas on the provable reader of #1; closedness facts of elaborated declarations |
| 5 | target-class generalisation | per-instance heads (`dead7`, `callerMix`, one masked parent, CT/CPX instances); memory parents with origin-built children (`hnomem`); command heads; the legacy route's semantics (only split off, L7e*) | generators producing the new-boundary heads per class (as the old `#machine_*` commands did), then a statement quantified over the accepted class |

Order that removes the most structural risk first (proposal, not a schedule): #1 prototype (it decides whether the reader
can be reasoned about at all), #3 for one machine child (it decides the parent semantic shape), then #5 generators;
#2 and #4 are boundary conditions that remain explicit premises until a runtime/environment model is chosen.
