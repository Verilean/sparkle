# Worker N (par/n-1, rounds 1–2): gate-route parent runs — integrated (target-only)

Integrator, 2026-10-14. Base poc `e8547205`. Taken from `par/n-1`: dd6bd34a (round 1), ce4eb22e (round 2);
worker record `docs/parallel/N-gate-parent-run.md`.

## Measured (cgrun, 3 GiB, swap 0, `-j 1`)
Run `n-r1` (as written): `ShippingGateParentTail`, `ShippingGateDefines`, `ShippingGateConeLeafContract`
built; `ShippingGateParentRuns` FAILED (an `obtain ⟨rfl, st⟩ := lift_runs st` chain: the `rfl` substitution
reintroduced the earlier `st`/`h` and the new ones became inaccessible, so the old hypotheses were used),
`ShippingGateParentPost` FAILED (`show some (.inst …)`: no expected type); the rest failed downstream.
Integrator fixes (no statement changed): fresh names + explicit `subst` in `emitLeaves_single_runs`' chain;
`Stmt.inst` in the `show`.
Run `n-r2`: `ShippingGateParentRuns`, `…Post`, `…Run`, `…RunG`, `ShippingGateConeLeafRuns`,
`Tests.Compiler.GateParentRunTest`, `Tests.Compiler.GateParentRunGTest`: all exit 0 (peak 0.34 GB).
Axioms: `gate_parent_run`, `gate_parent_runG`, `parentUse_gate_parent_run`, `parentUse_gate_parent_runG`:
[propext, Classical.choice, Quot.sound].

## What is proved (scope)
* `gate_parent_run` / `gate_parent_runG`: a returning run of `synthesizeCombinational` on an instance-root
  gate parent ⇒ the shipped module is the zero-width cleanup (or its merge) of a module `M` of
  `InstanceNShape` (ports, the child instance, the assign), with a real child result and the design
  modules — a RUN-SHAPE statement, NOT yet `DesignSV`/source equality of the parent.
* `parentUse_gate_parent_runG` (target-only): premises = the run, **`GateDefines`** (one per-world gate
  reflection: first gate refuses, mixed gate accepts the body under the run's own instance predicate),
  `ChildBnd`; every other side fact decided on the reflected body. `GateDefines` is **NOT in the
  classifier's ALLOWED list**; the round-1 form (`gate_parent_run`) instead carries `EntryDefines` + `tag` +
  `hscalar` + `old` + `accept` (tag, hscalar outside ALLOWED too). Implication lemma: the five round-1
  premises give `GateDefines` (`gateDefines_of_entry`), so it is not a stronger boundary.
* Cone (parentMix): leaf only (`inst_leaf_runs`, `armCont_leaf_contract`, no pinned child). World-level fuel
  induction and the cone theorem NOT written (worker record §9).

## Not claimed
Gate-route parents are NOT counted anywhere: no census row, no design-level endpoint. `ALLOWED` unchanged;
whether `GateDefines` may be admitted like `MachineDefines` is a pending ruling.

## Round 3 (par/n-3, 4fd28a2f): the cone at the world level — BUILT with integrator fixes
Run `n3` (cgrun, `-j 1`), on poc 4343df59 (after the prodMatcherArity? switch). As written:
`ShippingGateConeW` failed (the `subst` after `RunsC.bind` reintroduced the old `hr` — same shadowing
pattern as round 1; `intro instH instC` on a `letI` statement; the lemmas then elaborated with `flatLink`),
`ShippingGateConeRun` (`outStructure` stated at `flatLink`), the test (`decide` on goals with a free `y2`).
Integrator fixes (no statement changed except `outStructure`, generalised over `[LinkCtx]`): fresh name
`hr2`; `letI : HierCtx := hierLink children; letI : ChildSem := C` inside `leafK_contractW`'s proof;
`dsimp only; decide` in the test. All three targets exit 0.
Axioms: `gate_cone_runG`, `parentMix_gate_cone_runG` [propext, Classical.choice, Quot.sound].

What `parentMix_gate_cone_runG` says: from the run, `GateDefines` (NOT ALLOWED, ruling pending) and
`ChildBnd`: the shipped module is the cleanup (or merge) of `M`, the final child cache `mF` satisfies
`CacheInv`, and **IF** `childAdd` is tagged in the run's environment `envR`, `mF`'s `childAdd` entry is
`childModule` and it brings no modules, **THEN** `ParentMixObserves M`. Those three run-value facts are
antecedents NOT discharged (the tag is not yet derived from `GateDefines`' acceptance of a cone body).
World-level cone: leaves, literals, `binary` only; compare / Bool ops / mux / setw / slices / concats and
instance leaves with instance arguments (`parentNested`) NOT covered. Not counted anywhere.
