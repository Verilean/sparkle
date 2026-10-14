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

## Round 4 (par/n-4, ac490c7c): the leaf tag derived — BUILT as written
Run `n4` (`-j 1`): `Tools.ShippingGateConeTag`, `Tests.Compiler.GateConeTagTest` exit 0, no fix needed.
Axioms: `parentMix_tag`, `parentMix_gate_cone_runG'` [propext, Classical.choice, Quot.sound].
* (a) DISCHARGED generally: `gate_leaf_tag` / `gate_leaf_tag'` — the gate's acceptance (under
  `instancePredicate env`) of a cone body whose instance leaf is selected (`GateLeafSel`, decided per
  declaration via `bvarCall`) gives `isHardwareModule env mn = true`. `parentMix_gate_cone_runG'` concludes
  the tag at `envR` instead of assuming it.
* (b) `y.1 = childModule` and (c) `y.2.modules = []` REMAIN antecedents of the conclusion. `childAdd` is a
  FIRST-gate child (`certifiedShape?` accepts it): the existing RealChild facts assume the first gate
  refuses. (b) asks for text equality with a hand-written constant — no theorem pins module text and a
  `RunsTo` is not kernel-computable, so (b) is to be REPLACED by an observation against the run's own child
  (worker record §17). Next unit (no compiler change): first-gate child facts from `RealChild` +
  `EntryDefines childAdd` (ALLOWED), and a design-frame lemma for (c).

## Round 5 (par/n-5, e854565b): first-gate child facts; parentMix without run-value antecedents — BUILT
Run `n5` (`-j 1`). As written: `ShippingFirstGateChild` failed once (`admissible_zero` ambiguous between
`ShippingGateChild` and `ShippingMachineEntry`); integrator fix: qualified name. Then
`Tools.ShippingFirstGateChild`, `Tools.ShippingFirstGateKid`, `Tests.Compiler.GateConeKidTest`: exit 0.
Axioms: `kidFacts_of_first`, `parentMix_gate_cone_runK` [propext, Classical.choice, Quot.sound];
`addSem_spec` [propext, Quot.sound]. `example : childAddEntry = childAddValue := rfl` builds (the premise's
value IS the real entry constant).
* General (any first-gate child `quoteDecl dn names n fe`, `fe.WF`, `0 < n`): bridge
  `bindCertified_mixed` (first-gate harness = mixed harness on `mixB` binders), `fragmentDecl_of_entry`,
  full-entry outputs / inputs (Nodup, Allocated, not clk/rst/out), core design has no modules,
  `first_child_fullFacts`, `ChildFnR` (ChildFn without its unused `rst = 0` premise; copies of the built
  proofs), `kidFacts_of_first` (`KidFacts (ownChild y) …` from `RealChild` + `EntryDefines`).
* `parentMix_gate_cone_runK` (target-only): premises the run, `GateDefines` (NOT ALLOWED, ruling pending),
  `ChildBnd`, `EntryDefines childAdd` (ALLOWED). Conclusion: post ∧ `CacheInv mF` ∧ tag at `envR` ∧
  `∀ y, mF.get? ``childAdd = some y → ParentMixObservesC (ownChild y) M` — no run-value antecedent left;
  observation against the run's OWN cached child (replaces the hand-written `childModule`).
  NOT concluded: that the cache entry exists (the statement is about every entry found). Cone at the world
  level: binary fragment only; `parentNested` not covered. Not counted anywhere.

## Round 6 (par/n-6: 985d88d6, 6f48b6a7, 70ff3968) — BUILT as written
Run `n6` (`-j 1`): `Tools.ShippingGateConeEntry`, `Tests.Compiler.GateConeEntryTest`,
`Tools.ShippingGateConeCompare` exit 0, no fix needed. Axioms: `parentMix_entryWN`, `gate_cone_runGE`,
`parentMix_gate_cone_runK'`, `compare_contractW`, `fuel_contractWC` [propext, Classical.choice, Quot.sound].
* Cache entry existence: `EntryW` / `EntryWN`, `inst_entryW`, `binary_entryWN`; `gate_cone_runGE`
  (copy of `gate_cone_runG` with the entry conjunct). `parentMix_gate_cone_runK'` (premises unchanged:
  run, `GateDefines` NOT ALLOWED, `ChildBnd`, `EntryDefines childAdd`) concludes
  `∃ y, mF.get? ``childAdd = some y ∧ ParentMixObservesC (ownChild y) M` — no longer vacuous.
  `EntryWN` covers runs that skip the root cache lookup only (a cache hit skips the operands).
* `compare` at the world level: `compare_contractW`, fragment `cfragC` (= `cfrag` + compare),
  `fuel_contractWC`. The cone theorem is NOT yet restated over `cfragC`.
Remaining for gate-route parents: the other cone nodes (Bool ops, mux, setw, slices, concats), the cone
theorem over the larger fragment, `parentNested` (instance arguments), the other gate parents, the
design-level form (DesignSV / source), and the `GateDefines` ruling.

## Round 7 (par/n-7: c1e5a98d … 44f13cde) — BUILT with two integrator fixes
Run `n7` (`-j 1`). As written: `ShippingGateConeRunC` built; `ShippingGateConeBoolNot` failed (`decide` on
`0 < (Value.bool a).kind.width` — free variable; and `signalCompare_missW`'s implicit `va`/`vb`/`n` unified
wrongly, `vb := .bool a`), and everything after it downstream. Integrator fixes (no statement changed): pass
`(n := 1) (va := …) (vb := …)` and the two bit-vectors explicitly in BoolNot and BoolEq. Then all seven
targets exit 0: `…ConeRunC`, `…BoolNot`, `…BoolBin`, `…BoolEq`, `…Mux`, `…VecMux`, `…RunC6`.
Axioms: `gate_cone_runGC`, `gate_cone_runGC6`, `boolNot_contractW`, `boolBin_contractW`, `boolEq_contractW`,
`boolMux_contractW`, `vecMux_contractW`, `fuel_contractWC6` [propext, Classical.choice, Quot.sound].
World-level cone fragment now: leaves, literals, binary, compare, boolNot, boolBinary, boolEq, Bool mux,
bit-vector mux (`cfragC6`), with the cone theorem `gate_cone_runGC6` (premises run, `GateDefines` NOT
ALLOWED, `ChildBnd`). NOT in any fragment: setw, slices, concats, applicative forms, instance arguments.

Coverage of the eight simulated gate parents (worker N, BY READING; not a claim):
| parent | body | fragment | per-declaration theorem |
|---|---|---|---|
| parentUse | childAdd a b | cfrag | run shape only (parentUse_gate_parent_runG) |
| wrapAdd | childAdd a b at defaultDomain | cfrag | none |
| parentMix | childAdd a b + a | cfrag | parentMix_gate_cone_runK' |
| parentTwoCalls | childAdd a b + childAdd b a | cfrag | none |
| parentRepeat | childAdd a b + childAdd a b | cfrag | none |
| parentCmp | Signal.ult (childAdd a b) a | cfragC | none (entry existence for a compare root not written) |
| parentNested | childAdd (childAdd a b) b | NOT covered | none |
| wrapPick | pick sel x | NOT covered as stated (no domain binder: instEN reads sel as the domain) | none |

## Round 8 (par/n-8: 366938d2, 325922ca, 2938a0b6, a5435705, b2d9b6d2) — BUILT as written
Run `n8` (`-j 1`): `Tests.Compiler.GateConeTwoCallsTest`, `…RepeatTest`, `…WrapAddTest`,
`Tools.ShippingGateConeEntryC`, `Tests.Compiler.GateConeCmpTest`: all exit 0, no fix needed; no `sorryAx` in
any printed axiom list. `parentTwoCalls_gate_cone_runK'`, `parentRepeat_gate_cone_runK'`,
`wrapAdd_gate_cone_runK'`, `parentCmp_gate_cone_runK'`: [propext, Classical.choice, Quot.sound]
(`gateLeafSel_of2`: [propext, Quot.sound]). The peel sanity checks (`mixedGatePeel … = some … := rfl`)
build.
Each theorem: premises the run, `GateDefines` (NOT ALLOWED, ruling pending), `ChildBnd`,
`EntryDefines childAdd` (ALLOWED); conclusion post ∧ `CacheInv mF` ∧ tag at `envR` ∧
`∃ y, mF.get? ``childAdd = some y ∧ …ObservesC (ownChild y) M`.
New general pieces: `gateLeafSel_of2` (two leaves), `domCall` / `gateLeafSel_ofD` (constant domain),
`compare_entryWN`, `gate_cone_runGCE` (cone over `cfragC` with the entry conjunct).

Gate-route parents among the eight simulated: SIX now have a per-declaration cone theorem of this form
(parentMix, parentTwoCalls, parentRepeat, wrapAdd, parentCmp; parentUse has the run-shape form only and is
covered by the cone form via wrapAdd's pattern only by reading — not written). Not covered: parentNested
(instance arguments), wrapPick (no domain binder). All target-only, under the NOT ALLOWED `GateDefines`,
observation-level (`…ObservesC`), NOT the design-level DesignSV form; not counted in any tally.
