# Worker W, round 2 (par/w-2) — WRITTEN, NOT BUILT

Base: poc `ab3d3d5a`. No compiler file changed, no ALLOWED list change, no `sorry`, no new axiom,
no `native_decide`.

Ruling applied (reviewer, 2026-10-15): the meaning is extended to calls without a domain
argument IN PLACE (option (i)); the old domain-carrying definition is kept as a compatibility
layer with the agreement proved; the seven gate parents are regressed; the new `wrapPick`
real-compiler/source correspondence is added.

## Design choice (deviation from the integrator's sketch, flagged)

The port count is a FIELD of `ChildSem` (`ports : Name → Nat`), not a separate class
`[ChildPorts]` beside `[ChildSem]`. Reason: a separate class would have to be added to every
`variable [ChildSem]` section and every `(C : ChildSem)` / `LeafMeaning C …` statement (≈ 40
files, all `LeafMeaning C` / `HierConePreservesK` / `KidFacts` statements and every test that
passes `addSem` explicitly). As a field, every statement over `ChildSem` / `LeafMeaning C` is
unchanged; the child semantics and its arity are one consumer choice. The round-1 `ChildPorts`
class and `MeaningP` are REMOVED (subsumed; see below). The meaning is NOT weakened: the new
`Meaning.inst` reads exactly the compiler's arguments (`inst_args_eq`); `ArityOK` is a property
of a `ChildSem`, discharged by evaluation (`addSem_arityOK`, `pickSem_arityOK`), never assumed.

## Changed EXISTING statements / definitions (exact)

1. `Tools.ShippingUnifiedMeaning.ChildSem` — new field `ports : Name → Nat`.
2. `Tools.ShippingUnifiedMeaning.noChildSem` — `⟨fun _ _ => none, fun _ => 0⟩`.
3. `Tools.ShippingUnifiedMeaning.Meaning.inst` — was
   `instSpineArgs e = dom :: args → vs.length = args.length → …`; now
   `{e mn lvls pre args vs v} : view e = none → e.getAppFn = .const mn lvls →
   instSpineArgs e = pre ++ args → args.length = ChildSem.ports mn → vs.length = args.length →
   (∀ i …, Meaning inputs args[i] vs[i]) → ChildSem.childSem mn vs = some v → Meaning inputs e v`.
4. `Tools.ShippingUnifiedMeaning.Meaning.deterministic` — statement unchanged; proof now splits
   the spine by `List.append_inj'` at the port count (the round-1 `MeaningP.deterministic` text).
5. `Tools.ShippingInstanceLeaf.meaning_inst` — NEW premise `(hports : argsE.length = ChildSem.ports mn)`
   (third explicit argument, after `hlen`).
6. `Tools.ShippingInstanceLeaf.inst_leaf_fuel` — NEW premise `(hports : argsE.length = ChildSem.ports mn)`
   after `hlenV`.
7. `Tools.ShippingGateParentRun.InstLeafK` (def) — was
   `∃ mn lvls dom argsE vs, e = instEN mn lvls dom argsE ∧ pure ∧ bin ∧ fallbackKind (instEN …) = .other ∧ …`;
   now `∃ mn lvls (pre argsE : List Expr) vs, e = instEP mn lvls pre argsE ∧ pre ++ argsE ≠ [] ∧
   pure ∧ bin ∧ fallbackKind (instEP mn lvls pre argsE) = .other ∧ …` (the rest verbatim; `argsE`
   are the PORT arguments; `KidFacts … argsE.length` unchanged). `instEN … dom argsE` is
   `pre = [dom]` by `rfl`.
8. `Tools.ShippingGateParentRun.leafK_contractW` — statement unchanged; proof via the new
   `inst_leaf_contractWE`.
9. `Tools.ShippingGateParentRun.LeafKR` — NEW constructor
   `instK : InstLeafK tenv children C mF ctx inputs mems initial e v → LeafKR … e v`.
10. `Tools.ShippingGateParentRun.leafKR_of_leafK` — statement unchanged; an instance leaf now
    maps to `instK` (its premise `hm` is no longer read).
11. `Tools.ShippingGateParentRun.leafKR_contractW` — statement unchanged; new `instK` case.
12. `Tools.ShippingInstanceMeaningP` (round-1 file): REMOVED `ChildPorts`, `MeaningP`,
    `MeaningP.inst_args`, `MeaningP.deterministic`, `MeaningP.inst_cons`, `meaningP_of_meaning`,
    `meaningP_agree`, `no_meaning_of_portsSpine`, `LeafMeaningP`. CHANGED `ArityOK` (now
    `[ChildSem]` only: `childSem mn vs = some v → vs.length = ChildSem.ports mn`). Kept unchanged:
    `instEP`, `instEP_spineArgs`, `instEP_getAppFn`, `instEN_eq_instEP`, `portArgs_eq`,
    `filter_noclkP`, `instUncached_shapeE`, `instUncached_shape_of_E`, `instUncached_linkedE`.
13. Tests (definitions): `ShippingHierarchySoundnessTest.addSem` gains `ports _ := 2`;
    `WrapPickMeaningTest.pickSem` gains `ports _ := 2`; `WrapPickMeaningTest.ports2` REMOVED.
14. Tests (statements, target-only `WrapPickMeaningTest`): `addSem_arityOK : @ArityOK addSem`,
    `pickSem_arityOK : @ArityOK pickSem` (no `ports2`); `wrapAdd_leaf_agree` now
    `@MeaningD addSem … v → (@Meaning addSem … v' ↔ v' = v)`; `wrapPick_meaningP` RENAMED
    `wrapPick_meaning : @Meaning pickSem …`; `wrapPick_no_old_meaning : ¬ @MeaningD pickSem …`.

Proof-only edits (statements unchanged) in the seven parents' tests: every
`meaning_inst rfl rfl X Y` → `meaning_inst rfl rfl rfl X Y` (14 sites: GateConeUse, Repeat,
Nested ×2, TwoCalls ×2, WrapAdd, Kid, Run, Cmp, ShippingHierarchySoundnessTest ×4); the four
`inst_leaf_fuel` calls in ShippingHierarchySoundnessTest get one more `rfl`; the 7 `InstLeafK`
witnesses `⟨``childAdd, [], D, args, vs, rfl, rfl, rfl, rfl, tagR, rfl, …⟩` →
`⟨``childAdd, [], [D], args, vs, rfl, (by simp), rfl, rfl, rfl, tagR, rfl, …⟩`
(GateConeUse, Repeat, TwoCalls ×2, WrapAdd, Kid, Run, Cmp).

## New (compatibility layer + units)

`Tools/ShippingInstanceMeaningP.lean`:
* `MeaningD` — the OLD meaning verbatim; `MeaningD.deterministic` (old proof verbatim).
* `meaning_of_meaningD (hA : ArityOK) : MeaningD e v → Meaning e v`;
  `meaningD_agree (hA) (h : MeaningD e v) v' : Meaning e v' ↔ v' = v` — THE MEANING IS UNCHANGED
  WHERE THE OLD ONE IS DEFINED; `no_meaningD_of_portsSpine` (the round-1 finding).
* `inst_args_eq` (the arguments read are the compiler's `drop (length - #ports)`),
  `meaning_inst_cons`, `meaning_instP`, `instEP_eq_instEN` (a non-empty spine `d :: rest` split
  any way is `instEN … d rest`).

`Tools/ShippingGateConeLeafContractE.lean` (new lean_lib): `armCont_leaf_contractE` — the text of
`armCont_leaf_contract` for any `e` with `instSpineArgs e = pre ++ argsE` (`instUncached_shapeE`).

`Tools/ShippingGateConeW.lean`: `inst_leaf_contractWE` — `inst_leaf_contractW` for
`instEN mn lvls dom rest` whose spine `dom :: rest = pre ++ argsE` (ports `argsE`).

`Tools/ShippingGateKid.lean` (new lean_lib): `gate_child_fnR` (reset-free `ChildFnR` of a
MIXED-gate child at the full entry), `gate_full_outputs` (its one output is
`out : bitVector srt.width` when `srt.width ≠ 1`, from `PrintBaseAt`), **`kidFacts_of_gate`** /
`kidFacts_of_gate'` (`KidFacts (ownChild y) C c n v y` from `RealChild`, `EntryDefines`
(ALLOWED), the gate reading `#gate_child c` generates, and `hC` about `C`).

`Tests/Compiler/GateConeWrapPickTest.lean` (target-only): `wrapPickBinders`, `wrapPickBody`
(peel checked by `run_cmd`), `wrapPick_sel`, `wrapPick_tag`, `wrapPick_entryWN`, `pickTermSem`
(`pick`'s gate term on the two ports, `ports _ := 2`), `pickTermSem_hC`, `wrapPick_coneKT`
(the generalized `InstLeafK` with `pre = []`), **`wrapPick_gate_cone_runKT`** (`out` = `pick`'s
gate term on the inputs).

`Tests/Compiler/GateConeWrapPickSourceTest.lean` (target-only): `pickF_source` (the gate term
of `pick` IS `pick` on constant signals, by `rfl` + `ofNat_toNat`), `WrapPickObservesC`,
**`wrapPick_gate_cone_runK'`** — the shape of `wrapAdd_gate_cone_runK'`: `out =
((wrapPick sS xS).val t).toNat`. Premises: the run, `GateDefines` (NOT ALLOWED, unchanged
class), `ChildBnd` (ALLOWED), `EntryDefines … ``pick pick.gateValue` (ALLOWED).

## Build order (all under cgrun, `-j 1`)

1. `Tools.ShippingUnifiedMeaning` (everything downstream rebuilds), `Tools.ShippingInstanceLeaf`,
   `Tools.ShippingInstanceMeaningP`, `Tools.ShippingGateConeLeafContractE`,
   `Tools.ShippingGateConeW`, `Tools.ShippingGateConeNested`, `Tools.ShippingGateKid`.
2. `Tests.Compiler.ShippingHierarchySoundnessTest`, then the parents: `GateConeRunTest`,
   `GateConeKidTest`, `GateConeEntryTest`, `GateConeUseTest`, `GateConeWrapAddTest`,
   `GateConeTwoCallsTest`, `GateConeRepeatTest`, `GateConeCmpTest`, `GateConeNestedTest`, and the
   GateConeDesign*/GateParentRun* tests built on them.
3. `Tests.Compiler.WrapPickMeaningTest`, `Tests.Compiler.GateConeWrapPickTest`,
   `Tests.Compiler.GateConeWrapPickSourceTest`.
4. `Tests.AllTests` (full suite).

Predicted axioms: every printed theorem [propext, Classical.choice, Quot.sound] or a subset.

## Risks (not built)

* `pickF_source` closes by `rfl` between `pick`'s gate term evaluation and `pick`'s Signal code
  (the same unfolding the generated `pick.gate_child` closes with `fun _ _ => rfl` through
  `childValue pick.machineSource`); isolated in its own file so `GateConeWrapPickTest` does not
  depend on it.
* `pickTermSem_hC`: `InRange` by `Zip₂.cons` needs the elaborator to unfold
  `pick.gateBinders.filter …` to two cons cells; `wrapPick_sel` is the text of the built
  `parentUse_sel` (`unfold mixedGateCond unifiedInstanceRoot hierInstRoot; rw [hI]; rfl`).
* `gate_full_outputs`: `cases` on `PrintableType ty`; `dropZeroWidth_typed` 4th component is the
  outputs equation (as used by `childFn_dropZW`).
* `instEP_eq_instEN`: `rw [← List.foldl_append, h]` then `try rfl`.
* `(by simp)` for `[d] ++ args ≠ []` in the seven `InstLeafK` witnesses.
* `meaning_inst … rfl …` for `hports` needs `ChildSem.ports` of the `letI` instance to reduce
  to `2` (`addSem.ports _ := 2`).

## Integration (integrator, 2026-10-15) — `Meaning` extended IN PLACE; BUILT with one fix
Applied on poc fad8cf9a (lakefile conflict on appended lean_libs: kept both). Run `w2` (cgrun, 3 GiB, swap 0,
`-j 1`): every changed Tools file, `ShippingHierarchySoundnessTest`, ALL existing gate-parent tests
(GateCone*Test incl. the Design* / Walk / Names / Typed / All chains, GateParentRun*Test), `WrapPickMeaningTest`,
`GateDefinesProbe`: exit 0; `Tests.AllTests` + `DesignCoverageTest`: exit 0, census 134 / 133 (unchanged,
suite population only). As written, `GateConeWrapPickTest` failed code generation of `pickTermV` (a definition
used only in proofs); integrator fix: `noncomputable` on `pickTermV`, `pickF`, `pickTermSem` (no statement
changed). Run `w2b`: `GateConeWrapPickTest`, `GateConeWrapPickSourceTest` exit 0; no `sorryAx`.
Axioms: `kidFacts_of_gate`, `wrapPick_tag`, `wrapPick_coneKT`, `wrapPick_gate_cone_runKT`,
`wrapPick_gate_cone_runK'` [propext, Classical.choice, Quot.sound]; `wrapPick_sel` [propext];
`pickF_source` [propext, Quot.sound]. Measured: `WRAPPICK peel = (wrapPickBinders, wrapPickBody)`.
CHANGED EXISTING STATEMENTS (exact list in the worker section above): `ChildSem` gains the field `ports`;
`Meaning.inst` reads `instSpineArgs e = pre ++ args`, `args.length = ChildSem.ports mn` (was `dom :: args`);
`meaning_inst` and `inst_leaf_fuel` gain the premise `argsE.length = ChildSem.ports mn`; `InstLeafK` over any
prefix (`instEP`); `LeafKR` gains `instK`. Compatibility: `MeaningD` = the old definition verbatim,
`meaningD_agree` / `meaning_of_meaningD` (meaning unchanged where the old one is defined). The seven existing
gate parents: statements unchanged, proofs adapted, all rebuilt green. The round-1 `MeaningP` layer removed
(superseded). Deviation from the plan: the port count is a field of `ChildSem`, not a separate class
(~40 files otherwise).
`wrapPick_gate_cone_runK'` (target-only): premises run, `GateDefines` (separate gate-only class), `ChildBnd`,
`EntryDefines … pick pick.gateValue`; observation level (like the round-6 forms), not yet the design /
all-run level.
