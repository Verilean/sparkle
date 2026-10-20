# B — gate-route declarations as ENTRIES at the design level (round par/b-35)

Branch `par/b-35` from `20ab638e`. Everything here is **WRITTEN, NOT BUILT**:
no `lean`, `lake` or `iverilog` was started. Nothing below is a claim that an
endpoint exists. Marks: [R] read in the tree at 20ab638e (file:line), [M]
measured by the integrator in an earlier round, [P] predicted.

## 0. Unit 1 (small)

* `Tests/Compiler/CombClosedSweepLinkedTest.lean` (target-only): `pickByteH`
  through `#comb_closed_sweep` (the sweep runs `#machine_comb_design0`'s
  generator `combDesign0`, then the audit and the gap tool) and
  `#comb_closed_sweep_expect … "GENERATED"` — the class is PREDICTED (the
  shape of `pickByte`, GENERATED [M, 7d8d56b1]); the integrator corrects the
  line from the measurement. It imports `ShippingCallsCloseTest`, where
  `pickByteH.machine_closes` already exists.
* `Tools/ShippingDesignCoverage.lean`: a row only for a name that is a
  CONSTANT of the environment; the others (prefixes of `machine_design_…`
  theorems in `Tools.*` namespaces — the 7 false rows [M]) are counted and
  listed in the SCAN line as "NOT constants … no row". A declaration with
  `f.gateValue` that the machine reader refuses is `OPEN gate-route` (was
  `OPEN reader`). `f.gate_design0` is recognised as a design-level constant
  (exact last component `gate_design0`; `_gap` companions are skipped as
  before).
  PREDICTED census after this round, in the AllTests environment: rows 129
  (136 − 7); COVERED 124 unchanged (the gate sweep and the `pickByteH` file
  are target-only); `OPEN gate-route` 3; `OPEN reader` 0; "not a
  declaration" 7.

## 1. What existed for a gate-route declaration

| piece | where [R] | what it says | about |
|---|---|---|---|
| `f.gate_child` (`#gate_child`) | `Tools/ShippingGateChildCommand.lean` 104–118; general `gate_child_full`, `Tools/ShippingGateChild.lean` 252 | `ChildFn b P F` for the module `b` of ANY run of the full entry: `b.outputs = [outP]`, and on every environment with `rst = 0` and argument values in `P`, `evalAssigns (declWidth b) mems b.body env` succeeds with `outP` = `F` of the argument values. `P` = `InRange` of the gate binders; `F` = `childValue f.machineSource f.gateBinders i0` | ONE evaluation of the entry's module `b` |
| `gate_child_forwardCheck` | `Tools/ShippingCombKidText.lean` 209 | `forwardCheck b = true` over every run | the text of `b` itself, not of `checkedOptimize b` |
| `checked_forwardCheck` | `Tools/ShippingMixedForwardSoundness.lean` 99 | `forwardCheck (checkedOptimize m') = true` from `PrintBaseAt`, `TypedPostReady`, `SimpleStmts` of the harness's module | the SHIPPED module; never instantiated at the full entry of a gate declaration |
| `forward_of_entry` / `ForwardValue` | same file | emitted AST of `checkedOptimize m'` evaluated ONCE gives the expected value | one evaluation (`evalAssignsSV`), no run |
| `GateRun`, `gate_linked`, `childFull_of_real`, `gate_real_kidK` | `Tools/ShippingGateChild.lean` 333; `ShippingCallsGate`; `ShippingCombKidText` | the child's module inside a parent's design | a CHILD at depth ≥ 1 |
| `runModule_assigns`, `seq_run_to_sv`, `designSV0_of_leaf`, `designSV0_leaf_unique` | `ShippingMachineShipsComb` 64; `ShippingSeqSVSoundness` 302; `ShippingLeafEntry` 400; `ShippingLeafDesign` 214 | run transfer between assignment bodies GIVEN a run; IR run → emitted text run; text run → `DesignSV` at depth 0; uniqueness | used by the machine route's comb leaves |

So every existing statement about a gate declaration is either one
evaluation, or about a child. **The missing pieces were exactly two:**

1. *A run from evaluations.* `runModule_assigns` needs a run of the first
   body as a hypothesis; the machine route gets it from `MachineTraceL`.
   The gate route has only "every evaluation succeeds".
2. *The shipped module's text at the full entry.* `gate_child_forwardCheck`
   stops at `b`.

Both are written (§2). No piece is left as an antecedent; there is no open
form.

## 2. Files and statements (WRITTEN, NOT BUILT)

### `Tools/ShippingGateDesign.lean`

* `runModule_assigns_total` (pure) — missing piece 1:

      (hall : body.all isAssign = true)
      (hstep : ∀ k st mems, k < N → ∃ e, evalAssigns we mems body (seed k st) = some e ∧ R k e) :
      ∀ T st mems, T ≤ N → ∃ envs, runModule we body seed T st mems = some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) t, t + j + 1 = T → R t envs[j]

  Induction on `T`; the step rewrites with `regNexts_assigns`,
  `memNexts_assigns`, `applyNexts_nil` exactly as the BUILT
  `runModule_assigns` does.
* `seedR_arg`, `seedR_rst`, `seedR_args` (pure): `seedR b ins k st` shows
  `ins k` on an argument port and `0` on `rst`.
* `gate_entry_text` (from the run) — missing piece 2. Premises: the run of
  `synthesizeCombinational f`, `EntryDefines`, and the gate's reading
  (`old`, `peel`, `he`, `hb`, `hv`: the binders of `gate_child_full`).
  Conclusion: `forwardCheck (checkedOptimize b) = true ∧ SimpleStmts b.body`.
  Proof: `synthesizeCombinational_checked`, `gate_core_facts`, the facts at
  the all-zero environment (as `gate_childFn` reads them),
  `mergeChecked_assign`, `checked_forwardCheck`, `mergeDuplicates_simple`.
* `gate_design_of_childFn` (pure): from `ChildFn b P F`, `forwardCheck
  (checkedOptimize b)` and `SimpleStmts b.body` —

      ∃ outP, b.outputs = [outP] ∧ ∀ T ins st0 mems,
        (∀ t < T, P ((argPorts b).map fun p => ins t p.name)) →
        (inputs < 2 ^ declWidth b) → (inputs < 2 ^ weS (checkedOptimize b)) →
        Bounded (weS (checkedOptimize b)) st0 →
        ∃ envsO, TextRun (checkedOptimize b) (seedR b ins) T st0 mems envsO ∧ envsO.length = T ∧
          ∀ j hj, envsO[j] outP.name = F ((argPorts b).map fun p => ins (T - 1 - j) p.name)

  Proof: the run of `b` by `runModule_assigns_total` from `ChildFn`; the
  optimizer by `runModule_assigns` + `checkedOptimize_sound` (the text of
  the BUILT `machine_ships_comb`); the emitted text by `forwardCheck_text` +
  `seq_run_to_sv`.
* `gate_entry_design0` (from the run): the endpoint form, `∃ raw, (b = dz raw
  ∨ b = mergeChecked (dz raw)) ∧ ∃ outP, b.outputs = [outP] ∧ ∀ T ins st0 mems
  kids, … → (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b)
  (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧ envsO.length = T ∧ …) ∧ ∀ envs',
  DesignSV … envs' → …` — `gate_child_full` + `gate_entry_text` +
  `gate_design_of_childFn` + `designSV0_of_leaf` / `designSV0_leaf_unique`.

### `Tools/ShippingGateDesignCommand.lean`

`#gate_design0 f` adds `f.gate_design0` with binders the run and `EntryDefines
… f f.gateValue`, proof term

    Tools.ShippingGateDesign.gate_entry_design0 (F := childValue f.machineSource f.gateBinders i0)
      hr entry f.gate_old f.gate_peel f.gate_wf
      (bool_positions (by decide)) (bits_positions (by decide)) (fun _ _ => rfl)

— the proof term of the BUILT `f.gate_child` with the design-level theorem in
the place of `gate_child_full`. Per declaration the kernel does what it does
for `f.gate_child`: two `decide` on binder positions, one `rfl` (the source
function at constant inputs is the term's value). Nothing about the run's
module is decided; no `native_decide`.

`checkStatement`: exactly two proposition binders (`RunsTo`, `EntryDefines` at
`f` and `f.gateValue`); one existential; every antecedent under it ALLOWED
(there are none); `DesignSV` and `childMap` under it; none of
`forbiddenAll` nor `forwardCheck` in the statement.

`#gate_design_sweep f` (START line on stderr and in the log; generator; audit
on the stored statement with `collectAxioms` of the endpoint, the gate data
theorems and six general theorems; gap tool `gapOf`; a RESULT line with the
scope; never an error), `#gate_design_sweep_summary` (error only on an
inconsistency of what was measured), `#gate_design_sweep_expect f "CLASS"`.

### `Tests/Compiler/GateDesignSweepTest.lean` (target-only)

`#gate_design_sweep` on `ShippingMachineInstTest.pick`, `.pickD`,
`ShippingMachineDepthHTest.rcH`, then the summary. No class is asserted.

## 3. The statement against `f.machine_design_comb0` — differences

Same: the run of `synthesizeCombinational f` and a reflection as the only
proposition binders; `∃ raw` with the cleaned-or-merged disjunction;
`DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) T
⟨st0, mems, kids⟩`; existence AND "every closed run shows it"; the two
input-width antecedents and the state bound under the `∀`; no check
constant.

Different — each is a property of the statement, to be carried into any
report:

1. **Reflection**: `EntryDefines f f.gateValue`, not `MachineDefines`.
   (`allowed` accepts both.)
2. **No `ChildBnd`.** Not needed: the gate's text facts come from
   `PrintBaseAt` / `TypedPostReady`. The endpoint is stronger than the form
   asked for by one antecedent. If the uniform shape "exactly one antecedent
   `ChildBnd`" is wanted for a consumer, a weakening lemma is one line; I did
   not add an unused premise.
3. **The source is per cycle on values.** `envs[j] outP.name = childValue
   f.machineSource f.gateBinders i0 (argument values of cycle T−1−j)`, under
   `InRange` of each cycle's argument values. It is NOT `src i bools bits`
   on Signals with `SourceInputs`. What is missing for the Signal form: a
   theorem "for a combinational `f`, `(f.machineSource i bools bits)[0] t =
   childValue … (values of bools / bits at t)`". True by inspection, proved
   nowhere [R: `childValue` is used only at constant inputs,
   `Tools/ShippingMachineChild.lean` 155]. This is the one honest gap
   between this endpoint and the machine leaves' form; it is a gap in the
   SOURCE side (about `f.machineSource`), not a premise of the endpoint.
4. **The output port** is `∃ outP, b.outputs = [outP]`; its name is not
   stated (`ChildFn` hides it; `PrintBaseAt.output` knows it is `out`).
5. `InRange` and the two width bounds overlap (an in-range value fits the
   port); no lemma here derives one from the other.

## 4. PREDICTED outcomes

| item | PREDICTED | if not |
|---|---|---|
| `Tools/ShippingGateDesign.lean` builds | most likely places to fail, in order: (a) the three `simp` lines of the step of `runModule_assigns_total` (copied from a proof whose goal had an extra existential); (b) `seedR_arg`'s `contains` step (three alternatives under `first`); (c) `hwag'`'s `simpa` (`weS` against `weOf (wofOf …)`); (d) the 9-component pattern on `vals … (admissible_zero _ _)` in `gate_entry_text` (copied from `gate_childFn`) | all four are local; the statements do not depend on them |
| `pick`, `pickD`, `rcH` | GENERATED, premise lines 2 (both ALLOWED), 0 antecedents, audit OK, gap hypotheses `[]` | a FAILED row with the elaboration error: the statement in the command's quotation and `gate_entry_design0`'s conclusion were written twice by hand and must agree up to α/β — the first suspect |
| cost per declaration | of the order of `#gate_child` (a second or less each [P]; `f.gate_child` for these is in AllTests) | — |
| `rcH` vs `pick` | no difference expected: `rcH`/`pickD` are domain-polymorphic (`i0 = defaultDomain`), `pick` is at `defaultDomain` (`i0 = Unit.unit`); the command picks `i0` as `#gate_child` does | — |

After the measurement the census (if the sweep file is imported) should show
the three as COVERED by `gate_design0` and `OPEN gate-route` 0.

## 5. Could not be determined by reading

* Whether `simp only [runModule, stepModule]` leaves the goal of
  `runModule_assigns_total` in the shape the second `simp only` expects (I
  cannot see `stepModule`'s unfolded form without running Lean).
* Whether `gapOf` accepts a body `∃ raw, P ∧ ∃ outP, …` with NO antecedent
  (its two passes loop over arrows; zero iterations look fine [R:
  `Tools/ShippingFinalGoalCommand.lean` 82–146]); a failure is caught and
  reported in the row as `gap tool FAILED`, it does not fail the sweep, but
  it does not fail the summary either.
* Whether the census's reader really refuses the three (`OPEN reader` was
  measured, so `readMachine` throws on them although `f.machineData` exists
  — `gate_binders` [R: `ShippingGateChildCommand.lean` 99] uses it). The new
  class name depends only on `f.gateValue` being present.
* `keccakRcHW` (the fourth gate child, `Tests/Compiler/OneOutWKeccakFTest.lean`
  156, target-only) is not in the sweep file; by shape it is in scope [P].

## 6. Integrator

`lakefile.lean`:

    lean_lib «Tools.ShippingGateDesign» where
      roots := #[`Tools.ShippingGateDesign]

    lean_lib «Tools.ShippingGateDesignCommand» where
      roots := #[`Tools.ShippingGateDesignCommand]

and targets for `Tests.Compiler.GateDesignSweepTest`,
`Tests.Compiler.CombClosedSweepLinkedTest` (as the other sweep tests).

Build order: `Tools.ShippingGateDesign` → `Tools.ShippingGateDesignCommand` →
`Tests.Compiler.GateDesignSweepTest`; independently
`Tools.ShippingDesignCoverage` → `Tests.Compiler.DesignCoverageTest`, and
`Tests.Compiler.CombClosedSweepLinkedTest`.

`Tests/AllTests.lean`: nothing required. Could be added after the
measurement: `import Tests.Compiler.GateDesignSweepTest` (after
`ShippingMachineDepthHTest`; adds `pick/pickD/rcH.gate_design0` and `_gap`)
and `import Tests.Compiler.CombClosedSweepLinkedTest` (after
`ShippingCallsCloseTest`), each with its expect lines.

SCOPE of a GENERATED `f.gate_design0`, binding for any report: ONE gate-route
declaration as an entry, depth 0, no call, no register, one output; the run
and `EntryDefines f f.gateValue` are premises; the source is per cycle on
values (§3.3); `DesignSV` of the module list over the returned design's
child map — not the SV string, not `#sim`; seeding `seedR` (`rst` low).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `b7972454d116570c42794545f664b88a3ba32a8e` (poc e6f68394 + these files), cgrun 3 GiB swap 0, worker's files unchanged, FIRST
ATTEMPT. `b35` (exit 0, peak 0.80 GB): `CombClosedSweepLinkedTest`, `Tools.ShippingGateDesign`,
`Tools.ShippingGateDesignCommand`, `GateDesignSweepTest`. `b35-all` (exit 0, peak 0.44 GB):
`Tests.AllTests` with the two sweep tests imported, 1323 jobs; `DesignCoverageTest`; and, printed by the
integrator independently of the generator's audit: `rcH.gate_design0`, `pick.gate_design0` on
`[propext, Classical.choice, Quot.sound]`, and the full statement of `rcH.gate_design0`.

* `pickByteH.machine_design_comb0`: GENERATED (3 premise lines, 0 NOT ALLOWED), expect line "as measured".
* `f.gate_design0` GENERATED for `pick`, `pickD`, `rcH`: 2 premise lines (the run of
  `synthesizeCombinational f`, `EntryDefines f f.gateValue`), 0 antecedents, 0 NOT ALLOWED, audit OK,
  gap hypotheses `[]`, 126–271 ms.
* Census of the AllTests environment after this: 129 declarations, COVERED 128, OPEN 1 (`mixDeep`, calls);
  forms: leaf0 55, comb0 33, noPortsNR_closed 9 (+6 B), noPortsR0_closed 9 (+1 N), svH_full_closed 14,
  gate_design0 3. Log: `~/sparkle-work/coverage-census-2.log`.

The gate form is a DIFFERENT form from the machine-route ones and is reported separately: reflection
`EntryDefines` (not `MachineDefines`); no `ChildBnd` antecedent; the source side is the declaration's
value function `childValue f.machineSource f.gateBinders` applied to each cycle's argument values under
`InRange` — NOT the Signal-level source with `SourceInputs` (no theorem connects the two for arbitrary
Signals); the one output port is `∃ outP, b.outputs = [outP]`, its name not stated.
SCOPE of each: one declaration as an entry, depth 0, combinational, one output; runtime boundary;
`DesignSV` of the module list — not the SV string, not `#sim`.
