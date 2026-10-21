# From the child/cache work to the main endpoint (unit F, cluster round 2, base 0054b6b2)

Status words: **PROVED** (kernel-checked, name given), **PREMISE** (a hypothesis of a stated
theorem), **OPEN** (no proof, no hypothesis form carried through). Nothing here is CI; nothing is
pushed. "Built" means a local `./.cluster/qbuild.sh build …` exit 0 (run names in REPORT-F.md).

## 1. The two endpoints and what lies between them

**Child/cache side (NEW boundary).** One witness `O : RefLawsAOps MkRefd mref cref`, admissible
contexts `hA : AdmCtx O.quiet mctx cctx`, the invariants `JQ O.quiet D` (quiet, synthesis ref =
`synthesizeChild`, depth `D`) and `JQC O D = JQ ∧ CacheInvA O (cv w)`.
BUILT: `core_tripleA` (VertA), `core_tripleA_of_bodies` (DepthA, from `BodyStepA O`),
`core_tripleAC` / `full_tripleAC` / `hentry_of_body` / `closeInstsM_realA'` (CoreC, from `hbodyC`),
`synthesizeChild_realA` (CacheA), `translate_keepsA` (FallbackA), `fromConst_frontends_keepsA`
(FrontA, ALL-context `htr`).

**Main endpoint (OLD boundary).** `<p>_sat/_satC/_satC2`, and for a leaf
`f.machine_design_closed` (`#machine_leaf_design_closed`, ShippingLeafDesignClosedCommand.lean:
instance of `leaf_sat_design_closed5`, ShippingLeafInputWidths.lean:~300–360). Its antecedents:
the run `hr : RunsTo (synthesizeCombinational f) … (b, design) w'`, `MachineDefines`, and
**`hbnd : ChildBnd mref cref w`** with `ChildBnd w := ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w`
(ShippingChildInv.lean:674). The leaf sources inside are `machine_run_of_core` /
`machine_children_realA` (ShippingChildRun.lean:472–560), which unpack the run with
`core_reads_inv L` (ShippingChildRun.lean:134) and consume the **old** `RealChild`
(ShippingChildInv.lean:453: its `quiet` field is `∃ L : RefLaws mref cref, L.quiet w`, `synth` is
`SynthAt`, `cache` is read through `sparkleChildCache.get`) and the old `ChildrenReal`.

**Consequence (the gap).** No lemma exists from the new boundary to
`ChildBnd`, and none can be built from `RefLawsAOps`: `ChildBnd` asks for a 26-field *old*
`RefLaws` witness, whose every-context frame is false of the real runtime (probe
`Tests/Compiler/CanUnfoldProbe.lean`, run cu2/cu3 — counterexample stands against the old laws).
So `machine_design_closed` and the `_sat` family cannot be fed by `core_tripleAC` as they stand.
What must be written is a **port of the consumers** (§2, L5–L7), not a bridge lemma.

## 2. The chain, lemma by lemma

| # | link | statement (informal) | status | owner |
|---|---|---|---|---|
| L1 | handlers at a stable `I` | `LegacyImplA` (B), `LegacyCachedA` (A), `CanonKeyA` (A), `ProjFieldNameA` (C, needs `RefLawsATele`) | A/B/C exports pending; composed in `handlers_of_exports` (PROVED relative to them, MainA) | A, B, C |
| L2 | `BodyStepA O` | all depths ≥ 1: `ChildKeepsA D → body keeps JQ D` | D `bodyStepA_of_handlers` (par/u-d 5434407f, pending integration); composed `bodyStepA_of_exports` (PROVED relative to exports) | D |
| L3 | core entry, `OutQ → OutQ` | `core_tripleA_of_bodies` | BUILT (DepthA); composed `core_tripleA_of_exports` (PROVED relative to L2) | — |
| L4 | cache half | `hbodyC` at `JQC (D+1)`; `core_tripleAC`, `full_tripleAC`, `closeInstsM_realA'` | CoreC BUILT from `hbodyC`; `hbodyC` derived in `hbodyC_of_exports` (PROVED relative to A,B,C, D-generic, E child entry, legacy tail at `JQC`) | E (`BodyStepC`), D (generic) |
| L5 | run unpacking under the NEW boundary | the analogue of `core_reads_inv` / `machine_run_of_core`: a successful run of the core from a `JQ`/`JQC` world contains a run of `synthesizeMachineCertified` (or the leaf equivalent) starting in a `JQC` world at depth ≥ 1 | **OPEN, no owner** | propose **new unit G** |
| L6 | `machine_children_realA` on `RealChildA` | children of `closeInsts` are `RealChildA` (CoreC's `closeInstsM_realA'` already gives this for the monadic closing; what is missing is its use through L5's decomposition) | **OPEN** (needs L5) | unit G |
| L7 | consumers of `RealChild` | `childLink_real`, `entryStrict_real`, `realChild_of_childrenReal`, `callWidthsStrict…`, 92 files mention `RealChild mref cref` (grep count; not all use the quiet field); the leaf chain uses the *run* `hr` of the callee + `core_reads_inv L`. Port to `RealChildA O` (which carries the same `hr` plus `AdmCtx`, `sv`, quiet) | **OPEN** (list: `grep -l "RealChild mref cref" Tools/`) | unit G (mechanical but large) |
| L8 | leaf/parent heads | `leaf_names`, `leaf_input_widths`, `leaf_sat_design_closed5`, `<p>_sat*` take `ChildBnd`; replace by `JQC`-start premise (`OutQ` + `cv w = {}` ⇒ `JQC O 0`, PROVED `jqc_zero_of_empty`) | **OPEN** (statement change of the endpoint's premise — to be agreed, REPORT) | unit G |
| L9 | endpoint premise: the entry's start world | `OutQ O.quiet w` (quiet + `sv w = some synthesizeChild` + depth 0) and `cv w = {}` | PREMISE (run hypothesis; command→entry link not formalised, R13/R14 in open-items §1) | integrator / OPEN |

Why `MainA` stops at L4: the units' exports end there. The composed theorems that ARE proved:

* `bodyStepA_of_exports` (A+B+C+D → `BodyStepA O`),
* `core_tripleA_of_exports` (…→ core entry keeps `OutQ`, every outcome),
* `hbodyC_of_exports` (A+B+C at `I := JQC (D+1)` + D generic + E child entry → CoreC `hbodyC`),
* `entry_children_of_exports` (`hbodyC` → full entry keeps `JQC D`; children of the closing are `RealChildA`),
* `fullEntry_jqc_of_exports` (`OutQ` + empty cache + a run of the full entry → `JQC O 0` at the end),
* `jqc_zero_of_empty`, `handlers_of_exports`.

All in Tools/ShippingChildMainA.lean (build names/exits in REPORT-F.md; header says UNBUILT/BUILT).

## 3. Audit table: every remaining premise of the composed theorems

Kinds: **LAW-OPS** = field of `RefLawsAOps`; **LAW-TELE** = `RefLawsATele` (separate, WIDER
assumption family: recorded here as the widening of the boundary by `ProjFieldNameA`);
**HANDLER** = one named handler premise; **TAIL** = legacy tail; **RUN** = run/start hypothesis;
**MODEL↔ST** = fit of the Lean model to the real `ST`/`IO` runtime.
"Sat." = satisfiable by construction (a witness exists in a model we built). Rules applied: joint
satisfiability of the laws is NOT PROVEN (logical inconsistency NOT PROVEN, no proof either way);
`MkRefd` is a history, not freshness; `RealChildA` is a history of past synthesis results, not
semantic correctness in the current environment; opaque/extern/implemented_by counts are
STRUCTURAL dependency counts, not a runtime-fit proof.

| premise (MainA name) | kind | owner | sat. by construction? | runtime fit |
|---|---|---|---|---|
| `O.diag`, `O.frameT`, `O.excOk`, `O.frameQ`, `O.cacheSetQ`, `O.depthSetQ`, `O.frame`, `O.cacheSet`, `O.depthSet` (the 9 fields of `RefLawsAOps`, `O.quiet`) | LAW-OPS | boundary (InvA) | NO proof. The pure `HeapLaws` model (`heapLaws_sat`) restates only the ref-only fragment over a *different* type; `RefLawsAOps` itself: not satisfied by any model we built | OPEN (extern opaque `ST.Prim.Ref.*`, `Void IO.RealWorld`, Meta primitives, `diag` printers/handles, `excOk` on Lean's exceptions: unmodelled) |
| joint satisfiability of `RefLawsAOps` with `AdmCtx` | LAW-OPS | boundary | logical inconsistency NOT PROVEN | OPEN |
| `AdmCtx O.quiet mctx cctx` (`hA`, no `canUnfold?` or `InertUnfold`) | RUN | boundary | n/a | the entry's start context admissible: Sparkle never sets `canUnfold?`, command→entry link NOT formalised |
| `T : RefLawsATele O.quiet mref cref` | LAW-TELE | C (uses), boundary | NOT PROVEN; not implied by the old laws | OPEN (library telescopes keep `canUnfold?` is a reading of the library) |
| `H` with `hH` (B's `H₁A … HₖA O I` at every `JQ D`, resp. `JQC D`) | HANDLER ×k | B (one named premise per unproved legacy handler; list in docs/parallel/legacy-impl-inventory.md) | each premise is a `RecA` statement of Lean code; not discharged | OPEN |
| `hA_cached : LegacyCachedA` from `LegacyImplA` | HANDLER (proved from `LegacyImplA` by A, pending) | A | PROVED-pending | — |
| `hA_canon : CanonKeyA` | HANDLER (A, pending) | A | PROVED-pending | — |
| `hC_pf : ProjFieldNameA` | HANDLER via LAW-TELE | C | PROVED-pending relative to `T` | OPEN with `T` |
| `Lg` / `hLg` (D's `LegacyTailA O D`, all D) | TAIL (asked only of constants on which BOTH gates miss) | D | not discharged | OPEN |
| `hleg` (the same tail at `JQC O D`) | TAIL | D/E (not yet exported: D states `LegacyTailA` at `JQ` only) | not discharged | OPEN |
| `hBS : BS` (E's `BodyStepC O`) with `hE_child`, `hE_synth` | HANDLER-like (depth induction) | E (from `hD_gen`) | PROVED-pending relative to D-generic + the handlers | — |
| `hD_gen` (D's generic `fromConst_frontends_keepsCP`) | built-pending | D | — | — |
| the start: `OutQ O.quiet w` and `cv w = {}` | RUN | integrator | n/a | first-entry refs' contents (R13/R14), commands between two entries: OPEN |
| `hr` (the compiler's run succeeded) | RUN | — | no theorem claims a successful run exists | — |
| `MachineDefines`, `EntryDefines`, the generators' `rfl` checks | reflection | existing | checked per declaration | OPEN for all declarations |
| model→real ST correspondence (the `Triple`/`Keeps` model of `MetaM`/`ST` vs Lean's compiled code) | MODEL↔ST | nobody | n/a | **OPEN** |

**Facts that must stay in force (checked by tests, not by this file):**
* `Tests/Compiler/HeapProvenanceRegressTest.lean` (a `MkRefd` history that aliases a ref valid in
  the use world) must remain: `MkRefd` is NOT freshness, and nothing in MainA uses it as such.
* `Tests/Compiler/CanUnfoldProbe.lean` (cu2/cu3): the old every-context laws are false of the
  runtime; the audit (ChildVertAuditTest) forbids `RefLaws`/`RefLawsCore`/`toAOps`/`toA` in the closure.
* The audit's opaque / extern / implemented_by counts are STRUCTURAL (kernel-term dependencies),
  not a proof that extern code satisfies the laws.

### Statement-level honesty about what `JQC`/`RealChildA` give

`RealChildA O c r` records: SOME admissible-context run of `synthesizeCombinational c`, from a world
quiet for the fixed `O` with `sv = some synthesizeChild` and a `RealChildA`-only cache, returned `r`.
It is a history. It does not say `r` is correct in the *current* environment (the environment may
have changed between the past run and the cache hit; the old `RealChild` has the same weakness, and
`childLink_real`-style consumers re-read the environment, so the port L7 must not assume more).

## 4. Proposed additions to Tests/Compiler/ChildVertAuditTest.lean's list (integrator applies)

```
``Tools.ShippingChildMainA.handlers_of_exports,
``Tools.ShippingChildMainA.bodyStepA_of_exports,
``Tools.ShippingChildMainA.core_tripleA_of_exports,
``Tools.ShippingChildMainA.hbodyC_of_exports,
``Tools.ShippingChildMainA.entry_children_of_exports,
``Tools.ShippingChildMainA.jqc_zero_of_empty,
``Tools.ShippingChildMainA.fullEntry_jqc_of_exports
```
plus `import Tools.ShippingChildMainA` in that test. The hypotheses are all `Prop`/function
parameters, so `#print axioms` stays standard and the closures contain no old boundary.

## 5. Missing with no owner (proposals)

1. **Unit G — port the endpoint to the new boundary** (L5–L8): run unpacking under `JQ`/`JQC`
   (new `core_reads_inv`), `RealChild → RealChildA` in the consumer chain, `ChildBnd` replaced at the
   heads by `OutQ ∧ cv = {}`. Large, mechanical; the old chain is the template.
2. Legacy tail at `JQC` (a statement D/E must export; today only `LegacyTailA O D` at `JQ`).
3. Runtime fit and joint satisfiability of `RefLawsAOps` / `RefLawsATele`: research item.
