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

F2 scope: MainA now covers L1–L3 at JQ level (`core_tripleA_main`). L4 (JQC, `hbodyC`, full entry)
is E's and is a SEPARATE piece; the F round-1 `*_of_exports` composition over abstract `H/Lg/BS` was
removed (it counted abstractions as reduced premises).

## 3. Audit table (F2): remaining premises of the JQ-level main theorem

Theorems: `Tools.ShippingChildComposeA.{bodyKeepsA_of_tele, bodyStepA_of_tele, childKeepsA_all_of_tele,
core_tripleA_of_tele}` (integrator) and `Tools.ShippingChildMainA.{bodyStepA_main, childKeepsA_main,
core_tripleA_main}` (F2). Each depth step is built inside the induction: `ChildKeepsA D` → D2 bridge
→ B `legacyImplA_of_tele` → A (`canonKeyA`, `legacyCachedA_of_impl`) / C (`projFieldNameA`) → D
`bodyKeepsA_frontends`. The handlers are NOT assumed at every depth. Status of the F2 build: see
REPORT-F2.md (header of MainA says UNBUILT/BUILT).

Words: **PROVED** (name), **PREMISE** (hypothesis of the theorem), **OPEN** (no proof, no hypothesis).
Joint satisfiability of the laws: logical inconsistency NOT PROVEN. `MkRefd` is a history, not
freshness. `RealChildA` is a history of past synthesis results, not semantic correctness.
opaque/extern/implemented_by counts are structural, not a runtime-fit proof.

| item | kind | owner | status | runtime fit |
|---|---|---|---|---|
| `O : RefLawsAOps MkRefd mref cref` (9 fields: `diag, frameT, excOk, frameQ, cacheSetQ, depthSetQ, frame, cacheSet, depthSet`) | law family | boundary (InvA) | PREMISE; no model of it built; inconsistency NOT PROVEN | OPEN (extern `ST.Prim.Ref.*`, Meta primitives, printers, `excOk` on Lean exceptions unmodelled) |
| `hA : AdmCtx O.quiet mctx cctx` | start context | boundary | PREMISE | OPEN (command→entry link not formalised) |
| `T : RefLawsATele O.quiet mref cref` | ADDED unproved boundary (law family) | C uses it; B's `legacyImplA_of_tele` uses it too | PREMISE. Never "premise-free". Not derived from `Ops`: B's three telescope laws and C's `projFieldNameA` stay OPEN at runtime; the `panic` arm covered in the model only | OPEN |
| `hTail : LegacyTailStepA O` (`∀ D ≥ 1, ChildKeepsA O D → LegacyTailA O D`) | TAIL, ONE hypothesis | D states `LegacyTailA`; B3 proves the generic tail from `hC` (`legacyTailA_of_step`) | PREMISE until B3 is integrated. Covers EVERY constant where both gates miss, also machine-route ones | OPEN |
| start `OutQ O.quiet w` (the `Triple` precondition) | RUN | integrator | PREMISE (first-entry ref contents, commands between entries: OPEN) | OPEN |
| `LegacyImplA`, `LegacyCachedA`, `CanonKeyA`, `ProjFieldNameA`, `ChildEntryA` at `JQ D` | handlers | B, A, C, D2 | PROVED inside each step from `hC`, `T` (no extra premise) | follows `T`/`O` |
| `BodyStepA`, `ChildKeepsA D` (D ≥ 1), core entry keeps `OutQ` | induction | D, DepthA | PROVED from the rows above | — |
| `JQC` (child-cache invariant), E's depth-0 initialisation (JQ-only on success after the clear; exceptions before the clear EQ) | cache half | E | SEPARATE, NOT claimed here; E not integrated | — |
| connection to semantic preservation / `ChildBnd` endpoint (L5–L8 above) | port | unit G (proposed) | OPEN | — |
| model→real ST correspondence | MODEL↔ST | nobody | OPEN | OPEN |

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

## 4. Proposed audit additions (integrator applies)

`Tools.ShippingChildMainA.bodyStepA_main`, `childKeepsA_main`, `core_tripleA_main`, plus
`import Tools.ShippingChildMainA` in Tests/Compiler/ChildVertAuditTest.lean.

## 5. Missing with no owner (proposals)

1. **Unit G — port the endpoint to the new boundary** (L5–L8): run unpacking under `JQ`/`JQC`
   (new `core_reads_inv`), `RealChild → RealChildA` in the consumer chain, `ChildBnd` replaced at the
   heads by `OutQ ∧ cv = {}`. Large, mechanical; the old chain is the template.
2. Legacy tail at `JQC` and the whole JQC level (E, not integrated) (a statement D/E must export; today only `LegacyTailA O D` at `JQ`).
3. Runtime fit and joint satisfiability of `RefLawsAOps` / `RefLawsATele`: research item.
