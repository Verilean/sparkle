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
| L1 | handlers at a stable `I` | `LegacyImplA` (B), `LegacyCachedA` (A), `CanonKeyA` (A), `ProjFieldNameA` (C, needs `RefLawsATele`) | PROVED relative to `T`: `legacyImplA_of_tele` (B; needs `ChildEntryA` at the same `I`, so built INSIDE each depth step), `legacyCachedA_of_impl`, `canonKeyA` (A), `projFieldNameA` (C) — composed per step in `bodyKeepsA_of_tele` (ComposeA) / `bodyKeepsC_of_tele` (ComposeC) | A, B, C |
| L2 | `BodyStepA O` | all depths ≥ 1: `ChildKeepsA D → body keeps JQ D` | PROVED relative to `T` and the tail: `bodyStepA_of_tele` (ComposeA, `∀ D, LegacyTailA`) / `bodyStepA_main` (MainA, step-form tail `LegacyTailStepA`) via D `bodyKeepsA_frontends` | D, B3 (tail) |
| L3 | core entry, `OutQ → OutQ` | `core_tripleA_of_bodies` | PROVED relative to L2: `core_tripleA_of_tele` (ComposeA), `core_tripleA_main` (MainA) | — |
| L4 | cache half (SEPARATE induction, not inferred from JQ) | `hbodyC` at `JQC (D+1)`; `core_tripleAC`, `full_tripleAC`, `closeInstsM_realA'` | PROVED relative to `T` and `LegacyTailC`: E `childKeepsC_all`, `core0_tripleAC`/`full0_tripleAC` (outermost: JQ prefix/EQ before the clear, JQC after, EQC→EQ), E2 `bodyStepC_of_tele`, `core_tripleAC_of_tele`, `full_tripleAC_of_tele` (ComposeC) | E, B3 (tail at JQC) |
| L5 | run unpacking under the NEW boundary | `core_reads_invA`, `synthesizeFromConst_machine_invA`, `machine_run_of_coreA` (Tools/ShippingChildRunA.lean): a returning run of the core from `JQ O.quiet D` (+ `CacheInvA O (cv w)` if `D ≠ 0`) contains `getConstInfo`, `getEnv` and the body from a `JQC O (D+1)` world; on the machine route a run of `synthesizeMachineCertified` starts in `JQC O (D+1)` (depth ≥ 1). Premises: `O`, `hA`, the start world, `MachineDefines` (as in the old `machine_run_of_core`) | **PROVED** (g9, g10 exit 0; audit g13) | G |
| L6 | children of the closings are `RealChildA` | `closeInstsGM_realC`, `synthesizeMachineCertified_runsA`, `machine_children_realA'` (Tools/ShippingChildRunAKids.lean; the one-output closing is DepthC `closeInstsM_realC`). Premises: `BodyStepC O` (ComposeC `bodyStepC_of_tele` from `T`), `htr` (restricted translator keeps `JQC O (D+1)`; per-step in ComposeC, NOT yet instantiated here), `MachineClosesAtA` (no fallback; analogue of the old `MachineClosesAt`, a PREMISE) | **PROVED** relative to those premises; OPEN: instantiate `BodyStepC`/`htr` from the final ComposeC (`T`); `MachineClosesAtA` UNRESOLVED (premise, stays explicit) (g11 exit 0; audit g13) | G |
| L7 | consumers of `RealChild` | `childLink_real`, `entryStrict_real`, `realChild_of_childrenReal`, `callWidthsStrict…`, 92 files mention `RealChild mref cref` (grep count; not all use the quiet field); the leaf chain uses the *run* `hr` of the callee + `core_reads_inv L`. Port to `RealChildA O` (which carries the same `hr` plus `AdmCtx`, `sv`, quiet) | **OPEN** (list: `grep -l "RealChild mref cref" Tools/`) | `childLink_realA` done (L7a). NOT a completion condition: porting all ~90 files. Ported only along the dependency path of the main endpoints: next `entryStrict_realA` (small unit), then the consumers that need `ChildrenRealA` (`children_widths_real`, `callWidthsStrict_real`, `parent_children_widths_real`, via G's `machine_children_realA'`) |
| L7a (unit K) | `childLink_real` on `RealChildA` | `Tools.ShippingChildLinkA.childLink_realA (entry) (ResD) (P5) (hy : RealChildA O c y)`: same conclusion as `childLink_real`, premises `MachineDefines`, `ResDeclAt`, `P5At` unchanged. The minimal read witness is the callee's `getConstInfo`/`getEnv` reads, given law-free by `synthesizeCombinationalCore_reads` from the run inside `RealChildA` (the old proof used `core_reads_inv L`, an old `RefLaws`). No extra premise. | **PROVED** (built k2 exit 0; audit k3 exit 0: no RefLaws in closure, axioms standard). A history of a past run, not current-environment correctness. Conclusion = existence of the callee's shape and result kind only, NOT the meaning of the result `y` or its ports | K |
| L8 | leaf/parent heads | `leaf_names`, `leaf_input_widths`, `leaf_sat_design_closed5`, `<p>_sat*` take `ChildBnd`; replace by the start premise `JQ O.quiet 0` — the entry CLEARS the child cache itself (E `core0_tripleAC`/`full0_tripleAC`: JQ prefix, exceptions before the clear `EQ`, `JQC O 0` after it), so NO `cv w = {}` premise is needed | **OPEN** (statement change of the endpoint's premise — to be agreed) | G |
| L9 | endpoint premise: the entry's start world | `JQ O.quiet 0 w` = `OutQ O.quiet w` (quiet + `sv w = some synthesizeChild` + depth 0); no condition on the child cache `cv` | PREMISE (run hypothesis; command→entry link not formalised, R13/R14 in open-items §1) | integrator / OPEN |

F2 scope: MainA now covers L1–L3 at JQ level (`core_tripleA_main`). L4 (JQC, `hbodyC`, full entry)
is E's and is a SEPARATE piece; the F round-1 `*_of_exports` composition over abstract `H/Lg/BS` was
removed (it counted abstractions as reduced premises). The names `handlers_of_exports`, `bodyStepA_of_exports`,
`core_tripleA_of_exports`, `hbodyC_of_exports` no longer exist; the rows above give the current theorems.

## 3. Audit table (F2): remaining premises of the JQ-level main theorem

Theorems (par/int-r3, 0eaf1602): `Tools.ShippingChildComposeA.bodyKeepsA_of_tele` (the per-depth step,
tail as an argument) and `Tools.ShippingChildMainA.{bodyStepA_main, childKeepsA_main, core_tripleA_main}`
(the tail built in the same step from `hC` by B3 `legacyTailA_of_step`). JQC (separate induction):
`Tools.ShippingChildComposeC.{bodyKeepsC_of_tele, bodyStepC_of_tele, childKeepsC_all_of_tele,
core_tripleAC_of_tele, full_tripleAC_of_tele}` (tail at JQC from B3 `legacyTailA_generic`). Each depth step is built inside the induction: `ChildKeepsA D` → D2 bridge
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
| legacy tail (`LegacyTailA O D`; at JQC the generic tail) | tail | B3 | PROVED inside each step from `hC` and `T` (`legacyTailA_of_step`; `legacyTailA_generic` at JQC) — no tail premise remains | follows `T`/`O` |
| start `OutQ O.quiet w` (the `Triple` precondition) | RUN | integrator | PREMISE (first-entry ref contents, commands between entries: OPEN) | OPEN |
| `LegacyImplA`, `LegacyCachedA`, `CanonKeyA`, `ProjFieldNameA`, `ChildEntryA` at `JQ D` | handlers | B, A, C, D2 | PROVED inside each step from `hC`, `T` (no extra premise) | follows `T`/`O` |
| `BodyStepA`, `ChildKeepsA D` (D ≥ 1), core entry keeps `OutQ` | induction | D, DepthA | PROVED from the rows above | — |
| `JQC` (child-cache invariant), E's depth-0 initialisation (JQ-only on success after the clear; exceptions before the clear EQ) | cache half | E, E2 | PROVED relative to `O`, `hA`, `T`, start `JQ O.quiet 0` (ComposeC; separate induction, not inferred from JQ) | follows `T`/`O` |
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

## 4. Audit (applied)

Tests/Compiler/ChildVertAuditTest.lean imports MainA, ComposeC, LegacyTailA and audits
`ComposeA.bodyKeepsA_of_tele`, `MainA.{bodyStepA_main, childKeepsA_main, core_tripleA_main}`,
`ComposeC.{bodyKeepsC_of_tele, bodyStepC_of_tele, childKeepsC_all_of_tele, core_tripleAC_of_tele,
full_tripleAC_of_tele}`, `LegacyTailA.{legacyTailA_generic, legacyTailA_of_step}` (with the earlier
A/B/C/D/D2/E entries). Build status: see the integration round table (int-r3a).

## 5. Missing with no owner (proposals)

1. **Port the endpoint to the new boundary** (L5–L8): unit G — run unpacking under `JQ`/`JQC`
   (`core_reads_invA`/`machine_run_of_coreA`); unit K — `RealChild → RealChildA` in the consumer chain,
   starting with `childLink_realA` (minimal read witness; `ResDeclAt`/`P5At`/`MachineDefines` kept);
   `ChildBnd` at the heads replaced by the start premise `JQ O.quiet 0` (no `cv = {}`: the entry clears
   the cache). A CONDITIONAL connection to the existing semantic-preservation endpoints.
2. (done) Legacy tail at `JQC` and the JQC level: integrated (ComposeC with B3's generic tail).
3. Runtime fit and joint satisfiability of `RefLawsAOps` / `RefLawsATele`: research item.
