# Reader fuel candidate — boundary table (decision material for a production switch)

Integrator, 2026-10-16, poc a3a1d2d4. Ruling 2026-10-16 item 4: O1 / O2 are NOT added as axioms or allowed
binders. This table separates what is PROVED (kernel, standard axioms) about the isolated fuel candidate from
what is UNMODELLED about the old compiled `partial` reader. Production still calls the partial reader; nothing
here switches it.

## Proved (kernel)
| Claim | Theorem(s) | File | Commit |
|---|---|---|---|
| A finished fuel answer is stable under more fuel; two finished answers are equal | `fuel_stable`, `fuel_det`, `readF_stable`, `readF_det`, `machNormF_*` | ShippingReaderFuelKleene | 22908c5f |
| Finite-execution adequacy: `Eval senv c r ↔ ∃ n, readF senv n c = some r` (success and ordinary refusal; machNorm too) | `eval_fuel`, `fuel_eval`, `eval_iff`, `evalN_*` | ShippingReaderFuelEval | 36d6b5ef |
| Agreement with every solution of the transcribed old equations | `readF_agree_old`, `machNormF_agree_old` | ShippingReaderFuelOldEq | fc697219 |
| Agreement with every solution of the VERBATIM source equations of Elab.lean | `readF_agree_verbatim`, `machNormF_agree_verbatim` | ShippingReaderFuelVerbatim | 8fac0511 |
| R5 (LenOk) for every fuel and every successful result of the 7 fuel functions | `readersKeepLenOkF`, `machXF_lenOk` | ShippingReaderFuelR5 | 9a5ccc93 |
| Wrapper keeps OUT/FAIL/OK; OUT propagates through sharing probes | `findSomeO_out_append`, `findSomeO_fail_all`, `nestedStep_out_of_search` | ShippingReaderFuelShape | 65eaccbb |
| Bounded driver: FAIL / OK it returns are genuine and stable; it never produces FAIL for OUT | `driveShape_res`, `driveShape_fail_sound`, `driveShape_ok_sound` | ShippingReaderFuelDriver | 65eaccbb |
| Driver eventual completion: some fuel decides → some rounds give the same answer; OUT forever ↔ every fuel OUT; a finite wrapper derivation → driver answer | `driveShape_complete(_ok/_fail/_iff)`, `driveShape_out_forever_iff`, `shapeRuns_drive` | ShippingReaderFuelDriverComplete | fe65d4c5 |
| Wrapper adequacy both ways: `ShapeRuns … r ↔ ∃ N, machineShapeF N … = some r ↔ ∃ rounds, driver answer r` (success and refusal); no finite execution ↔ every fuel OUT | `compact_shapeW`, `fuel_shapeRuns`, `shapeRuns_iff`, `shapeRuns_drive_iff`, `shapeRuns_none_iff` | ShippingReaderFuelShapeEval | 25f877f8 |
| Resumable driver (total, no finite budget ending in a verdict): budget stop = resumable state, never a refusal; returned answers carry a fuel witness and are genuine; retries carry only the fuel; eventual completion from ∃ fuel and from a finite derivation | `runShapeFor_sound`, `runShapeFor_genuine`, `resumeRun_view`, `runShapeFor_complete_le`, `runShapeFor_resume_complete`, `shapeRuns_resume` | ShippingReaderFuelDriverResume | a6573291 |
| A finite wrapper derivation ⟺ the resumable driver (any start) eventually answers the same with a fuel witness (success and refusal) | `shapeRuns_iff_resume`, `shapeRuns_ok_iff_resume`, `shapeRuns_fail_iff_resume` | ShippingReaderFuelResumeEval | (this commit) |
| A solution of the source equation need not be reached by any fuel (so coverage does not follow from the equation alone) | `fixpoint_not_complete` | ReaderFuelGeneric | 0a53bd9e |

## Measured (not proved)
| Evidence | Scope | Commit |
|---|---|---|
| Driver vs real `machineShape?`: same class and all compared shape fields | 18 declarations (12 OUT→OK, 2 OUT→FAIL, 4 immediate FAIL) | 65eaccbb |
| prodMatcherArity?/projChain shadows (earlier switches) | grid + 260k-constant sweep | 9b86eb38 |
| Fixed-list shadow, start fuel 1: real vs driver, ALL shape fields | 40 real declarations (33 OUT→OK, 3 OUT→FAIL, 4 FAIL at 1), no TIMEOUT | f5df0683 |

## Unmodelled / open (NOT axioms, NOT binders)
| Id | Statement | Why outside |
|---|---|---|
| O1 | A run of the compiled `partial` reader that RETURNS corresponds to a finite derivation (`Eval`), hence to some fuel | the compiled code's runtime is not modelled; `Eval ↔ ∃ fuel` is proved, the link from the compiled run to `Eval` is not |
| O2 | The real compiled `partial` constants satisfy their verbatim source equations (`OldEqV`) | properties of opaque compiled constants are not kernel-checkable |
| O3 | Opaque Expr primitives (`instantiate1`, `liftLooseBVars`, `Expr.eqv`, …) and still-partial helpers (`rootFloat`, `zetaAll`, `rawNode`, …) behave as their text; they terminate | fixed constants inside `step`; their termination is not claimed |
| — | A final OUT of the bounded driver says nothing about the real reader | `2^rounds · start` is finite; deeper finite executions exist (P2 correction a3a1d2d4) |

## Still to produce before a switch decision (ruling 2026-10-16)
* Driver eventual completion — DONE (fe65d4c5).
* Wrapper-level R5 — DONE (see the section below).
* Fixed-list shadow — DONE (f5df0683): 40/40 equal.
* OldEqV source version recorded + drift check — DONE (fe65d4c5; `oldeqv_drift.py`, no drift).
A switch would in addition need: the compiler path calling the driver WITHOUT mapping OUT to refusal / legacy,
and the existing suite + shadows + corpus comparison (corpus rerun not approved yet).
CORRECTION (2026-10-17, reviewer): "OUT reported as an error" is NOT an acceptance-preserving route — a finite
budget followed by an error can reject an input the old reader accepted. Budget / cancellation errors may exist
only as experimental operational outcomes; they are neither a semantic refusal nor evidence of equivalence. The
only candidate route under consideration is an unbounded or resumable driver (no finite budget ending in a
verdict), and no production switch is planned.

## Wrapper-level R5 (worker H, 9eb01c91) — BUILT with integrator fixes
Applied on poc fbb445d0. Run `h1` (cgrun, 3 GiB, swap 0, `-j 1`). As written `Tools.ShippingReaderFuelShapeR5`
failed in two proofs (no statement changed): `okO_run_inv` (`injection` already closed the goal → one-line
`Option.some.inj`), `shapePost_decomp` (the inversion loop lacked `split at h` for the `match p.tup?` of the
output fields, and the final `ite` inversion is optional in some branches). Then `Tools.ShippingReaderFuelShapeR5`
and `Tools.ShippingCallWidthsEntryF` exit 0. Axioms of all theorems below: [propext, Classical.choice,
Quot.sound].
PROVED for EVERY successful candidate-wrapper result `machineShapeF n … = some (some sp)` (state kept through
start / root lets / body; `machineShapeF_steps`, `machineShapeF_lenOk`): `machineShapeF_decomp` (a `ShapeDecomp`
with names / kinds / inits of equal length), `machineShapeF_r5` (R5: `(names.zip kinds).length =
sp.layout.slots.length`), `machineShapeF_binderCount`, `machineShapeF_nDecl` (the closing's nDecl = `bs.length`),
`machineShapeF_callBinder`, `machineShapeF_slots_length`.
CONSUMER REDUCED (alternative next to the unchanged `entryStrict_of_links`): `entryStrict_of_linksF` /
`callWidthsStrict_of_linksF` — premises `NIN` (`d.nIn = bs.length + insts.length`) and `R5ok` (`d.r5Ok = true`)
DISAPPEAR, the links being candidate-wrapper successes (`LinkPF`, `LinkCF`).
NOT counted for the old compiler: these are about `machineShapeF`; transferring them to the real `machineShape?`
needs O1 + O2.

## Call widths, heterogeneous children + candidate R1 (worker K, par/r-15) — BUILT (k1 partial fail, k2/k3 exit 0; see below)
Reviewer 2026-10-17 item 2. From poc 20304f50. Four new files (old theorems unchanged):
`Tools/ShippingCallWidthsEntryFH.lean` (a), `Tools/ShippingReaderFuelR1.lean` + `Tools/ShippingReaderFuelShapeR1.lean`
(b), `Tools/ShippingCallWidthsEntryFR1.lean` (a + b). All about the CANDIDATE wrapper `machineShapeF`; NOT counted
for the old compiler (needs O1 + O2).

(a) `callWidthsStrict_of_linksFH` (+ `_'` with index functions): every call entry `k` has its OWN child
declaration, candidate link (own fuel / signature table / flags), shape and result kind (`ChildLinkF d kidOuts k`).
`callWidthsStrict_of_linksF_via_FH` re-derives the homogeneous theorem as the special case.

(b) Candidate R1. Invariant `InstR1 senv st` (every `insts` entry whose callee has `senv.inst c = some (_, r')` has
kind `r'`), proved for every fuel by the same arm-by-arm induction as R5 (`readF_good1`), carried through the
wrapper (`machineShapeF_instR1`, `machineShapeF_r1k`, `machineShapeF_r1At` = the old `R1At` predicate). Where the
reader builds call entries: `instStep` pushes `(c, js, res)` with the CALL's `res`; the `machInstCall?` arm takes
`(c, kinds, res)` from `senv.inst c` (R1 by construction, `machInstCall?_inst`); the memory arm calls with
`memChildName combo aw dw` / `.bits dw` (needs `MemR1`); `instSStep` appends entries of a STRUCTURE callee
(`machInstCallS?`: `senv.instS c = some _`; needs `senv.inst c = none`, i.e. `SigDisj`, PROVED for `structEnv env`
because `instSignature?` requires `machResultKind? = some _` and `instSignatureS?` requires it `none`).
The ONE fact R1 needs that the candidate reader does not establish: `MemR1 senv` — the compiler-built memory
placeholder names carry no one-Signal signature with a result other than `.bits dw` (holds when no
`@[hardware_module]` has such a name, `memR1_of_none`; an environment fact, not a reader fact).

### Premise table (new theorems)
| Premise | Theorem(s) | Status | Discharged by / why still assumed |
|---|---|---|---|
| `LinkPF` (parent = candidate result) | all | ASSUMED | a candidate-wrapper success; for the real compiler needs O1 + O2 (`machineShape?` → `machineShapeF`) |
| `NIN` | `…FH`, `…FH_sig`, `…FH_declared` | DISCHARGED | not a premise: R5 at the closing's `nDecl` from the candidate state (`machineShapeF_callBinder`) |
| `R5ok` | same | DISCHARGED | same (not needed for the conjuncts) |
| `NIN` in `r5Ok_of_linkF` | `r5Ok_of_linkF` (EntryF) | STILL ASSUMED | the DATA check `d.r5Ok` mentions `d.nIn`, which no candidate fact relates to the peel; only the data-free `shapeR5Ok_of_linkF` is NIN-free. NOT counted as solved |
| child link `LinkCF` (per entry) | all | ASSUMED (per entry) | candidate success of each child; old compiler: O1 + O2 |
| `ResC` (per entry) | `…FH`, `…FH_sig` | ASSUMED | for the unfolded entry constant (`inlinedConst (userInliner env) ci`) it is P5 (opaque `userInliner` on a type) |
| `ResC` (per entry) | `…FH_declared` | DISCHARGED | `resC_of_declared` from `hinst` + `hfind` (child linked at the DECLARED constant) |
| `hkid` (per entry) | all | ASSUMED (trivial) | the consumer's choice of `kidOuts` (`rfl`) |
| `R1k` (per entry) | `…FH` | ASSUMED | (form without signature data) |
| `R1k` (per entry) | `…FH_sig`, `…FH_declared` | DISCHARGED | `machineShapeF_r1k` (candidate R1) from `hcallee` + `hinst`, parent read with `structEnv env` |
| `hcallee` (entry `k`'s callee is `c`) | `…FH_sig`, `…FH_declared` | ASSUMED | a lookup in the reflected shape (`decide`-able on `d.shape.insts`) |
| `hinst` (`(structEnv env).inst c = some (kinds, res)`) | `…FH_sig`, `…FH_declared` | ASSUMED | an environment lookup; the candidate does not record WHICH table entry produced an `insts` entry (a memory or structure entry has none) |
| `hfind` (`env.find? c = some (.defnInfo dC)`) | `…FH_declared` | ASSUMED | environment lookup |
| `MemR1 (structEnv env)` | `…FH_sig`, `…FH_declared`, `machineShapeF_r1At` | ASSUMED | the only reader-call-site fact R1 needs that the reader does not establish (memory placeholder names vs. the environment's `@[hardware_module]` signatures) |
| `SigDisj` | `machineShapeF_r1k` (general `senv`) | DISCHARGED for `structEnv env` | `sigDisj_structEnv` |
| `hk` (`k < insts.length`) | per entry | DISCHARGED | supplied by `callWidthsStrict_of_entries` |

Predicted axioms: [propext, Classical.choice, Quot.sound] (as the R5 line). Build order: `ShippingCallWidthsEntryFH`,
`ShippingReaderFuelR1`, `ShippingReaderFuelShapeR1`, `ShippingCallWidthsEntryFR1` (the first is independent of the
other three).

### Integration of worker K (2a6e0d87) — BUILT with integrator fixes; PREMISE TABLE (current)
Applied on poc a6573291 (lakefile conflict on appended lean_libs: kept both). Runs (cgrun, 3 GiB, swap 0, `-j 1`):
`k1` — `lake build Tools.ShippingCallWidthsEntryFH` exit 0, `Tools.ShippingReaderFuelR1` exit 0,
`Tools.ShippingReaderFuelShapeR1` exit 1 (a multi-line `first` alternative did not parse; a `rw [he] at hc ⊢`
after `cases he :` found nothing in the goal) → integrator fixes (one line per alternative; `try rw` on the
hypothesis and the goal separately; no statement changed) → `k2` — `…ShapeR1` exit 0, `Tools.ShippingCallWidthsEntryFR1`
exit 0; `k3` (header updates) exit 0. Axioms: `readF_good1` [propext, Quot.sound]; `callWidthsStrict_of_linksFH`,
`callWidthsStrict_of_linksF_via_FH`, `sigDisj_structEnv`, `machineShapeF_r1k`, `machineShapeF_r1At`,
`callWidthsStrict_of_linksFH_sig`, `callWidthsStrict_of_linksFH_declared` [propext, Classical.choice, Quot.sound].

Remaining premises of the candidate call-width theorems (all about the CANDIDATE wrapper; nothing counted for the
old compiler without O1 / O2):
| Premise | `…linksF` (homog.) | `…linksFH` | `…linksFH_sig` | `…linksFH_declared` |
|---|---|---|---|---|
| parent candidate link `LinkPF` | assumed | assumed | assumed | assumed |
| per-child candidate link | one shared `sc` | per entry (assumed) | per entry (assumed) | per entry (assumed) |
| `NIN`, `R5ok` | discharged | discharged | discharged | discharged |
| `R1k` | assumed | assumed | DISCHARGED (`machineShapeF_r1k`) | DISCHARGED |
| `ResC` | assumed | assumed | assumed | DISCHARGED (`resC_of_declared`) |
| `hkid` | assumed (trivial: `kidOuts` choice, `rfl`) | same | same | same |
| `hcallee` / `hinst` (env lookups) | — | — | assumed | assumed |
| `hfind` (env lookup) | — | — | — | assumed |
| `MemR1 (structEnv env)` (memory placeholder name has no conflicting signature) | — | — | assumed | assumed |
| `SigDisj` | — | — | discharged for `structEnv` | discharged |
Separately: `r5Ok_of_linkF` STILL needs `NIN` (the data check mentions `d.nIn`); only the data-free
`shapeR5Ok_of_linkF` is NIN-free — NOT counted as solved.

### Header corrections (integrator, 2026-10-17, reviewer supplement)
* `…FuelDriverComplete`: the phrase "a finite derivation (equivalently, some fuel)" was premature in that file;
  it now says the equivalence is `shapeRuns_iff` in `…FuelShapeEval` (25f877f8), not proved there.
* `…FuelDriverResume`: "pure total function" / "the very function that is executed" could be read as a runtime
  termination guarantee. Corrected: "total" is a property of the MODEL; one attempt is NOT claimed to terminate
  or be cancellable at run time — the still-partial helpers / opaque primitives (O3/O4) have unproved termination
  and runtime agreement.
* New `Tools/ShippingReaderFuelResumeEval.lean`: `shapeRuns_iff_resume` = `shapeRuns_iff` ∘
  `resumeShape_answers_iff`. Run `m1`: `cgrun -n m1 -m 3G -j 1` — `lake build Tools.ShippingReaderFuelDriverComplete
  Tools.ShippingReaderFuelDriverResume` exit 0 (headers), `lake build Tools.ShippingReaderFuelResumeEval` exit 0,
  `#print axioms` (via `lake env lean`): `shapeRuns_iff_resume`, `shapeRuns_ok_iff_resume`,
  `shapeRuns_fail_iff_resume` [propext, Classical.choice, Quot.sound].

## Round 2026-10-18 (reviewer on 3a1938a3)

**Scope correction.** `ChildLinkFS` / `ChildLinkFD` need `senv.inst c = some _` for EVERY entry; memory placeholders may
have none, structure-field entries have `instS` some / `inst` none. The FH/FR1 theorems are heterogeneous
SINGLE-SIGNAL-child theorems, not all-entry coverage. `hinst` is not a trivial lookup and is not proved universally.

| Unit | Commit | Build | Axioms |
|---|---|---|---|
| Provenance invariant `InstProv` (ordinary / structure field with index, name, kind / memory with combo, aw, dw > 0), `readF_goodP` all fuels, NO MemR1 / SigDisj; wrapper lift `machineShapeF_origin` | 6f216c4e (S-PROV) | `p1`, `p2` exit 0 as written | standard (`axp`) |
| Exact per-entry obligation `entryStrict_iff_kidOutsOk`; per-kind `ChildLinkOrdD` / `ChildLinkStruct` / `ChildLinkMem`; MIXED `callWidthsStrict_of_linksFM`; `childLinkMem_of_outTys` (real memory module); `_declared` re-derived as corollary | 6f216c4e | `p2` exit 0 | standard |
| Real child dispatch audit (`docs/parallel/S-child-dispatch-audit.md`); `callWidthsStrict_real` with `kidOuts k` = the callee's `MachineDefines` shape at its entry constant (hkid removed), `children_widths_real`, `parent_children_widths_real` (children = the list `closeInsts(G)` consumed) | b35d4ff5 (S-DISP) | `cr1` exit 0 as written | standard (`ax18`) |
| Memory placeholder collision: measured MISCOMPILE in `closeInstsGM` (probe); `MemR1` false in a real env and not the guarding property; guarded model + dispatch theorems; compiler fix PROPOSED, not applied (`docs/parallel/S-memname-collision.md`) | db3179b3, 85b7d1b5 | `mc2`, `mc4` (probe), `md1` exit 0 | standard; `not_memR1_all` none |
| Header hygiene (k1 failures recorded, measured axioms) | 08553a05 | `hd18` exit 0 | `ax18` |

### Premise table (current)

| Premise | Status |
|---|---|
| Parent `LinkPF` (candidate) | assumed (O1/O2 for the real reader) |
| Ordinary child link `ChildLinkOrdD` | assumed (`hcallee`, `hinst` now supplied by provenance) |
| Structure-field obligation `ChildLinkStruct` | ASSUMED; deriving it from the structure child's own link needs layout vs `machOuts?` field list — open |
| Memory obligation `ChildLinkMem` | discharged from `ChildOutTys … (memModule combo aw dw)` |
| R1k / NIN / R5ok in `callWidthsStrict_of_linksFM` | not needed (provenance) |
| MemR1 | not needed by the mixed theorem; still a premise of `readF_good1` / `_declared` corollary; FALSE for some real envs |
| hkid | removed in `callWidthsStrict_real` (real callee's layout); still a rfl-binder in FH/FM (model choice, NOT emitted-child agreement) |
| ResC for the UNFOLDED child (P5) | EXPLICIT premise `P5At` (`inlinedConst` rewrites the type); `ResDeclAt` assumed |
| Callee `MachineDefines`, `ChildBnd`, `LeafKid`, `PB`, `memChild? = none` | assumed (reflection boundary / leaf scope / decidable checks) |
| ChildrenReal / cache | discharged from the parent run (`CacheInv`) |
| NIN in `r5Ok_of_linkF` | still assumed |
| Memory-name dispatch correctness of the REAL compiler | FALSE today (miscompile); holds in the guarded model only |

Production obligations still open: O1–O4 (distinct; none added as axiom or binder), the compiler fix approval for the
memory-name collision, `ChildLinkStruct` derivation, P5, non-leaf callees' `ChildOutTys`. CI: 0 runs for these SHAs.
