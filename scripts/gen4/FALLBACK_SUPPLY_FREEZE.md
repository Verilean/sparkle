# M4: fallback / legacy / memo-hit success routes — freeze (rev3 + §9 rev5 + §10 T-INV keep types, FOR REVIEW; rev1 = f92e2410, rev2 = a7f9753b; §9 rev4 = 658d2b8d)

- **Issue:** `sparkle-gen4-fallback-supply` (milestone `sparkle-gen4`; depends on `sparkle-gen4-routes`, done).
- **Base:** branch `kjob/g4fb-d0ddc50b` at d0ddc50b (rev3 is written on `kjob/g4fb-r3`, branched from a7f9753b). All `file:line` below are at that SHA. `Sparkle/Compiler/Elab.lean`
  is identical to `par/gen2-spec` there, so the lines in `scripts/gen2/ROUTE_CENSUS.md` still apply.
- **Status (synced after FB-2 approval at e7181279):** this document is docs. Lean exists only for the approved units: FB-1 (existence predicate, built g4fbv-79e6d672) and FB-2 (`R4Run`, `A4MachineSideA`, `a4_machine_or_R4Run`; built g4fb2v-e7181279; approved as a repackaging of the same A4 witness, not as a semantic guarantee of R4 and not as a T-INV supply). No production edit. Any further Lean needs its types frozen here and approved first.
- **Sources read:** `scripts/gen2/GENERAL_SPEC.md`, `GEN2_DEFS.lean.txt`, `ROUTE_CENSUS.md`; `Tools/ShippingGen2Defs.lean`;
  `Tools/ShippingLegacySemContract.lean`, `…EntryWalk.lean`, `…Memo.lean`, `…Instance.lean`; `Tools/ShippingMemoInv.lean`,
  `…MemoLaws.lean`, `…ChildCacheA.lean`, `…MachineOutcomeA.lean`, `…ServedRealA.lean`, `…ChildLegacyTailA.lean`,
  `…MachineClosesData.lean`; `Sparkle/IR/Machine.lean`; `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` (DG-FALLBACK),
  `T2COVER_FREEZE.md`, `M5_INDEP_STUDIES.md`; `par/gen4-gate:scripts/gen4/GATE_LEAF_RESULT.md`.

**What this document is not.** It is not a proof and not a supply of anything. It does not claim that a fallback, legacy
or memo-hit success is impossible, underivable or unreachable. Where it says "this investigation found no supplier /
path", that means exactly that: the files above were read and no supplier was found. A mutant or a `Prop`-level
premise in a later check is a rejection by signature/defeq, never a semantic counterexample.

---

## 0. rev3: response to the review of a7f9753b (R1–R3) and unification with the gate Issue

Nothing is withdrawn except what each item says. FG is not narrowed; no shared definition, law or compiler file is edited. The gate Issue's files are not edited.

**U. Unification with the gate side (`sparkle-gen4-gate-supply`).**
Read: `git show kjob/g4gate-r2:scripts/gen4/GATE_SUPPLY_FREEZE.md` at 3aab70fc (§3.0 and Q2). Its status in the Issue: U-G1 (child interface extraction) is **approved** for implementation, with `ChildIface` as the leading basis; the fallback side must not implement a parallel interface or a second file of the same name, and must present an import/adapter proposal.
- **Owner / order.** The gate Issue owns `ChildIface` and `Tools/ShippingGen4Iface.lean` (U-G1, base `06b8ca92`, whose `Tools/ShippingGen2Defs.lean` is byte-identical to d0ddc50b's per the gate freeze). The fallback Issue is the second approved side, so by the gate rule (Q2) it supplies the bridge **in its own file only**. Order: (1) gate U-G1 lands; (2) fallback adds its adapter/bridge file importing it; (3) neither edits the other's files. **Until (1) is built, no fallback Lean is written.**
- **Reference SHA for the common interface.** `ChildIface` = the text of gate freeze §3.0 at 3aab70fc, to be re-checked against the gate branch SHA that actually builds U-G1 (the unit's note records that SHA). `ChildShips` of Defs at d0ddc50b (Gen2Defs.lean:87-90) is the reference both sides are equal to.
- **Decision.** rev1/rev2's `IfaceData`/`Pkg.iface`/`ChildShipsD`/`childShips_iff` (rev2 §5.1) are **not implemented** by this Issue. They are replaced by the gate's names (table below). No second interface record, no second `Tools/ShippingGen4Iface.lean`.

| fallback rev2 | gate `ChildIface` (U-G1) | relation |
|---|---|---|
| `IfaceData.bsC : List (Name × MixedGateBinder)` | `ChildIface.bsC` | same type; both `q.d.bsIn.take q.kD` for a package |
| `IfaceData.outsC : List OutField` | `ChildIface.outsC` | same type; both `q.d.shape.layout.outs` |
| `IfaceData.S : ι → (Nat → List Nat) → List (Nat → Nat)` | `ChildIface.S` | same type; both `q.S` |
| (none) | `ChildIface.decl : Name` | extra field in the gate record; fallback needs it for `q.decl = c` and it is `q.decl` for a package |
| `Pkg.iface q` | `ChildIface.ofPkg q` | same definition up to the `decl` field: `Pkg.iface q` = `ofPkg q` with `decl` forgotten |
| `ChildShipsD I n mc Dc` | `ChildShipsI I n mc Dc` | same body (Defs:87-90 with the three reads replaced); neither reads `decl` |
| `childShips_iff q … : ChildShips q ↔ ChildShipsD q.iface` | `childShipsI_ofPkg q … : ChildShipsI (ofPkg q) ↔ ChildShips q` | gate's lemma is the same statement, `Iff.rfl` |
| rev2 `∃ q n, P c = some q ∧ q.decl = c ∧ ChildShipsD q.iface n b D` | `ShipsResI` conjunct `∃ I n, Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2`, with `Q = P.iface`, and `shipsResI_iface` | the fallback conclusion is stated with the gate's `ChildShipsI (ChildIface.ofPkg q)`; `shipsResI_iface` links it to `ShipsRes` |
If a later change makes the correspondence non-trivial, the adapter (`IfaceData.toChildIface (decl) …` with a field-equality lemma, in the fallback file) is added then; with the table above no adapter definition is needed, and none is introduced now.

**R1 — LegacyChildShips lacked a current-`c` package/route hypothesis (LegacyChildShips removed from the first unit).**
The reviewer's finding is accepted: `InvAt` constrains cache entries and `IHAt` deep successful runs; neither provides a package for the *current* `c`, rev2 §5.3's sentence "`P c` from `T1Hyp.pkg`" had no hypothesis in the type, and the whole `T1Hyp` cannot be added because its `closes` excludes R4.
rev3: `LegacyChildShips` is **not part of the first unit** and is not frozen as a Lean type here. §5.3 keeps only the *requirements* a later R4-local statement must state explicitly (listed there); it is not a type to implement.

**R2 — `TookLegacyTail` is an existence predicate (renamed and limited).**
It says: there exist an environment, constant and two worlds with a run of `legacyTail` returning `(raw, D)`. Those worlds are not linked to the core run, so it is **not** evidence about THIS run. It is renamed `LegacyTailRunExists` and described only so (§5.2). No connection to the core run's decomposition is typed in rev3 (that is a later lemma, §5.2).

**R3 — "creating the bundle is necessarily a new law / user decision" is withdrawn.**
A memo/law bundle splits into two different things (§5.6, §7):
(a) **re-packaging or conditional transport of existing laws** (e.g. relating `RefLawsM` and `RefLawsAOps` instances by a lemma, or carrying `RefLawsM` as a hypothesis of a theorem): not shown to be a new law; whether it is enough is not established here. Design work, no user decision implied.
(b) **adopting a new real-environment guarantee as an assumption** (a law about the runtime that no existing law states): only this needs a user decision.
Which of (a)/(b) a given memo statement needs is OPEN; rev3 does not claim either.

**Kept from rev2 (accepted by the reviewer):** memo vs raw vs post-processed separation, outer/nested start separation; the general supply of the fallback/legacy/memo successes is **OPEN**, K4 remains unproved.

---

## 0b. rev2 text (kept for reference; superseded where rev3 §0 says so)


Nothing in rev1 is withdrawn except what each item below says. FG is not narrowed; no shared definition, law or compiler file is edited.

**R1 — `∃ I n` was not tied to the source (retracted).**
rev1's `LegacyShips`/`MemoHitShips` concluded `∃ I n, ChildShipsD I n b D` with `I : IfaceData` free. `I.S` was connected to nothing, and the `P` argument was not used in the conclusion, so the statement
said only "some interface exists". That form is **withdrawn**. In rev2 (§5.3):
- The conclusion names the interface through the declaration: `∃ q n, P c = some q ∧ q.decl = c ∧ ChildShipsD q.iface n b D`. `P c` is the package that `T1Hyp.pkg` supplies for the reached name `c`; `q.S` is built from `q.src`, the Lean-source signal function of the package.
  The obligation "the synthesized module `b` implements the SOURCE function `q.S`" is therefore the `ChildRunN` conjunct of the conclusion; it is a proof obligation of the producer, never a hypothesis.
- **Extracting `IfaceData` from a package is not a supply.** `Pkg.iface` is a projection (§5.1); `ChildShips q ↔ ChildShipsD q.iface` is `Iff.rfl`-level. Neither says anything about a module produced by a legacy or memo run.
- Scope of this tie, read from `T1Hyp` (Gen2Defs.lean:195-204): `T1Hyp.defines` requires `MachineDefines … c q.d.shape` for every reached `c` with a package, i.e. `machineShape? = some`. So the package tie covers
  **the R4 tail** (machine shape exists, `closeLets`/`closeInsts` declined). It does **not** cover **R6 direct** (`machineShape? = none`): no `Pkg` for such a declaration exists under the current `T1Hyp`, and a source interface for it is exactly D-IFACE (§7), not defined here.
  A non-package tie (`Denotes env c I`) would be a new definition about the meaning of source declarations; it is listed as an open design point, not supplied and not assumed.

**R2 — "complete telescope" was prose; `TookLegacyTail`/`MemoInvShips` undefined; `L.mval` does not exist (corrected).**
`Laws mref cref` has exactly two fields, `O : RefLawsAOps …` and `T : RefLawsATele …` (Gen2Defs.lean:46-48). There is **no** `mval`; `mval` is a field of `RefLawsM` (ShippingMemoLaws.lean:90-93), a separate bundle. rev1's `L.mval` was wrong and is withdrawn.
The first implementation unit (§5.5) is fixed with full Lean types: `IfaceData`, `Pkg.iface`, `ChildShipsD`, the bridge, and `TookLegacyTail` (§5.2, using `legacyTail` of ShippingMachineOutcomeA.lean:54 and the `MachineRunJQC` pattern of ShippingServedRealA.lean:90).
The **memo side is separated and undesigned** (§5.6): the law bundle that gives `mval` for `Laws`, `MemoInvShips`, and `MemoHitShips` are NOT defined in rev2. Unit 1 contains no memo definition.
The run-order account of §2 stays as the description of the program; the Lean-level objects are the types of §5, and §2 is not itself an evidence predicate.

**R3 — Start is depth 0 (distinguished).**
`Start L mctx cctx w := AdmCtx … ∧ JQC L.O 0 w` (Gen2Defs.lean:52). It describes the OUTERMOST root only. A fallback/legacy/memo run under a parent is a nested run: depth `dv w > 0`, `sparkleChildCache` non-empty, no reset (E5).
§5.4 gives two statements with different start conditions: the outer root (`Start`, conclusion `TopShips`) and the recursive producer (the hypothesis list of `StepStmt`, Gen2Defs.lean:255-259: `InvAt (dv w) w`, `IHAt (dv w + 1)`, `ChildKeepsInv (dv w + 1)`; conclusion `ChildShips`).
Raw vs post-processed transport is explicit: the memo holds the raw core result, `sparkleChildCache` and the parent's `IHAt`/`ShipsRes` talk about the post-processed `b` (K2); each statement carries `b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)`.
**K4 stays unproved.** rev2 adds no argument for it; §5.6 and M-1 state it as the open obligation of the memo side.

---

## 1. Dispatch table (with overlaps) — `synthesizeFromConst`, Elab.lean:5288-5414

The outer wrapper `synthesizeCombinationalCoreWith` (:5423-5583) runs first. Its effects matter for rows 5 and 8:
at `depth == 0` it sets `sparkleSubModuleCache` (:5540) AND `sparkleChildCache` (:5541) to `{}`; at `depth ≠ 0` it touches
neither (:5542-5553 resets only the six wire/instance caches). `sparkleSynthDepthLimit` check at :5466.

These are NOT disjoint success paths. The overlaps, stated as a relation on one run of `synthesizeFromConst`:

| id | branch | guard (Elab.lean) | writes memo? | result is | overlaps with |
|---|---|---|---|---|---|
| R1 | certified gate | `certifiedFrontEnd ∧ certifiedShape? = some` (:5290-5297) | yes (:5297) | `synthesizeCertified` | none (first match) |
| R2 | mixed gate | `… mixedCertifiedShape? = some` (:5299-5305) | yes (:5304) | `synthesizeMixedCertified` | none |
| R3 | machine, synthesis returned | `certifiedFrontEnd ∧ ¬symbolic ∧ parameters = [] ∧ machineShape? = some shape` (:5311-5319) and `synthesizeMachineCertified = some` (:5320-5324) | yes (:5323) | machine result | — |
| **R4** | machine **declined after the harness ran**, then legacy/memo | `machineShape? = some` and `synthesizeMachineCertified = none` (:5317, `none` arm :5325 → falls to :5326) | no write by R4 itself | whatever R5/R6 returns | transitions INTO R5 or R6; **the harness effects of R4 are already in the heap** |
| R5 | memo hit | `¬symbolicMode ∧ memo.get? declName = some cached` (:5334-5338) | no | `cached` | entered from R4, or when no machine shape / front end off |
| R6 | legacy | `.defnInfo` after R5 misses (:5340-5389) | yes if `¬symbolicMode` (:5387-5388) | `finishSynth` of `emitLeaves` | entered from R4 (same constant), or directly |
| R7 | non-defn | `| _ => throwError` (:5390) | — | no success | — |

`synthesizeMachineCertified` (:5252-5264) returns `none` exactly in two ways, both AFTER `synthesizeMixedCertified`
(:2959, the whole combinational harness incl. nested child syntheses through `childSynthEntry`) has run:
- **N1** `Sparkle.IR.Machine.closeLets shape.layout.lets t = none` (:5256, :5264; `closeLets`, Sparkle/IR/Machine.lean:179-199: no packed wire,
  no operands, a width/name check or `assignmentOrderCheck` fails);
- **N2** `closeInstsM` / `closeInstsGM` returns `none` (:5260-5262): `sparkleChildSynth.get = none` (:5209/:5232), or
  `Sparkle.IR.Machine.closeInsts` (Machine.lean:396-426) / `closeInstsG` (Sparkle/IR/MachineInstG.lean:115) returns `none`. The
  one-output `closeInsts` requires, among other checks, `kidsCombB` (Machine.lean:371, :425): every child is assignments only.
  *Read from the source; this investigation did not run a corpus to see whether a sequential one-output child occurs.*

Orthogonal entry modes (not extra rows):
- `entryConst` (:5266-5282) hands over the UNFOLDED constant when the original misses both gates and the unfolding passes a gate
  or is a machine shape. R4's legacy tail therefore runs on that unfolded constant, not on the original.
- Symbolic / parametric entry (`synthesizeCombinationalWithParameters`, :8940): machine route and memo are off, the top is R6.
  Its children are `synthesizeChild` runs in the non-symbolic nested configuration (`[] false`).
- `synthesizeChild` (:8929-8934): `childCache` hit returns the cached `Res` (route 8); a miss runs
  `synthesizeCombinational` = `synthesizeCombinationalWith` (post-processed, see §3) and inserts that result.
  All translator child calls go through it (`childSynthEntry` :5620; `synthesizeCombinational` :6332; callers :6586, :6598, :8712, :8730).

### Dispatch decision tree (the same table, as the order the run takes)
```
R1 ? → R2 ? → [machine? = some shape] → R3 (some) | R4 (none: N1 | N2) → memo? → R5 (hit) | R6
                                       [machine? = none]                 → memo? → R5 (hit) | R6
```

## 2. Run telescopes (program order; descriptive, not an evidence predicate — see §5.2)

`E` = prefix common to every row (Elab.lean:5423-5583, `synthesizeCombinationalCoreWith`):
`E1` logProf; `E2` `depth ← sparkleSynthDepth.get`; `E3` throw if `depth ≥ 1024` (:5466, no success);
`E4` read the six saved maps if `depth ≠ 0`; `E5` if `depth = 0` set 11 cells incl. memo and childCache to `{}` (:5536-5548), else set the six
wire/instance caches (:5549-5559); `E6` `sparkleSynthDepth.set (depth+1)` (:5561); `E7` `getConstInfo`, `getEnv`, `entryConst`,
`instancePredicate env`, then `synthesizeFromConst`; `E8` (finally) `depth.modify (·-1)`, restore the six maps if `depth ≠ 0` (:5577-5583).
The real entry then post-processes (`synthesizeCombinationalWith`, :8920 / :5585-5603): `dropZeroWidthModule` on the top,
`mergeChecked` unless `SPARKLE_NO_REGDEDUP` (an `IO.getEnv`).

**R5 (memo hit), at a nested entry** — `E` ; `T1` (R1/R2 guards pure, decline) ; [`getEnv` (:5312) ; `machineShape?` pure — if `some`, R4 telescope below runs first] ;
`T5` `sparkleSubModuleCache.get` (:5335) ; `if some cached` → `logProf "MEMO HIT"` (:5337) ; `pure cached`. No write.

**R6 (legacy), direct** — `E` ; `T1` ; [`getEnv`; `machineShape? = none` ⇒ `pure none`] ; `T5` memo `get` (miss) ; `logProf` ; `match constInfo`,
`.defnInfo` : `openRecordInputs defnInfo.value` (:5345) ; `stripMemoizeWrappers` (pure) ; `lambdaTelescope body (fun xs inner => …)`
(:5359) containing: `splitReturnLeaves inner`, `IO.mkRef {}`, `bindInputsLegacy [] false xs 0 (emitLeaves translate cache logProf leaves none 0)` run
from `entryCompilerState false cache` and `CircuitM.init (ModuleName.ofDecl declName)` (children enter here through the
translator → `synthesizeChild`), `finishSynth` (:5384, defined :2218; name legality check; `addClockResetIfSequential … finalize`), then
`sparkleSubModuleCache.modify (·.insert declName result)` (:5388) ; `pure result`. In `Tools/ShippingLegacySemEntryWalk.lean:133` (`legacy_entry_walk`) this is
`MemoHit ∨ (∃ body0 xs inner leaves cache returned st, … Returns (bindInputsLegacy …) … ∧ m = (addClockResetIfSequential st.module).finalize ∧ legal)`.

**R4 (declined machine, then R5/R6)** — `E` ; `T1` ; `getEnv` ; `machineShape? = some shape` ;
`M1` `synthesizeMixedCertified translate logProf declName shape.binders shape.body` (:2959-2975: `mkFreshFVarId`s, `IO.mkRef`, the translator run on the
body — **nested child syntheses happen here and write `sparkleChildCache` / `sparkleSubModuleCache` / the six caches**) ;
`M2` `closeLets` (pure) — if `none`: **N1**, return `none` ;
`M3` if `shape.insts ≠ []`: `sparkleChildSynth.get`, then one `synth c` per call (`closeInstsM` :5207-5224 / `closeInstsGM` :5229-5247; each `synth c` = `synthesizeChild c`:
`childCache` hit, or a full nested entry `E…` + insert), then pure `closeInsts`/`closeInstsG` — if `none`: **N2**, return `none` ;
then continue at `T5` (memo read; hit ⇒ R5) or the R6 tail. `Tools/ShippingMachineOutcomeA.lean:354` (`synthesizeFromConst_machine_split2A`) states this split: `r = none ∧ RunsTo (legacyTail …) w₂ (m,d) w'`.
**Heap carried into the tail:** everything M1/M3 did to `childCache`, to the memo (for NESTED names only — R4 itself writes no memo entry for `declName`), and to the depth
counter (balanced). The `JQC` side of this is covered by `machineCert_keepsAP` (used at MachineOutcomeA:384); the SEMANTIC side is not.

**R8 (child cache hit)** — `synthesizeChild n`: `sparkleChildCache.get` (:8930) ; `some r` ⇒ `pure r` (no `E`, no memo access, no depth change).
Miss: `synthesizeCombinational n` (= `E` ; one of R1-R6 ; post-processing) ; `sparkleChildCache.modify (·.insert n r)` (:8932). The cached `r` is the
POST-processed result; the memo holds the PRE-processed (`raw`) result of the same run.

## 3. Cache invariants (what exists, what each says, what is not covered)

grep results (names exist at d0ddc50b):
| name | where | says | proved / statement only |
|---|---|---|---|
| `RealChildA O c r` | Tools/ShippingChildCacheA.lean:105 | `r` was returned by a run of `synthesizeCombinational c` from a world with `AdmCtx`, quiet, `sv w = some synthesizeChild` and a cache of real children | inductive; `RealChildA.of_jqc` :160 |
| `CacheInvA O m` | :115 | every entry of a map `m` is a `RealChildA` | `cacheInvA_empty` :127, `cacheInvA_insert` |
| `JQC O D w` | :120 | `JQ` ∧ `CacheInvA (cv w)` — **`cv` is `sparkleChildCache`'s value; the memo is not in it** | `stableA_JQC`, `synthesizeChild_realA`, `closeInstsM_realA` (header) |
| `CacheShips L P Reach m`, `ShipsRes`, `InvAt`, `IHAt`, `BodyKeepsInv`, `ChildKeepsInv` | Tools/ShippingGen2Defs.lean:130-182 | the `sparkleChildCache` entries of REACHED names ship (`ChildShips`) | definitions; keep lemmas in `Tools/ShippingGen2Keep*.lean` |
| `RefLawsM` (`mval`, `memoGet/Set/Modify`, `memoFrame`) | Tools/ShippingMemoLaws.lean:90 | heap laws for `sparkleSubModuleCache` | structure of NAMED runtime laws, not proved |
| `MemoInv L Φ w` | Tools/ShippingMemoInv.lean:44 | every memo entry satisfies `Φ` | `memoInv_of_empty/reset/frame/read/write/hit` PROVED (generic) |
| `stored Ψ`, `Meaning` | :192-199 | an entry has meaning `Ψ` for SOME constant / instance predicate (the key is the name only) | definitions |
| `ArmObligations`, `KeepsMemo`, `MemoSound` | :130-215 | per-arm preservation of `MemoInv (stored Ψ)` | **statements only; the header says "No theorem in the development uses them"** |
| `MemoLaws` (old) | Tools/ShippingLegacySemMemo.lean:65 | superseded sketch | `memo_miss_after_reset` |
| `memo_miss_after_reset` family | `…LegacySemMemoWalk.lean` (`outer_miss` :495) | at the OUTERMOST entry the memo read misses (reset at :5540) | proved from `RefLawsM` |

Facts read from the source that any memo-hit statement must respect:
- **K1 (key).** Both caches are keyed by `declName` only (no parameters, constant, predicate, translator).
- **K2 (value).** `memo[n]` is the `raw` result of the core run (written at :5297/:5304/:5323/:5388, before `synthesizeCombinationalWith`'s `dropZeroWidth`/`mergeChecked`);
  `childCache[n]` is the post-processed result. They are different values of one run.
- **K3 (reset).** Both are reset together, only at depth 0. Nested runs never reset either.
- **K4 (what a nested memo hit would need).** A nested entry is reached through `synthesizeChild n`, which returns from `childCache` first. So a nested run
  reaches `memo.get? n` only if `childCache[n] = none`. A nested hit therefore needs a memo entry `n` that has no `childCache` entry. In this reading the writes that precede
  `synthesizeChild`'s insert are consecutive (:5388 … `finally` … :8932) and the `finally` block restores wire caches only. **This investigation found no execution producing such a
  state at a nested entry; it has NOT been proved**, and it is a statement about all heap-effecting steps in between (including the machine attempt R4), not an observation.
- **K5 (top).** The depth-0 top writes `memo[top]` at the end of its run and no later run reads it before the next reset.

`MemoInv` / `ArmObligations` are INTERFACES (what a supply would have to prove) and none is a supply.

## 4. `LegacyDom` and the legacy contract: types, and the range not yet supplied

Types (Tools/ShippingLegacySemContract.lean):
```lean
def LegacySem (Dom) ctx inputs we mems initial : Prop          -- :155  STATED ONLY
def ReachesInline tenv rec ctx e : Prop                       -- :182  premise
def ReachesUnfold tenv rec ctx e : Prop                       -- :183  premise (weaker)
inductive LegacyDom tenv ctx inputs : Lean.Expr → Value → Prop -- :264
  | input  : inputs id = some v → LegacyDom (.fvar id) v
  | cert   : (t : Term s) → t.WF kb kv vw → Meaning … → LegacyDom … leaves → LegacyDom (quote dom bE vE t) (pack s (eval …))
  | inline : NotCore e → (∀ rec, ReachesUnfold tenv rec ctx e) → (∀ e', InlineUnfolds e e' → LegacyDom e' v) → LegacyDom e v
theorem legacy_translate_contract : LegacyDom tenv ctx inputs e v → Contract (translateExprToWire tenv) ctx inputs we mems initial e v   -- :327
```
Output statement (Tools/ShippingLegacySemEntryWalk.lean:273 `legacy_entry_output_walked`; value in `ShippingMixedEntrySoundness.lean:538 RawValueAt`):
for a legacy DECLARATION, a successful run is `MemoHit ∨ (∃ ids cache, … ∀ bools bits initial mems, Admissible … → ∀ v, LegacyDom … (leafOf ids) v → RawValueAt v.kind.width bs m initial mems v.toNat)`.

**What it covers** (as typed): a module `m` with output `"out"` computed by `evalAssigns` (combinational assigns) equal to a scalar `Value` (`bool` / `bits n`, Tools/ShippingUnifiedMeaning.lean:21),
for ONE leaf `("out", leafOf ids)`, **provided the premise `LegacyDom … (leafOf ids) v` holds**.

**What is not supplied** (no supplier of these found in this investigation; each is a premise or absent):
- U1 `LegacyDom` membership of the real leaf: it is a hypothesis `dom` of `legacy_entry_output_walked`. The only constructions in the repo are in `Tests/Compiler/LegacySemInstanceTest.lean`
  (`useDbl`, `dbl_unfold_dom`, `add2_unfold_dom`) — concrete declarations, not a ∀-declaration derivation.
- U2 `inline`'s `∀ rec, ReachesUnfold`: about runs of the fallback (`NoSubModule`, "the unfolding oracle returned an unfolding and translating it did not throw", `…LegacySemInstance.lean:30-34`).
- U3 `htele : TelescopeSpec` / `EntryFacts` (`BinderWalk`, single leaf `("out", …)`): the header of `…EntryWalk.lean:55-77` says these are not walked and the binder walk "cannot be stated" with the present `Returns`.
- U4 expression forms: `LegacyDom` has constructors only for `input`, the certified quoted fragment and unfolding. Instances (`.inst`), registers/`Signal.register`, `memory`, loops, multi-output,
  projections of multi-output children — the forms that make a module sequential or hierarchical (`addClockResetIfSequential`, :2233) — have no constructor and `Value` is scalar.
- U5 module-level interface: no theorem turns the above into `ChildRunN`/`CombChildRunN`/`SeqChildRunN` (`Tools/ShippingGen2Defs.lean` / GEN2_DEFS `ChildRunN`) or `TopShips`; no package.
- U6 the `MemoHit` disjunct of `legacy_entry_walk`: removed only at the outermost entry (`outer_miss`); a nested legacy run still returns `MemoHit` as an alternative (K4).
- U7 the `rec`-hypothesis side: `LegacySem` is "STATED, NOT PROVED"; the cached shim `Rec.translateExprToWireCached` is outside the contract (its hit is unvalidated, header :80-87).
- U8 premises `old`, `mixed`, `hmach` (reflection of the three gates' declining) — exactly the R4 case is where `hmach` is FALSE (a machine shape exists), so `legacy_entry_walk` as stated does not describe R4's tail.
  `legacyTail` for R4 is a different premise set (`synthesizeFromConst_machine_split2A`, where the machine attempt precedes it).

## 5. Interface types and statement shapes (types; NOT yet in Lean)

All new names, new file, additive. Nothing here edits `Pkg`, `ChildShips`, `TopShips`, `T1Hyp`, `Laws`, `Start` or any shared file.

### 5.1 Common interface: provided by the gate Issue (rev3: no fallback definition)
rev2's `IfaceData`/`Pkg.iface`/`ChildShipsD`/`childShips_iff` are replaced by the gate's `ChildIface`/`ChildIface.ofPkg`/`ChildShipsI`/`childShipsI_ofPkg` (table in §0). This Issue adds nothing here; fallback statements that need an interface use `ChildShipsI (ChildIface.ofPkg q)`.
Dependency: gate U-G1 must be built first. If the built U-G1 differs from gate freeze §3.0 (3aab70fc), the table of §0 is re-checked field by field and re-frozen before use.

### 5.2 `LegacyTailRunExists` (renamed from `TookLegacyTail`) — an EXISTENCE predicate
Pattern of `MachineRunJQC` (ShippingServedRealA.lean:90-95). `legacyTail` is the verbatim copy of the memo-read + legacy arm of `synthesizeFromConst` (ShippingMachineOutcomeA.lean:54; `TranslateFn` is its translator type).
```lean
def LegacyTailRunExists {mref cref} (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (mctx : Meta.Context) (cctx : Core.Context) (n : Nat) (c : Name)
    (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (w9 w10 : Void IO.RealWorld),
    RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) c [] false ci) mctx mref cctx cref w9 (raw, D) w10 ∧ JQC O n w9
```
What it is, and the restriction that is fixed:
- It says: some environment `tenv`, constant `ci` and worlds `w9 w10` admit a run of `legacyTail` that returns `(raw, D)`, with `JQC` at `w9`. It is an existence statement about a tail run. **It is not evidence that THIS core run took the tail**: `w9`/`w10`/`ci`/`tenv` are existential and not linked to the start/end worlds of any `synthesizeCombinationalCore` run.
- It covers the whole tail (memo read and legacy build, R5 and R6 of §1); separating them needs `mval` (§5.6).
- Connecting it to a core run (same worlds, same `ci` from `entryConst`) is a **separate, later lemma/type**, not defined in rev3: for R4, `synthesizeFromConst_machine_split2A` (OutcomeA:354, case `r = none`) gives `JQC O n w₂` and the tail run for the same run; for R6 direct (`machineShape? = none`) no analogous theorem exists (`legacy_entry_walk`, EntryWalk:133, has the `hmach` premise, U8). A later statement that wants run evidence will either use that split's decomposition or add a type that ties the same core run; this is OPEN.
- If only the existence predicate is extracted (the case in rev3), nothing is claimed about which route a given run took.

### 5.3 Requirements for a later R4-local producer statement (NOT a type; not in unit 1)
rev2's `LegacyChildShips` is removed from this freeze as a Lean type (R1). A later unit may state an R4-local producer; before that, its freeze must give a **complete type** satisfying all of the following. Listed as requirements, not as a definition:
1. It is R4-local: hypotheses say that `machineShape? = some shape` for the *current* `c` (after the environment/`entryConst` handling), that `synthesizeMachineCertified` returned `none` for it (N1 or N2), and the run is the nested one of §5.4. The whole `T1Hyp` is **not** added (`T1Hyp.closes` excludes R4; adding it would exclude the case).
2. The current-`c` package is a **hypothesis of the statement itself**: `P c = some q`, `q.decl = c`, and the tie from `q` to the declaration actually run (`q.d.shape` equals the shape `machineShape?` returned for `c`; the source `q.src` is the one the module is to implement). `InvAt`/`IHAt`/`ChildKeepsInv` constrain cache entries and deeper runs and are not a source of this package.
3. The conclusion is of the form `ChildShipsI (ChildIface.ofPkg q) n b D` (gate names), with `b` the post-processed result (§5.5); `ChildRunN` inside is the producer's obligation, never a premise.
4. Run evidence for the tail (R2): either the decomposition of the same core run (`synthesizeFromConst_machine_split2A`) or a type tying the worlds; `LegacyTailRunExists` alone is not enough.
5. R6-direct (`machineShape? = none`) has no `Pkg` under the current `T1Hyp`; it needs a source interface (D-IFACE, §7) and is not covered.
Whether a producer meeting 1-4 is provable is OPEN: this investigation found no supplier of the legacy contract (§4, §6).

### 5.4 Two start conditions (R3)
| | outer root | recursive (nested) producer |
|---|---|---|
| world | `Start L mctx cctx w` = `AdmCtx ∧ JQC L.O 0 w`; depth 0; `sparkleChildCache`/memo empty after E5 | `InvAt L P Reach (dv w) w`, `dv w` arbitrary < limit; `sparkleChildCache` holds earlier `ShipsRes`; memo may be non-empty |
| extra hypotheses | none beyond `T1Hyp` | `IHAt (dv w + 1)`, `ChildKeepsInv (dv w + 1)` (Gen2Defs.lean:255-259 pattern) |
| conclusion | top: `∃ q n, P c = some q ∧ TopShips q n c b raw D` (T1Stmt's form) | child: `ChildShips`/`ChildShipsI` for the post-processed `b` |
| covers fallback / legacy / memo of a child? | no — a child run is not at depth 0 | yes |
A statement of §5.3 would be the recursive form. The outer-root form (`LegacyTopShips`, conclusion `TopShips q n c b raw D` with `Start`) is not typed in rev2: `TopShips` reads machine fields (`p.d.ss`, `p.extS`, `p.src`, `p.kD`) whose meaning for a legacy module's registers/slots is part of D-IFACE.
A nested R5/R6 under a parent is therefore never covered by a `Start`-based statement. Neither is the converse.

### 5.5 Raw memo vs post-processed child (R3)
- `memo[n]` = `raw` core result (K2); `childCache[n]` = post-processed (`dropZeroWidthModule`, `mergeChecked` unless `SPARKLE_NO_REGDEDUP`).
- A child `c` reached through `synthesizeChild` yields the post-processed result to the parent; `ShipsRes` (`IHAt`) is about it. A nested run that returns a memoised `raw` therefore returns through `synthesizeCombinationalWith`'s post-processing again, and `b` is that post-processed form.
- Hence a memo-side invariant is of the form `MemoInv M (fun n r => Reach n → ∀ b, PP r.1 b → ∃ q n', P n = some q ∧ q.decl = n ∧ ChildShipsI (ChildIface.ofPkg q) n' b r.2)` with `PP raw b := b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)`. This is a **shape**, not a definition of rev2 (needs `M`, §5.6).
- The transport lemma "ChildShips of `raw` ⇒ of `PP raw`" (the post-processing steps preserve `ChildRunN`) is an obligation of the producer too (it is G-TRANSPORT/G-LIFT territory of Gen2Defs); not proved, not assumed.

### 5.6 Memo side: separated and undesigned
Not typed in rev2: a memo law bundle for the `Laws` of Gen2Defs (`Laws` has `O`, `T`; `mval` is in `RefLawsM`, which `extends RefLaws`, while `O : RefLawsAOps`; whether one world interpretation can satisfy both by transport of existing laws, or only by a new assumption, is not established),
`MemoInvShips`, `MemoHitShips`, the K4 invariant `memo-names ⊆ childCache-names ∪ {top}`. Whether such a bundle/mapping is only a re-packaging or conditional transport of existing laws (design work) or adopts a new real-environment guarantee (the only case needing a user decision) is OPEN (§0 R3, §7 D-MEMO-LAW). K4 remains a reading of the source, **not proved**. Until this part is designed, the memo-hit case of `LegacyTailRunExists` (§5.2) is uncovered by any conclusion.

### 5.7 First implementation unit (applies after rev3 is approved; the definition does not wait for gate U-G1)
Sync (after approval of 6eb58bf2): `LegacyTailRunExists` does not reference `ChildIface` and needs no import of the gate's file, so the dependence on gate U-G1 being built is **not technical** for this definition. Only a later adapter that actually uses `ChildIface` must match the gate's built SHA. This definition is an intermediate definition, not a supply result.
Contents (small, definitions only): the `LegacyTailRunExists` definition of §5.2, in a new file of this Issue (e.g. `Tools/ShippingGen4FbTail.lean` + `lean_lib` entry in lakefile.lean; imports `Tools.ShippingGen2Defs`, `Tools.ShippingMachineOutcomeA`), and a check file that records its type and `#print axioms`, plus signature-level mutants (e.g. dropping `JQC O n w9`; replacing `legacyTail … ci` by another term) rejected by signature/defeq — **not** semantic counterexamples.
It contains: no interface record (gate U-G1), no `LegacyChildShips`, no memo definition, no claim about a run. The §0 table is relevant only to later adapters, not to this unit.
No sorry/axiom/native_decide. Not started. It claims no supply of any legacy or memo condition.

## 6. Supply paths for the unsupplied legacy contract / memo conditions, and where each stops

Rule applied: turning an unsupplied legacy contract or memo condition into a new named hypothesis does NOT complete this issue. Each candidate below is a way to SUPPLY it, with the point where this investigation stops.

**L-1 Derive `LegacyDom` membership from the declaration (U1).** Path: a ∀-declaration producer by induction on the expression, using the existing certified-fragment reader (`readTerm_sound`, `readTerm_quote`, M5 DG-READKINDS) for the `cert` constructor
and `plain_call_reaches` (Tools/ShippingLegacySemInstance.lean:51) for `inline`.
 Stops at: U2 (`ReachesUnfold` is a fact about runs: `NoSubModule`), U3 (telescope/binder walk), and U4 (no constructor for instances / registers / memories / multi-output). Beyond the scalar combinational fragment the `Value` / `Contract` types have nothing to state.
**L-2 Extend `Contract`/`Value`/`LegacyDom` to sequential and hierarchical legacy bodies (U4, U5).** Path: new arms (`.inst`, `register`) with a trace-level semantics, feeding `SeqChildRunN`.
 Stops at: this changes `Value`/`Contract` (shared, `Tools/ShippingUnifiedMeaning.lean`, `ShippingUnifiedRecursion.lean`) — a new semantic definition. It is a user-approval item (new law / shared definition), not started.
**L-3 Show R4 never happens on successes (turn the fallback into an excluded case).** Path: derive `MachineClosesAtA` from data (`closes_of_data`, `closes_of_data_calls`, `machineCloses_of_noLets`) as T1Hyp.closes' docs already suggest.
 Stops at: `closes_of_data_calls` leaves `CallsClose` UNDERIVED (MachineClosesData:249 doc: "`CallsClose` is NOT derived"), and N2 includes `kidsCombB` on children — a property of the child's synthesized module, i.e. of a different route's output. And the DG-FALLBACK text (DGEN_FREEZE §5 D2) says that excluding fallback by a compiler guard is a compiler change under the output policy, "not started without a user decision".
 Also: `closes` as a **premise** (T1Hyp.closes) is the current state; making it a premise for a **larger** class of declarations is a scope statement, not a supply.
**L-4 Route R4's tail through the existing `legacy_entry_walk`.** Path: use `synthesizeFromConst_machine_split2A` (r = none ⇒ `legacyTail`) and `legacy_entry_output_walked`.
 Stops at: U8 — `hmach` is false in R4; the walk has to be redone with the machine attempt in front (heap state after M1/M3) and for the UNFOLDED `entryConst` constant. No theorem for this combination was found.
**M-1 Memo invariant, nested hit (K4).** Path: prove an invariant `memo-names ⊆ childCache-names ∪ {depth-0 top}` (new, over `RefLawsM` + `RefLawsAOps` jointly) by the same frame/step lemmas as `MemoInv`; then a nested R5 is unreachable (the `childCache` read hits first) and `MemoHit` can be dropped from nested `legacy_entry_walk`.
 Stops at: a joint law structure for BOTH caches (`RefLawsM` extends `RefLaws`, `RefLawsAOps` is a different bundle: `Laws mref cref` of Gen2Defs uses `O : RefLawsAOps`) — whether they can be combined without a new law is not established; and `KeepsMemo` for every arm (the 6 `ArmObligations` are statements only).
 If instead nested hits DO occur (K4 false), the memo returns the K2 raw value for a name whose `childCache` entry is absent, and `MemoHit ⇒ ShipsRes` needs the writer's `ShipsRes` carried as a `MemoInv` of the §5.5 shape (needs the undesigned memo law, §5.6). That carries a stored meaning for "SOME constant" (`stored Ψ`, K1), not for the reader's constant (docs/parallel/B-memo.md §5 per the MemoInv header).
**M-2 Memo at the top.** Path: `outer_miss` (proved from `RefLawsM`). No further obligation at the top; the top is never a hit.

**Summary of where the chain stops.** For the R6/R4-tail successes this investigation found NO path that supplies, from the declaration and the run, a `ChildRunN`/`TopShips`-level statement; the contract that exists is the scalar-combinational `RawValueAt`
under a hypothesised `LegacyDom`. Paths L-2 (and any D-IFACE option that changes shared semantic definitions) need a user decision. For R5, M-1 is a plausible but unproved invariant; no supplier was found.

## 7. Decision points surfaced by this freeze (user's, NOT decided here)

- **D-IFACE.** The common interface for non-machine tops (`TopShipsD`/`SemPkg`) — new definition(s); allowed only as new files, but the FG statement's meaning for non-machine tops is part of the guarantee.
- **D-LEGACY-SCOPE.** If L-1/L-2 cannot be completed, FG holds for legacy successes only with an explicit legacy contract (GENERAL_SPEC M4 risk, :485). Guarantee impact: declarations whose compilation falls to the legacy tail (R6, or R4 with `closeLets`/`closeInsts` = none)
  would be outside the proved guarantee, or covered by a stated contract. Accepting that is a user decision; scope reduction is not made here.
- **D-GUARD.** Rejecting R4 at compile time (a compiler guard making machine declines an error) is a compiler change under the output policy; not proposed for approval here.

- **D-MEMO-LAW (conditional).** A memo law bundle usable with `Laws` (§5.6): if it is a re-packaging or conditional transport of existing laws, no user decision; if it adopts a new real-environment guarantee as an assumption, that part is the user's decision. Which holds is undesigned/OPEN. Memo-hit coverage waits for the design.

If this freeze is approved, the first Lean unit is §5.7 (new file; one existence-predicate definition; no supply; not blocked by gate U-G1). The memo side (§5.6), L1-L4 and M-1 remain read-only research until their own design is frozen.

## 8. What is NOT claimed
- No statement that a fallback, legacy or memo-hit success is impossible, non-derivable or unreachable. K4 is a reading of the source, not a theorem.
- No result about the corpus (which declarations fall back); N2/`kidsCombB` is read from code, not measured.
- No change to FG, `T1Hyp`, `GenWF`, TRUSTED boundaries or any law. `T1Hyp.closes` is described, not edited.
- Nothing here is conditional-on-new-hypothesis presented as done; §6 lists where each path stops.
- rev3 does not claim that an R4-local producer is provable, that R6-direct is coverable, or that any memo statement holds; K4 is unproved; `LegacyTailRunExists` is an existence predicate and is not evidence about a given run; no Lean was written or built.

---

## 9. Producer research (rev3 addendum): same-core-run tail decomposition and source tie — complete type and supplier survey

- **Status (synced):** research plus frozen types. §9.2's `R4Run`/`A4MachineSideA`/extraction lemma are implemented as FB-2 (built, approved; a repackaging of A4's witness). `R4TailStmt`, the producers and every obligation in §9.3 are NOT supplied; the memo obligation (T-MEMO/K4) is an obligation of R4 as a whole and is kept. Nothing in §9.1-§9.8 is a supply of T-INV. Origin: it is the "main work" asked for after the rev3 approval (target SHA of the approval: 6eb58bf2). It is not a re-freeze of §0-§8; it adds a section. Whatever it proposes as a Lean type needs its own review before implementation.
- **rev4 (review of 79e6d672, R1-R3):** §9.2 is rewritten with the exact A''' conclusion, a complete `R4Run`, the extraction lemma and `R4TailStmt` for R4 as a whole (memo obligation kept); §9.6 limits only the first unit; §9.7 adds T-INV research; build evidence is a reference (§9.6). Docs only.
- **rev5 (review of 658d2b8d):** §9.2.1-§9.2.3 now carry the complete types: `R4Run` over `O` (no `⟨O,T,…⟩`), the (a) side as the separate definition `A4MachineSideA` in the new namespace `Tools.ShippingGen4FbR4` (not `Gen2.MachineTaken`), ambient `open`s stated, `mctx/mref/cctx/cref` of `StartReadsN`/`FinallyRestores` fixed to the original run; §9.5 replaced (independent Expected; the extraction is a theorem, not called defeq); §9.7 extended (T-INV). `R4TailStmt` is a target schema; no producer is supplied. The general semantic guarantee for R4 is NOT supplied by this document or by unit 1.
- **Scope:** the R4 tail only (§1: `machineShape? = some shape`, `synthesizeMachineCertified = none`, then memo/legacy), for a NESTED run (§5.4 right column). R6-direct is not in this section; the memo-hit side and K4 are not covered by any producer here but remain obligations of R4 as a whole (§9.2, §9.6).
- **Wording rule:** "no supplier found" below means: the files named in the "Sources read" line and those cited here were read and no supplier of the item was found. It does not mean the item is impossible or underivable.

### 9.1 What already ties the tail to THE core run (found)
`core_machine_outcomeA'''` (Tools/ShippingMachineOutcomeA4.lean:224; built per its header, `mo4b`) states, for one successful run `RunsTo (synthesizeCombinationalCore declName [] false) … w (m,d) w'` with `MachineDefines … declName shape`, `hw : JQ O.quiet D w`, `hc : D = 0 ∨ CacheInvA O (cv w)`, premises `O`, `hA : AdmCtx`, `T : RefLawsATele O.quiet mref cref`:
`∃ tenv b ci envR' w₁ … w₆ r`, linked reads (`getConstInfo` `w₁→w₂`; `getEnv` `w₂→w₃`; `JQC O (D+1) w₃`; second `getEnv` `w₃→w₄`; `machineShape? … (entryConst true false [] ci …) (structEnv envR') = some shape`), the machine attempt `w₄ →(r) w₆` with `JQC O (D+1)` at `w₄`, `w₆`, the entry's `finally` (`coreFinally`, `FinallyRestores`, `StartReadsN`) from the body end `w₅` to the core's `w'` with `JQC O D w'`, and the disjunction
(a) `r = some res ∧ res = (m,d)` plus the profile log and memo insert `w₆ → w₅`; or
(b) `r = none ∧ RunsTo (legacyTail … declName [] false (entryConst true false [] ci …)) w₆ (m,d) w₅ ∧ ∃ t d₀ w₇, RunsTo (synthesizeMixedCertified … shape.binders shape.body) w₄ (t,d₀) w₇ ∧ JQC O (D+1) w₇ ∧ (closeLets = none ∧ w₆ = w₇  ∨  closeLets = some t' ∧ shape.insts ≠ [] ∧ (closeInstsM / closeInstsGM run w₇ → w₆ returning none))`.
Facts that matter for the producer:
- Worlds ARE linked in (b): the tail starts at the machine attempt's end `w₆` and ends at the body end `w₅`, both inside the core run `w → w'`. This is the "same core run" decomposition that `LegacyTailRunExists` (§5.2) lacks; `core_machine_outcomeA'''` supplies it for R4 given its premises. (Its (b) disjunct is not a proof that (b) occurs.)
- The tail runs on `entryConst true false [] ci …`, the UNFOLDED constant, not on `declName`'s own `ci`. The shape `shape` is that of the same unfolded constant (the `machineShape?` conjunct). So the tie "shape = the constant the tail runs on" is part of the theorem; the tie "that constant = the source of the package" is not (§9.3, T-SRC).
- Its extra premise `T : RefLawsATele` is `Laws.T` (Gen2Defs.lean:46-48), an existing field of `Laws`; the premise `D = 0 ∨ CacheInvA O (cv w)` and `JQ O.quiet D w` follow from `InvAt` (`InvAt L P Reach D w = JQC L.O D w ∧ …`). No new law.
- Conclusion shape is a PRE-`finally` statement about `w₅`; the post-processing (`dropZeroWidthModule`, `mergeChecked`) is outside the core run (§5.5) and is not in this theorem.

### 9.2 Complete type of the R4 producer (rev4; text for review; NOT Lean, NOT implemented)
Names are proposals. Interface names are the gate's (`ChildIface`, `ChildShipsI`, §0), used only in text. `Laws`, `Pkgs`, `Pkg`, `InvAt`, `IHAt`, `ChildKeepsInv`, `dv` as in Tools/ShippingGen2Defs.lean:141-177; `AdmCtx` Tools/ShippingChildInvA.lean:77; `MachineDefines` Tools/ShippingMachineEntry.lean:2345; `JQC := JQ ∧ CacheInvA` Tools/ShippingChildCacheA.lean:120; `StartReadsN`/`FinallyRestores` Tools/ShippingMachineOutcomeA4.lean:53/79. `L.O`, `L.T` are the existing `Laws` fields (`T : RefLawsATele O.quiet mref cref`, Gen2Defs.lean:46-48).

**9.2.0 The existing conclusion, quoted.** `core_machine_outcomeA'''` (Tools/ShippingMachineOutcomeA4.lean:224-273; statement) — premises `O : RefLawsAOps MkRefd mref cref`, `hA : AdmCtx O.quiet mctx cctx`, `T : RefLawsATele O.quiet mref cref`, `{declName shape D w w' m d}`, `hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w'`, `entry : MachineDefines mctx mref cctx cref declName shape`, `hw : JQ O.quiet D w`, `hc : D = 0 ∨ CacheInvA O (cv w)`. Conclusion: `∃ tenv b ci envR' w₁ w₂ w₃ w₄ w₅ w₆ r` with, in order (line):
1. `RunsTo (getConstInfo declName) … w₁ ci w₂` (:233)
2. `RunsTo (Lean.getEnv : MetaM Environment) … w₂ tenv w₃` (:234)
3. `JQC O (D + 1) w₃` (:235)
4. `RunsTo (Lean.getEnv : MetaM Environment) … w₃ envR' w₄` (:236)
5. `machineShape? false [] (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape` (:237-238)
6. `RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape) … w₄ r w₆` (:239-241)
7. `JQC O (D + 1) w₄ ∧ JQC O (D + 1) w₆` (:241)
8. `∃ sf sw sl sp sc ss sg, RunsTo (coreFinally D sf sw sl sp sc ss sg) … w₅ () w' ∧ FinallyRestores D sf … sg w₅ w' ∧ (D = 0 → sf = {} ∧ … ∧ sg = {}) ∧ (D ≠ 0 → StartReadsN declName b D w sf … sg)` (:242-248)
9. `JQC O D w'` (:248)
10. the disjunction (:249-273): (a) `∃ res, r = some res ∧ res = (m, d) ∧ ∃ wl, RunsTo (profLogIO b "[profile] synthesizeCombinational … machine certified front end") … w₆ () wl ∧ RunsTo (sparkleSubModuleCache.modify (·.insert declName res)) … wl () w₅`; or (b) `r = none ∧ RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName [] false (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv) (structEnv tenv))) … w₆ (m, d) w₅ ∧ ∃ t d₀ w₇, RunsTo (synthesizeMixedCertified (…same translate…) (profLogIO b) declName shape.binders shape.body) … w₄ (t, d₀) w₇ ∧ JQC O (D + 1) w₇ ∧ ((closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨ (∃ t', closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧ ((shape.instFields.isEmpty = true ∧ RunsTo (closeInstsM shape t (closeMachine shape.layout t') d₀) … w₇ none w₆) ∨ (shape.instFields.isEmpty = false ∧ RunsTo (closeInstsGM shape t (closeMachine shape.layout t') d₀) … w₇ none w₆))))`.

Here `t'` is quantified INSIDE the second disjunct of the closeLets case (`closeLets … = some t'`), not at the top; `t, d₀, w₇` are inside (b); `r` is `none` in (b).

**9.2.1 What links which worlds (witness vs. run chain).** The explicit run chain in the conclusion is: `w₁ →(getConstInfo) w₂ →(getEnv) w₃ →(getEnv) w₄ →(machine attempt) w₆ →(legacyTail) w₅ →(coreFinally) w'`, and inside (b) the side run `w₄ → w₇ [→ w₆ via closeInsts]`. **The conclusion does not contain a run from the core's start `w` to `w₁`.** `w₁` is the world that the theorem itself obtains from the same `hr` (internally via `core_reads_link4A`, defined :116, used :275); the statement only guarantees that this `w₁` exists. The relation of `w` to `w₁` in the conclusion is limited to item 8's `StartReadsN … w` (for `D ≠ 0`, the entry's initial reads run FROM `w`, returning the saved maps) and `JQC O (D+1) w₃`; nothing states `w₁` is reachable from `w` by an explicit run, nor that the heap between them is related except through those facts. A producer must therefore treat `w₁` as "the world the theorem returned for this `hr`", not as a world it can chain to from `w`; any need to connect `w`'s `InvAt` to `w₄`'s (T-INV) is an additional obligation (§9.3, §9.7), not a consequence of the conclusion.

**9.2.2 Definitions `R4Run` and `A4MachineSideA` and the extraction lemma (rev5: complete text; this is the exact text to be put into `Tools/ShippingGen4FbR4.lean`).**
File header: `import Tools.ShippingMachineOutcomeA4`, `set_option autoImplicit false`. Namespace `Tools.ShippingGen4FbR4` (new, separate from `Tools.ShippingGen2`). Ambient `open`s are exactly those of Tools/ShippingMachineOutcomeA4.lean:35-52 plus `Tools.ShippingMachineOutcomeA4` itself (`Lean Meta`, `Tools.ShippingEntrySoundness`, `Tools.ShippingMachineEntry`, `Sparkle.Compiler.Elab`, `Sparkle.IR.Builder`, `Tools.ShippingChildInv`, `…BndInit`, `…Fresh`, `…TranslateA`, `…BndCore`, `…InvA`, `…VCA`, `…CacheA`, `…DepthC`, `…FrontCP`, `…RunA`, `…RunAMain`, `…ComposeC`, `Tools.ShippingMachineOutcomeA`, `…A3`, `…A4`). There is NO `variable` line: `mctx mref cctx cref` are binders of each declaration, so the `StartReadsN`/`FinallyRestores` calls name them explicitly, as A4 does (`(mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)`). `Module`/`Design` are written `Sparkle.IR.AST.Module`/`Design` as in A4.
* `R4Run` takes the ops law `O : RefLawsAOps MkRefd mref cref` (not `Laws`; the `⟨O,T,…⟩` of rev4 is removed; `T` is only a premise of the lemma, as in A4).
* `A4MachineSideA` is the (a)-side prefix. It is a NEW definition in a NEW namespace and is NOT `Tools.ShippingGen2.MachineTaken` (Gen2Defs.lean:130, an `abbrev` over `Laws` with no world arguments, used by the M2/M3 units). The name avoids that clash; rev4's use of the name `MachineTaken` for it is withdrawn.
* In the (a) side `(m, d)` is substituted for `res` (A4 has `r = some res ∧ res = (m,d)`); the extraction does that by `rfl`.
```lean
namespace Tools.ShippingGen4FbR4
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4

/-- (b) side of `core_machine_outcomeA'''`: prefix items 1-9 with `r = none`, the `legacyTail` run `w₆ → w₅`, and the
harness/closing data. `t'` is inside the second `closeLets` disjunct. -/
def R4Run {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC O (D + 1) w₄ ∧ JQC O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- (a) side of `core_machine_outcomeA'''` (NOT `Gen2.MachineTaken`): the same prefix 1-9 with `r = some (m, d)`,
and the profile-log and memo-insert runs `w₆ → wl → w₅`. -/
def A4MachineSideA {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
    JQC O (D + 1) w₄ ∧ JQC O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC O D w' ∧
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

/-- The none-side extraction: `core_machine_outcomeA'''` with its item-10 disjunction split. No new law/premise. -/
theorem a4_machine_or_R4Run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    A4MachineSideA O mctx cctx D declName shape m d w w' ∨ R4Run O mctx cctx D declName shape m d w w' := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, r, h1, h2, h3, h4, h5, h6, h7a, h7b, h8, h9, h10⟩ :=
    core_machine_outcomeA''' O hA T hr entry hw hc
  rcases h10 with ⟨res, rfl, rfl, wl, hl, hm⟩ | ⟨rfl, htail, t, d₀, w₇, hh, hj, hcase⟩
  · exact Or.inl ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h1, h2, h3, h4, h5, h6, h7a, h7b, h8, h9, wl, hl, hm⟩
  · exact Or.inr ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h1, h2, h3, h4, h5, h6, h7a, h7b, h8, h9,
      htail, t, d₀, w₇, hh, hj, hcase⟩

end Tools.ShippingGen4FbR4
```
The proof of the lemma is `core_machine_outcomeA'''` followed by an `rcases` on item 10 and re-packaging the same witnesses (items 1-9 pass through unchanged). It is not `Iff.rfl`/defeq: the original has `r` existential and a disjunction; the lemma has two definitions with `r` instantiated (`some (m,d)` / `none`). Its premises are exactly those of A4: no new law, no new hypothesis. If the build requires a non-semantic text change, this section is synchronised in the NOT BUILT/BUILT header commit.

**9.2.3 (rev5) Run context fixed to the original.** In `R4Run`/`A4MachineSideA` every `RunsTo`, `StartReadsN` and `FinallyRestores` is at the `mctx mref cctx cref` of the declaration, i.e. the same four as the lemma's `hr` (`synthesizeCombinationalCore declName [] false` from `w` to `w'`); `StartReadsN … D w …` starts from that same `w`, and `FinallyRestores … w₅ w'` ends at that same `w'`. Both are therefore tied to the original A4 run, not to an arbitrary run context.

**9.2.4 `R4TailStmt` (R4 as a whole; target statement).**
```lean
def R4TailStmt (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat) (w w' : Void IO.RealWorld)
    (raw : Module) (dsg : Design) (out : Module),
    Reach q.decl → P q.decl = some q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach D w → IHAt L P Reach (D + 1) → ChildKeepsInv L P Reach (D + 1) →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref w (raw, dsg) w' →
    (out = dropZeroWidthModule raw ∨ out = mergeChecked (dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref q.decl q.d.shape →
    (R4Run L.O mctx cctx D q.decl q.d.shape raw dsg w w') →
    ∃ n, ChildShipsI (ChildIface.ofPkg q) n out dsg
```
- `D` is the depth of `InvAt` (= the `D` of A'''). The A''' premises come from the statement: `hw := h.1.1` and `hc := Or.inr h.1.2` from `InvAt L P Reach D w = JQC L.O D w ∧ CacheShips …` with `JQC = JQ ∧ CacheInvA` (ShippingChildCacheA.lean:120); `T := L.T`. (Earlier text used `dv w` for the depth; `InvAt`'s `D` is used instead so that no `dv w = D` fact is assumed.)
- **R2 / scope.** The `R4Run` hypothesis is the whole (b) side of A''' including the `legacyTail` run, whose head contains the memo read (so memo hit and memo miss are both inside it; §3, §5.6). The conclusion `∃ n, ChildShipsI …` is therefore the target for R4 AS A WHOLE, memo hit included. Nothing in this revision narrows it: the memo obligation (T-MEMO, below) stays an obligation of `R4TailStmt`, and K4 is not discharged by anything here. The ONLY scoping is of the first implementation unit (§9.6), not of the statement.
- `T1Hyp` is not a premise (its `closes` excludes R4). `P q.decl = some q`, `Reach q.decl`, `MachineDefines` are hypotheses of the statement and not derived from `InvAt`/`IHAt`. The package-source tie (T-SRC) and the legacy meaning (T-LEG) are not premises either; they are the obligations the producer has to meet and are unsupplied (§9.3). `DataOk q` is open (whether the legacy output satisfies the rows it asserts), as is whether `n` is `∃` or given and the post-processing relation (carried over from rev3 §9.2 / §5.5 unchanged; not re-verified here).
- **Status (rev5):** `R4TailStmt` is a TARGET SCHEMA (the shape a future R4 producer would prove). No producer for it is supplied; nothing in unit 1 proves any part of its conclusion.
- The proof of `R4TailStmt` is NOT proposed here; nothing in this section proves it or any part of its conclusion.

### 9.3 Obligations the producer must discharge, and the supplier survey
Each row: the obligation, the closest existing item, and what this investigation did NOT find. "found" = an existing proved item supplies it as typed.

| id | obligation (what the conclusion needs) | closest existing item | result |
|---|---|---|---|
| T-RUN | the tail ran in THIS core run, from the machine attempt's end world | `core_machine_outcomeA'''` (OutcomeA4:224) | **found** (needs `T`, `MachineDefines`, `JQ`, `hc`) |
| T-HARN | what the machine attempt left in the heap: the harness `synthesizeMixedCertified` run `w₄ → w₇` and the closing run `w₇ → w₆` | A''' (b) gives the runs and `JQC (D+1)` at `w₇`, `w₆` | runs **found**; their effect on `InvAt` (the `CacheShips` half at `w₆`) — see T-INV |
| T-INV | `InvAt (dv w + 1)` at `w₆` (the tail's start): every `childCache` entry of a reached name ships | `KeepBodyStmt` / `keepBody` (Tools/ShippingGen2Keep.lean:54, PROVED): `synthesizeFromConst` body keeps `InvAt` on every outcome; `legacyTailA_generic` (ChildLegacyTailA:194): the tail keeps any `StableA` invariant given `RecA O I translate` | no supplier found for `InvAt` at the INTERMEDIATE world `w₆` as typed: `keepBody` is about the whole body, A''' gives only `JQC` there. A candidate path through the generic `machineCert_keepsAP` at `I = InvAt` exists with three unverified gaps (§9.7); not a supply |
| T-SRC | the entry constant's body (the unfolded `entryConst`) is the declaration whose Lean source `q.src` defines `q.S` | `MachineDefines` / `T1Hyp.defines` (shape of the entry constant); `Pkg.body_eq`/`Pkg.ok` (Pkg.lean) | the shape-level tie is **found**; a tie from the *legacy module's meaning* to `q.S` — none found (see T-LEG) |
| T-LEG | the legacy module `m` = `finalize (addClockResetIfSequential st.module)` implements `q.S` at the interface of `ChildIface.ofPkg q`: `ChildRunN … m (bsIn.take kD) outs (q.S i)` | `legacy_entry_walk` (EntryWalk:133), `legacy_entry_output_walked` (:273), `LegacyDom` (Contract:264), `legacy_translate_contract` (:327) | no supplier found. `legacy_entry_walk` has premise `hmach : machineShape? = none` (U8), false in R4; `LegacyDom` / `Value` are scalar-combinational (U4); `LegacySem` is stated, not proved (U7); the unfolded constant and the heap after T-HARN are not in its premises |
| T-SHAPE | `ChildRunN`'s non-trace conjuncts of the legacy module: `outputs = outs.map …`, inputs nodup, `"clk"`/`"rst"` presence (Seq) or absence (Comb), `argPorts` length = non-domain binder count | `addClockResetIfSequential` (Elab.lean:2233, :2218 `finishSynth`); `legacy_entry_walk` conclusion `m = (addClockResetIfSequential st.module).finalize ∧ legal` | no supplier found for the port/arity equations against `q.d.bsIn.take q.kD` and `q.d.shape.layout.outs`. Port naming of a multi-output legacy module is not stated in the files read |
| T-STATE | for a machine shape with slots/registers (`layout.slots ≠ []`) the legacy module's state reset `ResetN dsn n mc s` and the per-cycle state/slot semantics equal the package's | none | no supplier found; `Value` is scalar (U4), `SeqChildRunN`'s trace is not mentioned by any legacy contract |
| T-INST | instances (`shape.insts ≠ []`): the legacy module instantiates child modules whose `ChildRunN` at `n-1` is available (`IHAt`/`CacheShips`) | `IHAt` (Gen2Defs:~160) for reached children; `CallDec` for the package | no supplier found for the legacy translator's instances being the package's calls (`LegacyDom` has no `.inst`, U4); `closeInsts`-`none` (N2) is exactly the case where the machine route's own instance closure failed |
| T-MEMO | the memo-read at the head of `legacyTail` misses (or its hit ships) | `outer_miss` (depth 0 only), `MemoInv` (generic, §3) | no supplier found for nested; this is K4 (§3) and the memo-law design (§5.6). **Remains an obligation of `R4TailStmt`** (the `legacyTail` run in `R4Run` includes the memo read, hit and miss); not discharged by this section or by the first unit (§9.6) |
| T-PP | `b = dropZeroWidthModule raw ∨ b = mergeChecked (…)` preserves `ChildRunN` | G-TRANSPORT / G-LIFT territory (Gen2Defs docs) | no supplier found for legacy-shape modules; same obligation as for the machine route |
| T-REACH | the tail's nested children are reached names, so `IHAt`/`CacheShips` apply (`Reach` closure) | `T1Hyp.closed` states the static closure for packages' instances | no supplier found for the translator's calls under the legacy tail (not packages); `Reach` for such calls is a G-REACH item |

Reading of the table: only T-RUN and the shape-level part of T-SRC are supplied. T-LEG, T-SHAPE, T-STATE and T-INST are the substance and have no supplier in the files read; they correspond to U1-U5, U8 of §4. T-INV has a partial supplier (whole-body keep).

### 9.4 Supplier candidates and where each stops (extends §6)
- **P-1: a legacy contract for the R4 tail through `core_machine_outcomeA'''` + `legacyTail`.** Redo the `legacy_entry_walk` argument for `legacyTail` on `entryConst`, starting at `w₆` (not at a fresh world), producing T-LEG. Stops at: needs a `Contract`/`Value` that has registers, memories and instances (L-2, shared semantic definitions: user decision) and a statement that the legacy module's slots equal `layout.slots` (T-STATE). Beyond the scalar combinational fragment nothing in the files read states it.
- **P-2: a restricted R4 class.** State the producer only for packages whose shape is combinational, `slots = []`, `insts = []` (so `CombChildRunN`, scalar-per-output). Then T-STATE and T-INST are vacuous and T-LEG reduces to a multi-output extension of `legacy_entry_output_walked` (still U1-U3, U8). **This narrows the producer's scope; it does not by itself narrow FG.** Whether the remaining R4 successes are then covered by something else is OPEN. Choosing it as the only coverage would be a scope statement = user decision (D-LEGACY-SCOPE); it is listed, not chosen.
- **P-3: derive `closes` so R4 does not occur (L-3).** Unchanged from §6: `CallsClose` not derived; `kidsCombB` is a property of a different route's output; compiler guard needs a user decision.
- **P-4: tie via machine-route output.** Show that if `closeLets`/`closeInsts` returned `none` then a stronger/other certificate gives the machine meaning anyway (e.g. `harness` output `t` already implements `q.S`; only the closing step failed). Path: `synthesizeMixedCertified`'s result `(t,d₀)` is the combinational harness (the R2 route's harness); the legacy tail does NOT use it (its output is a fresh `emitLeaves` build). Stops at: the tail's output does not contain `t`; connecting the legacy module to `t` is again a legacy meaning statement (T-LEG).
No candidate here reaches a complete producer. This is a statement about what was found.

### 9.5 Checks planned (rev5: independent Expected, signature-level mutants)
Unit 1 (`Tests/Gen4/FbR4Check.lean`, new file; helper `Tests.Gen3.ExpectedType`):
1. **TYPE.** `checkExpected` compares each of `R4Run`, `A4MachineSideA` (definition values) and `a4_machine_or_R4Run` (theorem type) against an INDEPENDENT `Expected…` copy of the statement written separately in the check file, binder by binder (names, binder info, types; `==` first, `isDefEq` fallback logged). The independent copies are typed out again from §9.2.0 / the A4 conclusion in the check file; they are not `unfold`s or abbreviations of the definitions under test.
2. **No "defeq" claim for the extraction.** `a4_machine_or_R4Run` is NOT defeq to `core_machine_outcomeA'''`: the lemma instantiates `r` to `some (m,d)` / `none`, removes `∃ r` and the equation `r = none` and splits the `Or`. Its relation to A''' is the proof (a theorem), not a definitional unfolding; the check does not describe it as defeq, and no check here compares it to A''' by `isDefEq`. The statement-level check is (1) against the independent Expected of the lemma.
3. **MUTANT** (each must be rejected by the signature/defeq comparison; these are rejections of mis-typed statements, NOT semantic counterexamples): `R4Run` with (i) the `legacyTail` run's start world `w₆` replaced by `w₄`; (ii) `D ≠ 0 → StartReadsN …` replaced by `True`; (iii) the `w₆ = w₇` conjunct dropped; (iv) `JQC … w₆` dropped; (v) `StartReadsN` started at `w₅` instead of `w`; `A4MachineSideA` with `none` instead of `some (m,d)`; the lemma with the `A4MachineSideA` disjunct dropped. (A `t'`-outside-the-disjunct mutant was planned in rev5 and is not run.)
4. **AXIOMS.** `collectAxioms` ⊆ {propext, Classical.choice, Quot.sound} for all three declarations.
5. **Closure.** The check file builds only against built targets (`Tools.ShippingMachineOutcomeA4` and its imports) and the new library target; no other file imports the new files.
Later units (not scheduled; not run): TYPE against an independent `R4TailStmt`; mutants for `R4TailStmt` (dropping `P q.decl = some q`; `InvAt (dv w)` replaced by `Start`; dropping `MachineDefines`; replacing `ChildShipsI` by `∃ I n, …`; stating `R4Run` with unlinked existential worlds, i.e. `LegacyTailRunExists`; dropping the post-processing disjunct).

### 9.6 What §9 does not cover, and the next step
- Not covered (as a PRODUCER; the statement `R4TailStmt` is not narrowed, §9.2.4): R6-direct (`machineShape? = none`; no `Pkg`, D-IFACE); the memo-hit side and K4; any producer proof; `DataOk`; height lifting; `Reach` for translator calls. No FG, law, shared-definition or compiler change is proposed. No user decision item is raised by this section: P-1's L-2 and P-2's scope choice are already D-LEGACY-SCOPE / L-2 of §6-§7 and are not decided.
- Next (reviewer's call): whether `R4Run` (§9.2.2), the extraction lemma (§9.2.2) and `R4TailStmt` (§9.2.4) are an acceptable set of types to freeze. **Scope of the first implementation unit (limited; this is a unit boundary, not a scope reduction of R4):** the definitions `R4Run` and `A4MachineSideA` and the lemma `a4_machine_or_R4Run` (§9.2.2; new files `Tools/ShippingGen4FbR4.lean`, `Tests/Gen4/FbR4Check.lean`, new `lean_lib`s only) (a repackaging of the built `core_machine_outcomeA'''`: no new law, no new premise, no new hypothesis about a package's meaning). It supplies nothing toward `R4TailStmt`'s conclusion, and the memo obligation (T-MEMO/K4), T-LEG, T-SHAPE, T-STATE, T-INST, T-SRC beyond the shape level, T-INV and T-PP all remain open obligations of R4. Later units are not scheduled by this document.
- **Build evidence for FB-1 (R3):** build evidence: g4fbv-79e6d672 (clean issue-linked kjob run, clean detached worktree, SHA 79e6d672; log path and marker are recorded by the coder in the Issue note, not here).

### 9.7 T-INV: further supplier research (rev4; no supply claimed)
The question: is there a supplier of `InvAt L P Reach (D+1)` (in particular `CacheShips`, not only `JQC`) at the intermediate worlds `w₄` and `w₆` of `R4Run`?
- **Found (as typed):** `stableA_invAt` (Tools/ShippingGen2Connect.lean:41): `InvAt` is `StableA`, i.e. it depends only on `cv`, `sv`, `dv`, quiet. `machineCert_keepsAP` (Tools/ShippingChildFrontCP.lean:107) is generic in the invariant `I`: from `hchild : ∀ c, Keeps I (synthesizeChild c)`, `hsv : ∀ w, I w → sv w = some synthesizeChild`, `htr : ∀ e hint top named, KeepsCP I (translate …)` and `hA, hS (StableA)`, it gives `Keeps I (synthesizeMachineCertified translate (profLogIO b) declName shape)` — a keep of the machine attempt for any such `I`, so potentially for `I := InvAt L P Reach (D+1)`. `ChildKeepsInv L P Reach (D+1)` is `ChildSynthA L.O (InvAt …)`, i.e. `∀ mctx cctx, AdmCtx → ∀ c, Keeps (InvAt …) (synthesizeChild c)`: exactly `hchild` at that `I`, and it is already a premise of `R4TailStmt`. `legacyTailA_generic` (Tools/ShippingChildLegacyTailA.lean:194) likewise keeps any `StableA` `I` given `RecA O I translate`.
- **Candidate path (NOT verified; not a proof):** `InvAt (D+1)` at `w₄` + `machineCert_keepsAP` at `I = InvAt (D+1)` would give `InvAt (D+1)` at `w₆` (the machine attempt returned `none`; `Keeps` constrains every outcome's end world — to be confirmed against the `Keeps` definition for the `none` return). Remaining gaps on this path, each unverified: (1) `InvAt (D+1)` at `w₄` from `InvAt D` at `w`: A''' gives only `JQC (D+1)` at `w₃`/`w₄`; the entry prefix (reads, saved-map `get`s, the depth `set` to `D+1`, `getConstInfo`, two `getEnv`) must be shown not to change `cv` (CacheShips depends on `cv`) — framed reads are used in A''' for `JQC`, but a `CacheShips`-level statement for the depth set (`tripleC_depthSet`) was not checked; and `w` is not chained to `w₁` in A''' (§9.2.1); (2) `htr`: `KeepsCP InvAt (translateExprToWire tenv …)` for the specific `tenv` — the hypothesis shape `RecA O I translate` is what `legacyTailA_generic` asks; whether `KeepsCP` at `InvAt` for `translateExprToWire` follows from `ChildKeepsInv` was not found stated (the `translateRel`/`harnessRel_of` family in ShippingChildBody.lean:55-70 is at `J L D` = JQ-level, not `InvAt`); (3) `hsv` from `InvAt` (via its `JQ` part: `JQ` includes the synthesis ref; not checked in this pass).
- **Result:** the earlier text said "no supplier found for `InvAt` at `w₆`". Refined: a candidate path through generic lemmas exists in the files read; gaps (1)-(3) above are what this investigation did not close. This does not supply T-INV and does not say it is derivable or underivable.
- **Independent next steps** (research only; no Lean before approval): (i) read `Keeps` and `tripleC_depthSet` to settle gap (1) and the `none`-outcome question; (ii) look for an `InvAt`-level `KeepsCP` of `translateExprToWire` (gap (2)); (iii) for the legacy tail itself, T-INV at the TAIL'S END is `legacyTailA_generic` given (2) — the same `RecA O I translate` hypothesis.

### 9.8 T-INV: research continued (rev5; read-only; no supply claimed)
Done for the "independent next steps" of §9.7, by reading the cited files. Nothing here is a proof and nothing is built.
- **(i-a) `Keeps` and the `none` outcome (settled by definition).** `Keeps I m := ∀ w, I w → I (endW … m w) ∧ ErrOk … m w` (Tools/ShippingChildInv.lean:315), and `endW` is the end world on either outcome (`.ok` or `.error`, :300-303). So a `Keeps` statement about `synthesizeMachineCertified` constrains the end world whether it returns `some` or `none`; the "to be confirmed" in §9.7 for the `none` return is answered by the definition. (A run `RunsTo … w₄ none w₆` has `w₆ = endW … w₄`; the lemma relating them is `endW_of_runs`, used in A4's text at ChildCacheA.lean:~250; its exact name/signature at this use was not re-checked.)
- **(i-b) Prefix steps and `InvAt`.** `keepsA_framed O hA (hS : StableA O.quiet I) (hp : FramedA _ p) : Keeps … I p` (Tools/ShippingChildVCA.lean:71) is generic in `I`; `stableA_invAt` (ShippingGen2Connect.lean:41) gives `StableA` for `InvAt`. So the framed prefix reads (`getConstInfo`, `getEnv`; A4 uses them with `stableA_JQC`) keep `InvAt` by the same lemma at `I = InvAt`. For the depth set, `tripleC_depthSet` (ChildCacheA.lean:235) is stated for `JQC`; its proof shows `cv` unchanged (`hk.1`), and `CacheShips` depends on `cv` only, so `InvAt D → InvAt (D+1)` across the set is a candidate small lemma (not found stated; not written). **Remaining part of gap (1):** A4's conclusion contains no explicit run `w → w₁` (§9.2.1), so even with these lemmas the producer has no run to apply them along; that would need either a stronger extraction (re-deriving A4's prefix with `InvAt` carried) or an A4 variant. This is the open part.
- **(ii) `KeepsCP … InvAt` for `translateExprToWire`.** `htr_of_tele` (ChildRunAMain.lean:37) gives it at `JQC O (D+1)` through `translate_keepsC_of_tele` (ChildComposeC.lean:53), whose body is built from `hS := stableA_JQC`, `childEntryA_JQC…`, `canonKeyA O hS`, `legacyImplA_of_tele O hS T hcanon hchild`, `legacyCachedA_of_impl`, `projFieldNameA O T hS`, `translate_keepsA O hS tenv …`. Of these the `hS`-parametric ones take `hS` as an argument; `childEntryA_of_childSynthA O hS hsv hC` (ChildFrontCP.lean:248) is the `I`-generic version of the child-entry keep and `ChildKeepsInv L P Reach (D+1)` is by definition `ChildSynthA L.O (InvAt …)` (Gen2Defs.lean:174-176). So an `I = InvAt` copy of `translate_keepsC_of_tele` is a candidate; I did not verify that each component is `I`-generic (only the signatures cited above were read), and it was not found stated.
- **(iii) Tail end.** `legacyTailA_generic` (ChildLegacyTailA.lean:194) at `I = InvAt` would give `InvAt` at the tail's END `w₅` from `RecA O I translate` (= (ii)) and `StableA` (= `stableA_invAt`); not applied.
- **Result.** This pass narrowed (1) to the missing `w → w₁` run and the unwritten depth-set lemma, and (2)/(3) to an unverified `I`-generic copy of an existing proof. T-INV is still NOT supplied; this does not say it is derivable or underivable.

---

## 10. T-INV: complete types of the `InvAt` prefix / depth / translate keeps (rev6; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only. Nothing in this section is built, and none of the statements below has been checked by Lean. It fixes types for a possible later unit "FB-3"; it does not supply T-INV, it does not supply any part of `R4TailStmt`, and it says nothing about derivability. FB-2 (`R4Run`, `A4MachineSideA`, `a4_machine_or_R4Run`) is unchanged and stays the approved repackaging of A4's witness. No new law, no new field of `Laws`, no shared-definition edit: every statement below is a THEOREM whose proof is planned from existing fields (`O.depthSet`, `O.cacheSet`, `O.frame`, …) and existing lemmas. "Planned proof" is a plan, not a result; if a step does not go through, that is reported as "not closed in this attempt", not as impossible.
- **Why FB-2 alone cannot be used for T-INV.** `R4Run` carries `JQC` at `w₃, w₄, w₆`, but `InvAt = JQC ∧ CacheShips` and A4's conclusion has no run `w → w₁` (§9.2.1, §9.8 (i-b)). The `CacheShips` half has to be carried along the REAL prefix of the core run, so the prefix peel of `core_reads_link4A` (Tools/ShippingMachineOutcomeA4.lean:116) has to be redone with `InvAt` threaded. §10.2-§10.6 give the types.
- **Ambient (new file `Tools/ShippingGen4FbInv.lean`, namespace `Tools.ShippingGen4FbInv`).** `import Tools.ShippingGen4FbR4` and `import Tools.ShippingGen2Keep` (which imports `ShippingGen2Connect`, `ShippingChildPinC`). `open`s: those of `Tools/ShippingGen4FbR4.lean` (copied verbatim) plus `open Tools.ShippingGen2 Tools.ShippingGen4FbR4`. `variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}`; `L : Laws mref cref`, `P : Pkgs ι dom`, `Reach : Name → Prop`, `mctx : Meta.Context`, `cctx : Core.Context` are binders where shown. New `lean_lib`s only (`Tools.ShippingGen4FbInv`, `Tests.Gen4.FbInvCheck`); no other file imports them.

### 10.1 What already exists (reused as typed; nothing is re-proved)
| id | item | location | what it says | note |
|---|---|---|---|---|
| E-STAB | `stableA_invAt L P Reach D : StableA L.O.quiet (InvAt L P Reach D)` | ShippingGen2Connect.lean:41 | `InvAt` depends on `cv`, `sv`, `dv`, quiet only | proved there |
| E-SV | `invAt_sv L P Reach D : ∀ w, InvAt L P Reach D w → sv w = some synthesizeChild` | ShippingGen2Keep.lean (before `translate_keepsInv_of_tele`) | `hsv` for `machineCert_keepsAP` | proved there |
| E-TRANS | `translate_keepsInv_of_tele L P Reach D (hC : ChildKeepsInv L P Reach D) tenv : RecA L.O (InvAt L P Reach D) (fun e h t n => translateExprToWire tenv e h t n)` | ShippingGen2Keep.lean (docstring "The translator keeps `InvAt D` from the child hook") | **the `InvAt`-level translate keep. §9.8 (ii) said an `I`-generic copy was "not found stated"; this one exists in the file** | the file has no BUILT header line; the lakefile has `lean_lib Tools.ShippingGen2Keep`; this investigation did not build it, so FB-3 must build the import before relying on it |
| E-FRAMED | `keepsA_framed O hA (hS : StableA …) (hp : FramedA Fresh p) : Keeps … I p`; `keepsA_diag` (ShippingChildVCA.lean:85) | ShippingChildVCA.lean:71 | any framed or diag step keeps any `StableA` invariant | generic in `I` |
| E-MACH | `machineCert_keepsAP` | ShippingChildFrontCP.lean:107 | `Keeps I (synthesizeMachineCertified translate (profLogIO b) declName shape)` from `htr : ∀ e hint top named, KeepsCP … I (translate e hint top named)`, `hchild : ∀ c, Keeps … I (synthesizeChild c)`, `hsv`, with `O`, `hA`, `hS` | generic in `I` |
| E-CHILD | `ChildKeepsInv L P Reach D := ChildSynthA L.O (InvAt L P Reach D)` | ShippingGen2Defs.lean:175 | `∀ mctx cctx, AdmCtx → ∀ c, Keeps … (InvAt …) (synthesizeChild c)` | exactly `hchild` after instantiating `mctx cctx hA` |
| E-KEEPS | `Keeps I m := ∀ w, I w → I (endW … m w) ∧ ErrOk … m w` | ShippingChildInv.lean:315 | constrains the end world of BOTH outcomes | answers the `none` question (§9.8 (i-a)) |
| E-DSET | `tripleC_depthSet`, `tripleC_clear` | ShippingChildCacheA.lean:235, :218 | stated at `JQC` / `JQ` only | not at `InvAt` — hence K-DEPTH / K-CLEAR below |

### 10.2 K-CLEAR (the depth-0 cache clear, at `InvAt`) — new theorem
```lean
theorem invAt_cacheClear (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ L.O.quiet D)
      (sparkleChildCache.set {} : MetaM Unit) (fun _ => InvAt L P Reach D) R
```
Planned proof: as `tripleC_clear` (ShippingChildCacheA.lean:218): `O.cacheSet`, `O.cacheSetQ`; the new cache value is `{}` (`hk.1`), so `JQC` by `cacheInvA_empty` and `CacheShips L P Reach {}` because `{}.get? c = none` (`Std.HashMap.get?_empty`). `Triple` is the one of `ShippingChildKeeps.lean:50`; its namespace is read from that file when FB-3 is written. Needed only for the `D = 0` branch of the prefix.

### 10.3 K-DEPTH (the depth set `D → v`, at `InvAt`) — new theorem
```lean
theorem invAt_depthSet (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx) (D v : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (InvAt L P Reach D)
      (ST.Ref.set sparkleSynthDepth v : MetaM Unit) (fun _ => InvAt L P Reach v) R
```
Planned proof: as `tripleC_depthSet` (ShippingChildCacheA.lean:235) for the `JQC` half; for `CacheShips`, that proof shows `cv` unchanged (`hk.1`), so rewrite it and reuse `h.2`. This is the lemma §9.8 (i-b) called "candidate, not found stated"; it is stated here, not proved. Used with `v = D + 1`.

### 10.4 K-LINK: the core prefix with `InvAt` threaded — new theorem (`core_reads_link4A` plus one conjunct)
```lean
theorem core_reads_link4Inv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {D : Nat} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {Dg : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, Dg) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo) (w1 w2 w3 w4 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, Dg) w4 ∧ JQC L.O (D + 1) w3 ∧
      InvAt L P Reach (D + 1) w3 ∧
      ∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
        (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
        (sg : Std.HashMap String String),
        RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w4 () w' ∧
        (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
        (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
          declName b D w sf sw sl sp sc ss sg)
```
The conclusion is `core_reads_link4A`'s with ONE added conjunct, `InvAt L P Reach (D + 1) w3`. Premise `hI` replaces `hw : JQ O.quiet D w` and `hc` (they follow: `hw := hI.1.1`; `hc := Or.inr hI.1.2`, or `Or.inl` when `D = 0`; the proof case-splits on `D = 0` like the original). Planned proof: the original's two branches; each peel step applies `keepsA_framed`/`keepsA_diag`/`framed_runs` with `stableA_invAt` instead of `stableA_JQ/JQC` (E-FRAMED); the `D = 0` branch uses `invAt_cacheClear`; both use `invAt_depthSet D (D+1)`; `getConstInfo`/`getEnv` by `FramedA.constInfo`/`FramedA.env` at `stableA_invAt (D+1)`. This is the "stronger extraction" §9.8 (i-b) named as the open part. Not checked here: that each `peelK/peelF/peelP` use goes through at `InvAt` (the macros are written against `stableA_JQ`/`JQC`; FB-3 writes `InvAt` versions in the new file or inlines the steps).

### 10.5 K-MACH: the machine attempt keeps `InvAt (D+1)` — new theorem (instance of E-MACH)
```lean
theorem machineAttempt_keepsInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach (D + 1))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (shape : MachineShape) :
    Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
      (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb) declName shape)
```
Planned proof: `machineCert_keepsAP` at `O := L.O`, `hA`, `hS := stableA_invAt L P Reach (D+1)`, `translate := fun e hint top named => translateExprToWire tenv e hint top named`, `htr := fun e hint top named => translate_keepsInv_of_tele L P Reach (D+1) hC tenv mctx cctx hA e hint top named` (E-TRANS; `RecA` is `∀ mctx cctx, AdmCtx → ∀ e hint top named, KeepsCP …`), `hchild := hC mctx cctx hA` (E-CHILD), `hsv := invAt_sv L P Reach (D+1)` (E-SV).

### 10.6 K-RUN: the packaged type `R4RunInv` and the extraction — new definition and theorem
`R4RunInv` is `R4Run` (§9.2.2, FB-2) with the same existential witnesses and two added conjuncts, `InvAt L P Reach (D + 1) w₄` and `InvAt L P Reach (D + 1) w₆`. It is a separate definition because the worlds are existentially bound in `R4Run`; the built `R4Run` is not edited.
```lean
def R4RunInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧
    -- followed by EXACTLY the conjuncts of the built `R4Run` body (Tools/ShippingGen4FbR4.lean, the part after
    -- the `∃` binders), same order, same text, with `O := L.O`
```
The conjunct list is fixed by reference to the built text rather than copied here, to avoid a second copy that could drift; FB-3 writes it out in full and the Expected copy in the check file is typed separately (§9.5). The extraction:
```lean
theorem a4_inv_machine_or_R4RunInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInv L P Reach mctx cctx D declName shape m d w w'
```
Planned proof: the proof of `core_machine_outcomeA'''` (Tools/ShippingMachineOutcomeA4.lean:224-273) with `core_reads_link4A` replaced by `core_reads_link4Inv`; `T := L.T`; `hw`, `hc` from `hI`; `InvAt (D+1) w₃` from K-LINK; `InvAt (D+1) w₄` from `w₃` by `keepsA_framed` at `stableA_invAt (D+1)` with `FramedA.env`; `InvAt (D+1) w₆` from `machineAttempt_keepsInv` and `endW_of_runs` for the run `w₄ → w₆`; then the same `rcases` on item 10 as `a4_machine_or_R4Run`. The (a) side stays `A4MachineSideA` (no `InvAt` conjuncts there). Premises beyond A4's: `hI` (the statement's own `InvAt L P Reach D w`, stronger than `hw/hc`) and `hC` (already a premise of `R4TailStmt`, §9.2.4). `P q.decl = some q`, `Reach` as a hypothesis and `IHAt` are not used by this lemma.

### 10.7 Supplier table (after this section nothing is supplied yet)
| part | supplier | status |
|---|---|---|
| translate keep at `InvAt (D+1)` | E-TRANS `translate_keepsInv_of_tele` | exists; written as proved in its file; not built by this investigation |
| machine attempt keep at `InvAt (D+1)` | K-MACH from E-MACH, E-TRANS, E-CHILD, E-SV | type fixed here; proof planned; not written |
| framed prefix steps (`getConstInfo`, `getEnv`, saved-map `get`s, profile reads) | E-FRAMED at `stableA_invAt` | existing lemma, instantiated inside K-LINK |
| depth set `D → D+1` | K-DEPTH | type fixed; no existing `InvAt`-level statement found |
| depth-0 cache clear | K-CLEAR | type fixed; no existing `InvAt`-level statement found |
| the missing run `w → w₁` (§9.2.1) | K-LINK carries `InvAt` along the REAL prefix | type fixed; proof planned; peel macros not checked at `InvAt` |
| packaging for the R4 statement | `R4RunInv` + `a4_inv_machine_or_R4RunInv` (K-RUN) | type fixed; not written |
| `InvAt` at the tail's END `w₅` (`legacyTailA_generic` at `I = InvAt (D+1)`) | E-TRANS gives `RecA`; but `legacyTailA_generic` is about `synthesizeFromConst … false false ci`, and the match with the `legacyTail` run in `R4Run` was not checked | NOT in FB-3; open |
| `InvAt` at `w₇` (harness) | not looked at beyond `mixed_keepsAP` being used inside E-MACH | not in FB-3; not needed for the tail's start `w₆` |

### 10.8 Checks planned for FB-3 (after this section is approved; nothing run)
1. TYPE: each of `invAt_cacheClear`, `invAt_depthSet`, `core_reads_link4Inv`, `machineAttempt_keepsInv`, `R4RunInv` (definition value), `a4_inv_machine_or_R4RunInv` against an independent `Expected…` typed again in `Tests/Gen4/FbInvCheck.lean` (`checkExpected`, `==` first, logged `isDefEq` fallback).
2. MUTANTS (rejections of mis-typed statements by signature/defeq, NOT semantic counterexamples): `invAt_depthSet` with `JQC` instead of `InvAt` in the post; `machineAttempt_keepsInv` at `InvAt L P Reach D` instead of `D+1`; `core_reads_link4Inv` with the `InvAt (D+1) w3` conjunct dropped; `R4RunInv` with the `w₆` conjunct dropped; `a4_inv_machine_or_R4RunInv` without `hC`; with `hI` replaced by `JQ`.
3. AXIOMS `⊆ {propext, Classical.choice, Quot.sound}`; `sorry` 0; no `native_decide`.
4. No edit of Tools/ShippingGen2Defs, Elab*, T1Hyp*; new files and new `lean_lib`s only.

### 10.9 What this section does not claim
- It does not claim T-INV is supplied, nor that `R4TailStmt` is closer to proved: T-INV is one obligation among T-MEMO, T-LEG, T-SHAPE, T-STATE, T-INST, T-SRC (beyond shape), T-PP, T-REACH, K4 — all still open.
- The planned proofs are plans. Unchecked steps are named above (peel macros at `InvAt`; `Triple` namespace; `ShippingGen2Keep` not built here; `legacyTail` vs `synthesizeFromConst` at the tail end).
- No user decision is raised: only existing fields/lemmas are used. If FB-3 finds a step that needs a new law field, that is a stop-and-decision point (not decided here).

## 11. FB-3 implementation status (docs sync; Pod build only)

- Implemented per §10 in `Tools/ShippingGen4FbInv.lean` (`invAt_cacheClear`, `invAt_depthSet`, `core_reads_link4Inv`, `machineAttempt_keepsInv`, `R4RunInv`, `a4_inv_machine_or_R4RunInv`) and checked in `Tests/Gen4/FbInvCheck.lean`, at f172d4b7: `kjob lake build Tests.Gen4.FbInvCheck` exit 0 inside the Pod. A clean issue-linked build is the coder's and has not been done by this unit.
- `R4RunInv` is the `R4Run` body of e7181279 with `O := L.O` and the two leading conjuncts `InvAt (D+1) w₄`, `InvAt (D+1) w₆`; the check compares it with an independently typed Expected and proves the projection `R4RunInv → R4Run` (`r4RunInv_to_R4Run`) and the projected extraction (`a4_inv_projects_to_a4_machine_or_R4Run`). K-LINK and K-RUN share the same prefix witness (`w₃ w₄ w₆` from one peel, one `getEnv`, one machine run); no separate existentials are identified.
- Mutants are rejections by signature/defeq, not semantic counterexamples. The `a4_inv_machine_or_R4RunInv` conclusion is accepted by logged `isDefEq`, not syntactically.
- **Not supplied.** Preserving `InvAt` up to the tail's START world `w₆` is a different thing from the semantic guarantee of the legacy route and of the memo hit. The latter two are NOT supplied (T-LEG, T-MEMO, tail end `w₅`, K4, post-processing remain open). No new law or shared-definition change was used.

---

## 12. FB-4: tail-end `InvAt` and the semantic obligations — complete types, supplier table (rev7; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only; nothing below is built or checked by Lean. Base = `f07f4bf2` (FB-3, limited approval: `InvAt` up to `w₄` and the tail START `w₆`; machine-none extraction). This section (a) fixes the types of ONE further preservation unit, "FB-4", and (b) fixes, as TARGET SCHEMAS (text only, no Lean, no proof), the statements that the meaning of the legacy tail, of the memo hit and of the post-processing would have to take. No new law, no new field of `Laws`, no shared-definition edit, no change of FG or of a guarantee. "Planned proof" is a plan, not a result; a step that does not go through is reported as "not closed in this attempt".
- **Two different things are kept apart throughout.**
  1. **Preservation (P)**: a heap invariant (`InvAt`) holds at a world. FB-3 gave it at `w₃`, `w₄`, `w₆`. FB-4 adds `w₅` (the END of the `legacyTail` run). It says nothing about what the module `(m, d)` computes.
  2. **Semantic guarantee (S)**: `(m, d)`, after post-processing, ships (`ChildShipsI (ChildIface.ofPkg q) n out dsg`). This is T-LEG / T-MEMO / T-PP / T-SHAPE / T-STATE / T-INST (§9.3). **Nothing in §12.1–§12.3 is (S).** §12.4–§12.6 fix the TYPES of (S) and supply none of it.
- **What must not be confused.** The `JQC …` conjuncts at the end of `R4Run` (`JQC (D+1) w₄/w₆/w₇`, `JQC D w'`) are heap-shape facts (`JQ ∧ CacheInvA`), not `InvAt` (no `CacheShips`) and not meaning. `JQC O D w'` is at the END of `coreFinally` (`w'`), after the tail end `w₅`; it is not `InvAt` at `w₅`. `InvAt (D+1) w₅` does not give `InvAt D w'` (see T-FIN below).

### 12.1 What exists (reused; nothing re-proved)
| id | item | where | note |
|---|---|---|---|
| E-TAILCORE | `legacyTail_core` / `legacyTailA_generic`: `Keeps … I (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst)` for any `StableA` `I`, `RecA O I translate`, `T : RefLawsATele` | Tools/ShippingChildLegacyTailA.lean:138 / :194 | stated about `synthesizeFromConst … false false ci isInst`, NOT about the named program `legacyTail`. That the two coincide was **not checked** (§10.7 row 7 stands). |
| E-LTAIL | the named program `legacyTail translate logProf declName parameters symbolicMode constInfo` | Tools/ShippingMachineOutcomeA.lean:54 | verbatim copy of the memo-read + legacy arm; the `RunsTo` in `R4Run` is about this program with `parameters = []`, `symbolicMode = false`, `constInfo := entryConst true false [] ci (instancePredicate tenv) (userInliner tenv) (structEnv tenv)` |
| E-TRANS | `translate_keepsInv_of_tele L P Reach D hC tenv : RecA L.O (InvAt L P Reach D) (fun e h t n => translateExprToWire tenv e h t n)` | Tools/ShippingGen2Keep.lean:~40 | used by FB-3 inside K-MACH (built, f07f4bf2) |
| E-STABLE | `stableA_invAt L P Reach D : StableA L.O.quiet (InvAt L P Reach D)` | Tools/ShippingGen2Connect.lean:41 | |
| E-RUN4 | `a4_inv_machine_or_R4RunInv` (FB-3), `R4RunInv` (FB-3) | Tools/ShippingGen4FbInv.lean | `InvAt (D+1)` at `w₄`, `w₆` with the same witnesses as the run data |

### 12.2 K-TAIL: the `legacyTail` run keeps `InvAt (D+1)` — new theorem
```lean
theorem legacyTail_keepsInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach (D + 1))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (ci : ConstantInfo) :
    Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
      (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false ci)
```
`ci` is arbitrary (it is instantiated with the `entryConst …` of `R4Run`). Premises: exactly `hC`, `hA` (as K-MACH). `L.T` is the telescope family inside `Laws`; no extra premise.
Planned proof (two routes; the first that closes is used, and the document is synchronised to the one used):
- **Route 1.** Show `legacyTail … ci` is (definitionally or by `rfl`/`show`) the part of `synthesizeFromConst translate (profLogIO pb) declName [] false false ci' isInst` that `legacyTail_core` reasons about, and apply `legacyTailA_generic L.O L.T (stableA_invAt L P Reach (D+1)) hA _ (translate_keepsInv_of_tele L P Reach (D+1) hC tenv) pb declName ci' isInst`. The `synthesizeFromConst` body has binds before the tail (environment/entry construction), so a plain `rfl` is not expected; if Route 1 needs a bridging lemma that is not a one-liner, Route 2 is used.
- **Route 2 (replay).** `unfold legacyTail`, then replay the proof of `legacyTail_core` from its `Keeps.bind (by vca) fun memo => …` step on (`keepsA_lambdaTelescope`, `splitReturnLeaves_keeps`, `tripleA_mkExprCache`, `bindInputsLegacy_keepsCP`, `emitLeavesAP`, `finishSynthA`, `keepsA_framed … sideModify`), with `O := L.O`, `hS := stableA_invAt L P Reach (D+1)`, `TLam/TF := L.T`'s two telescope laws, `htr := translate_keepsInv_of_tele …`. The existing file is not edited; the replay lives in the new file. The `match constInfo with | .defnInfo … | _ => throwError` arm and the `if !symbolicMode` memo arm are the steps to re-check (`symbolicMode := false` is fixed).
- If neither route closes, FB-4 stops at that point and reports "not closed in this attempt" with the failing step; this is not a claim that the keep is false.

### 12.3 K-RUNT: `R4RunInvT` and the extraction — new definition and theorem
`R4RunInvT` is `R4RunInv` (FB-3, `Tools/ShippingGen4FbInv.lean` at `f07f4bf2`) with ONE more leading conjunct `InvAt L P Reach (D + 1) w₅`:
```lean
def R4RunInvT (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
    -- followed by EXACTLY the conjuncts of the `R4RunInv` body after its two leading `InvAt` conjuncts
    -- (Tools/ShippingGen4FbInv.lean at f07f4bf2), same order, same text
```
The conjunct list is fixed by reference to the built text (pinned at `f07f4bf2:Tools/ShippingGen4FbInv.lean`, which pins `e7181279:Tools/ShippingGen4FbR4.lean`), not copied here; FB-4 writes it out in full and the check file types an independent Expected (§12.7). The worlds are existentially bound, so this is a separate definition (the built `R4RunInv` is not edited).
```lean
theorem a4_inv_tail_machine_or_R4RunInvT (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w'
```
Planned proof: `rcases a4_inv_machine_or_R4RunInv L P Reach hA hI hC hr entry` (FB-3). (a) side: unchanged. (b) side: destructure the ONE witness package it returns (`tenv pb ci envR' w₁…w₆`, `InvAt w₄`, `InvAt w₆`, the tail run `htail : RunsTo (legacyTail …) … w₆ (m, d) w₅`, the rest); obtain `InvAt (D+1) w₅` as `triple_runs (keeps_iff.mp (legacyTail_keepsInv L P Reach D hC hA tenv pb declName _)) hI6 htail`; re-pack with the same witnesses. **No second existential for `w₅`: it is the `w₅` of the same package, so `InvAt` at `w₅` is about the world the tail run ends in, which is the world `coreFinally` starts from.** (a) side stays `A4MachineSideA` (no `InvAt` conjuncts, as in FB-3).
Projections (theorems in the check file, not defeq): `R4RunInvT → R4RunInv` (drop the `w₅` conjunct), and by FB-3's `r4RunInv_to_R4Run` `R4RunInvT → R4Run` (the old FB-2 type, `O := L.O`). The extraction projects to FB-3's `a4_inv_machine_or_R4RunInv` and, composed with `a4_inv_projects_to_a4_machine_or_R4Run`, to FB-2's `a4_machine_or_R4Run` (the check re-proves these two projected statements). Direction of consequence for the target statements: a statement with hypothesis `R4Run` (§9.2.4 `R4TailStmt`) implies the same statement with hypothesis `R4RunInvT` (stronger hypothesis); not conversely, and **a caller who only has `R4Run` cannot recover `InvAt` at `w₄/w₆/w₅`**, because `R4Run`'s worlds are existential and not linked to `w` (§9.2.1). That is why the pipeline hands the extraction's `R4RunInvT` to the output statement (§12.4), not a separately obtained `R4Run`.

### 12.4 The output statement (target schema; NOT Lean in FB-4; nothing proves it)
`R4OutStmt` is `R4TailStmt` (§9.2.4) with the hypothesis `R4Run` replaced by `R4RunInvT` and the post-processing written out in full (§12.6):
```lean
def R4OutStmt (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat) (w w' : Void IO.RealWorld)
    (raw : Module) (dsg : Design) (out : Module) (dout : Design),
    Reach q.decl → P q.decl = some q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach D w → IHAt L P Reach (D + 1) → ChildKeepsInv L P Reach (D + 1) →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref w (raw, dsg) w' →
    PPRel raw dsg out dout →
    MachineDefines mctx mref cctx cref q.decl q.d.shape →
    R4RunInvT L P Reach mctx cctx D q.decl q.d.shape raw dsg w w' →
    ∃ n, ChildShipsI (ChildIface.ofPkg q) n out dout
```
Pipeline: `hr` ⟶ (K-RUNT) `A4MachineSideA ∨ R4RunInvT` ⟶ the (b) side feeds `R4OutStmt`. The (a) side (machine returned `some`, the result is memoised) is outside this statement. `R4OutStmt` is the target for R4 AS A WHOLE, memo hit included; it is not narrowed. The decomposition below (T-LEG-miss, T-MEMO-hit, T-PP) is how a proof of it would be organised; each part is an obligation that is **not supplied**.

`PPRel` differs from `R4TailStmt`'s `out = dropZeroWidthModule raw ∨ …` in one respect that this freeze records: the design is rewritten too (Elab.lean `synthesizeCombinationalWith`, 5598-5606: `top f d := { d with modules := d.modules.map fun x => if x.name == m.name then f x else x }`), so the conclusion is stated for `dout`, not for `dsg`. `ChildIface` needs `dout.modules = []` (ShippingCallsGate.lean:233); `dout.modules` is the `map` of `dsg.modules`, so it is empty iff `dsg.modules` is empty. Whether `dsg.modules = []` for the tail's output is **not** established here (a gate/legacy-route fact; see T-LEG).

### 12.5 T-LEG / T-MEMO: the types of the two output-meaning statements (target schemas; not Lean; not supplied)
Tail dichotomy at the tail start `w₆` (the memo read is the first action of `legacyTail`, with `symbolicMode = false`):
```lean
-- K-TSPLIT (type fixed; NOT in FB-4's implementation scope): the run of legacyTail returning (m,d) is a hit or a miss.
def MemoGetAt (declName : Name) (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design))
    (mctx cctx) (w : Void IO.RealWorld) : Prop :=
  ∃ w₁, RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w memo w₁
theorem legacyTail_hit_or_miss {translate logProf declName ci mctx cctx w w₅ m d}
    (h : RunsTo (legacyTail translate logProf declName [] false ci) mctx mref cctx cref w (m, d) w₅) :
    (∃ memo, MemoGetAt declName memo mctx cctx w ∧ memo.get? declName = some (m, d)) ∨
    (∃ memo, MemoGetAt declName memo mctx cctx w ∧ memo.get? declName = none)
```
The miss arm records only the miss at `w₆`; the build that follows is not given a name here (`legacyTail` has no named "rest" program). No claim is made about `w₅` vs `w₆` in the hit arm.

**T-MEMO-hit (target).** For a hit the module is whatever an earlier run stored under the NAME `declName` (the key ignores parameters, translator, constant, `symbolicMode`: Tools/ShippingMemoInv.lean header). The statement would be
```lean
def MemoHitStmt (LM : RefLawsM mref cref) (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ (q : Pkg ι dom) D (w₆ : Void IO.RealWorld) (raw : Module) (dsg : Design) (out : Module) (dout : Design),
    Reach q.decl → P q.decl = some q → MemoInv LM (PhiPP L P Reach) w₆ →
    (∃ memo, MemoGetAt q.decl memo … w₆ ∧ memo.get? q.decl = some (raw, dsg)) →
    PPRel raw dsg out dout → ∃ n, ChildShipsI (ChildIface.ofPkg q) n out dout
-- PhiPP L P Reach := fun n r => Reach n → ∀ b dd, PPRel r.1 r.2 b dd →
--    ∃ q' n', P n = some q' ∧ q'.decl = n ∧ ChildShipsI (ChildIface.ofPkg q') n' b dd     (§5.5)
```
and would follow from `memoInv_hit` (Tools/ShippingMemoInv.lean:88) given `MemoInv LM (PhiPP …) w₆` and `P q.decl = some q`, `q'.decl = q.decl` (injectivity of `P` on names is part of the `Pkgs` structure and was not re-checked). **What is not supplied:** (i) `LM : RefLawsM mref cref` is NOT a field of `Laws` (`Laws` has `O : RefLawsAOps` and `T`; `RefLawsM extends RefLaws`); whether one world interpretation can satisfy both by transport of existing laws, or only by a new assumption, is the open D-MEMO-LAW (§5.6, §7) and is **not decided here**. If a proof needs `LM` as a new premise or law, that is a stop-and-decision point (user's), not something FB-4 introduces. (ii) `MemoInv LM (PhiPP) w₆` itself: the memo-content invariant at the tail start; `ArmObligations`/`MemoSound` (ShippingMemoInv.lean:152/:209) are statements only and unused in the repo; K4 (memo names ⊆ `childCache` names ∪ {top}) is a reading of the source, not proved. (iii) The miss arm WRITES the raw result (`sparkleSubModuleCache.modify (·.insert declName result)`), so keeping `MemoInv` across the tail also needs the miss arm's own T-LEG-miss below.

**T-LEG-miss (target).** For a miss the module is `finishSynth declName [] false` of the final circuit state of the legacy build (`emitLeaves`/`bindInputsLegacy`). The statement would be
```lean
def LegMissStmt (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ (q : Pkg ι dom) mctx cctx D (w w' : Void IO.RealWorld) (raw : Module) (dsg : Design),
    Reach q.decl → P q.decl = some q → AdmCtx L.O.quiet mctx cctx → InvAt L P Reach D w →
    IHAt L P Reach (D + 1) → ChildKeepsInv L P Reach (D + 1) →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref w (raw, dsg) w' →
    MachineDefines mctx mref cctx cref q.decl q.d.shape →
    R4RunInvT L P Reach mctx cctx D q.decl q.d.shape raw dsg w w' →
    (the tail's memo read at its start world w₆ missed) →
    ∃ n, ChildShipsI (ChildIface.ofPkg q) n raw dsg     -- the RAW output, before PPRel
```
("the tail's memo read … missed" needs the same-witness `w₆` of the `R4RunInvT`; a statement that re-obtains a `w₆` would break the tie, so it is stated through the package's `w₆` — which is why `R4RunInvT`'s existential is destructured, not re-quantified.) **What is not supplied:** all of T-LEG, T-SHAPE, T-STATE, T-INST, T-REACH (§9.3 rows): no supplier was found for any of them in the files read. In particular `legacy_entry_walk` has the premise `hmach : machineShape? = none` (false in R4), `LegacyDom`/`Value` are scalar-combinational (U4), and the tail's world is `w₆` (after the machine attempt and the `closeInsts` / harness), not a fresh world (U8). `InvAt (D+1) w₅` (K-TAIL) is NOT such a supplier: it keeps the cache honest, it does not relate `(m, d)` to `q.S`.

### 12.6 T-PP: the post-processing (complete type; target; not supplied)
```lean
def PPRel (raw : Module) (dsg : Design) (out : Module) (dout : Design) : Prop :=
  let top : (Module → Module) → Design → Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name == raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = Sparkle.IR.RefineCheck.mergeChecked m' ∧ dout = top Sparkle.IR.RefineCheck.mergeChecked d₁)
```
(first disjunct = `SPARKLE_NO_REGDEDUP` set, Elab.lean 5603; second = the default). The transport obligation is
```lean
def PPTransportStmt : Prop :=
  ∀ (I : ChildIface …) n raw dsg out dout, PPRel raw dsg out dout → ChildShipsI I n raw dsg → ChildShipsI I n out dout
```
(or its package-indexed form). Supplier survey: `G-TRANSPORT`/`G-LIFT` (Gen2Defs docs); `RefineCheck` / `ZeroWidth` correctness files were **not** read in this pass for a statement that preserves `ChildRunN`; "no supplier was found in the files read" is the only claim. `PPTransportStmt` is the same obligation as for the machine route (§9.3 T-PP). It is NOT claimed false or underivable.

### 12.7 Supplier table (after this section only the (P) rows have a planned supplier; no (S) row has one)
| part | supplier | status |
|---|---|---|
| `InvAt (D+1)` at `w₅` (tail end) — (P) | K-TAIL `legacyTail_keepsInv` from E-TAILCORE (Route 1) or the replay of its proof (Route 2), E-TRANS, E-STABLE | type fixed here; proof planned; whether `legacyTail` coincides with E-TAILCORE's subject unchecked (Route 1) |
| same worlds as the run data — (P) | K-RUNT `a4_inv_tail_machine_or_R4RunInvT` re-packs FB-3's single witness package | type fixed here; not written |
| projections to `R4RunInv`, `R4Run`, FB-3 extraction, FB-2 extraction | theorems in the check file | planned; not written |
| `InvAt D` at `w'` after `coreFinally` (T-FIN) | none looked at: `FinallyRestores` restores the saved maps and the depth, `keepBody` (Gen2Keep:54) is about `synthesizeFromConst` bodies, not `synthesizeCombinationalCore` | NOT in FB-4; open; `JQC O D w'` is the only fact at `w'` |
| `InvAt` at `w₇` (harness) | not needed for the tail's start/end | not in FB-4 |
| T-LEG (miss arm module meaning), T-SHAPE, T-STATE, T-INST, T-REACH — (S) | none found | open; §9.4 P-1…P-4 unchanged; need a legacy contract beyond the scalar-combinational fragment (L-2, D-LEGACY-SCOPE; not decided) |
| T-MEMO hit, K4 — (S) | `memoInv_hit` (generic) | needs `LM : RefLawsM` and `MemoInv … w₆`; D-MEMO-LAW undecided; no supplier of the invariant found |
| T-PP | none found | open |
| K-TSPLIT (hit-or-miss at `w₆`) | `unfold legacyTail` + `RunsTo.bind`/`ite` | type fixed (§12.5); not in FB-4's implementation scope |
| (a) side: memo insert after `some` | `A4MachineSideA` carries the run | not an `InvAt`/meaning supply; outside this section |

### 12.8 Checks planned for FB-4 (after this section is approved; nothing run)
New files only: `Tools/ShippingGen4FbTailInv.lean` (K-TAIL, `R4RunInvT`, K-RUNT), `Tests/Gen4/FbTailInvCheck.lean`, `lean_lib` entries in lakefile.lean; imports `Tools.ShippingGen4FbInv`. No edit of the built FB-1/2/3 files or of shared definitions.
1. TYPE: `legacyTail_keepsInv`, `R4RunInvT` (definition value), `a4_inv_tail_machine_or_R4RunInvT` against independent `Expected…` typed again in the check file (`checkExpected`, `==` first, logged `isDefEq` fallback). The `R4RunInvT` Expected is typed out in full from the `f07f4bf2` text of `R4RunInv` plus the one conjunct.
2. MUTANTS (rejections of mis-typed statements by signature/defeq, NOT semantic counterexamples): `R4RunInvT` with the `w₅` conjunct dropped; with `InvAt (D+1) w₅` replaced by `JQC (D+1) w₅`; with the conjunct at depth `D` instead of `D+1`; with `w₅` replaced by `w₆` (i.e. the FB-3 fact restated); `legacyTail_keepsInv` at `InvAt … D`; without `hC`; `a4_inv_tail_machine_or_R4RunInvT` without `hC`, or with `hI` replaced by `JQ`.
3. Projections proved as theorems: `R4RunInvT → R4RunInv`, `R4RunInvT → R4Run`, the extraction → FB-3 extraction, → FB-2 `a4_machine_or_R4Run`.
4. AXIOMS `⊆ {propext, Classical.choice, Quot.sound}`; `sorry` 0; no `native_decide`.
5. The clean issue-linked build is the coder's. A Pod build by this unit is not a clean build.

### 12.9 What this section does not claim
- It does not claim that any (S) statement is supplied, derivable or underivable. `InvAt` at `w₅` is a preservation fact; it is not the semantic guarantee of the legacy route or of the memo hit, and it does not discharge T-LEG, T-MEMO, K4, T-PP, T-FIN.
- `R4OutStmt`, `MemoHitStmt`, `LegMissStmt`, `PPTransportStmt`, `K-TSPLIT` are TARGET TYPES (text). They are not Lean in FB-4 and are not proved anywhere.
- A new law (`LM : RefLawsM` as a premise of `Laws`, a legacy contract for registers/instances) or a scope choice (D-LEGACY-SCOPE) is a user decision and is not taken here. If FB-4 finds a step that needs one, it stops and writes a decision document instead.
- Whole-Issue status unchanged: fallback / legacy / memo success routes, M4 and FG are not complete.

---

## 13. FB-4 implementation status and corrections to §12 (docs; Pod build only)

### 13.1 Implemented (K-TAIL, K-RUNT) — preservation only
- `Tools/ShippingGen4FbTailInv.lean` at `f8470c1c` (header sync `282998e0`, comment only): `legacyTail_keeps_generic` (the proof of `legacyTail_core` replayed on the NAMED program `legacyTail`, Route 2 of §12.2; Route 1 was not tried, so "legacyTail coincides with `synthesizeFromConst … false false ci isInst`" is still unchecked and not needed), `legacyTail_keepsInv` (K-TAIL, type of §12.2 as frozen), `R4RunInvT` (the `R4RunInv` body of `f07f4bf2` with ONE more leading conjunct `InvAt (D+1) w₅`), `a4_inv_tail_machine_or_R4RunInvT` (re-packs FB-3's single witness package; `InvAt` at `w₅` is `triple_runs` of K-TAIL on the tail run from `w₆`; no second existential).
- `Tests/Gen4/FbTailInvCheck.lean`: TYPE OK ×3 against an `Expected` typed again from the `ExpR4RunInv` text plus the one conjunct (the extraction conclusion is accepted by logged `isDefEq`, not syntactically); MUTANT REJECTED ×8 (`R4RunInvT` without the `w₅` conjunct / `JQC` instead of `InvAt` / depth `D` / `w₆` again; K-TAIL at `D`, without `hC`; extraction without `hC`, with `JQ` hypothesis) — these are rejections by signature/defeq, NOT semantic counterexamples; projections `R4RunInvT → R4RunInv → R4Run` and the two projected extractions are THEOREMS; AXIOMS standard three for 8 declarations.
- Explicit value-closure audit (type and body of every reached constant, structure name of raw `Expr.proj` included): none of the 8 new declarations reaches `Tools.ShippingMemo.*` (so no `RefLawsM`, no `MemoInv`, no `memoInv_hit`); controls with the SAME search: direct use of `memoInv_hit` flagged, use through two helpers in other namespaces flagged, a raw `Expr.proj` of `RefLawsM` flagged, an unrelated theorem and a built FB-3 theorem not flagged. The raw-proj control is on a bare expression, not on a declaration.
- Pod build only: `kjob lake build Tools.ShippingGen4FbTailInv` and `Tests.Gen4.FbTailInvCheck` exit 0 (713 jobs). Clean issue-linked build: fb5v-f4ea75ce exit 0 (713 jobs), scoped approved at f4ea75ce. No new law, no `Laws` field, no shared-definition edit, no `sorry`/`axiom`/`native_decide`.
- Not supplied by this: T-LEG, T-MEMO, K4, T-PP, T-FIN, `MemoInv`/`LM`; K-TSPLIT is not implemented. `InvAt (D+1) w₅` keeps the cache honest; it does not relate `(m, d)` to `q.S`.

### 13.2 Corrections to §12 (docs)
1. **§12.4–§12.6 are a roadmap, not an accepted complete type.** `R4OutStmt`, `MemoHitStmt`, `LegMissStmt`, `PPTransportStmt` still have omissions: `MemoHitStmt` has `MemoGetAt q.decl memo …` with `…` elided; `LegMissStmt` carries the premise "(the tail's memo read at its start world w₆ missed)" in prose, not as a term; `PPTransportStmt` has `ChildIface …` elided and an unfixed index. They were NOT approved as a type freeze (scoped approval at `6b41b373` covers §12.2/§12.3/§12.8 only). A complete type has to be written, reviewed and frozen before any Lean for them.
2. **`ChildIface` / `ChildShipsI` do not require `design.modules = []`.** In the gate Issue's file (`kjob/g4gate-fix:Tools/ShippingGen4Iface.lean`) `ChildIface ι` is a structure (`decl bsC outsC S`) and `ChildShipsI I n mc Dc` quantifies over designs `dsn` containing `Dc.modules`; there is no `modules = []` conjunct. The `design.modules = []` conjunct belongs to the older Prop `ChildIface c n b design` at `Tools/ShippingCallsGate.lean:233`, the interface of the leaf producers (`ChildFull.iface`, gate/slotless-machine children). The §12.4 sentence "`ChildIface` needs `dout.modules = []` (ShippingCallsGate.lean:233)" confused the two: it is wrong for `ChildIface.ofPkg` / `ChildShipsI`. What stays true: `dout.modules` is the `map` of `dsg.modules`; whether the fallback tail's design has empty `modules` is a question only for a producer that has to FEED a leaf-style (`ShippingCallsGate`) consumer, and it is not established here. (These gate-Issue names are not in this worktree's `Tools/`; the quotation is from the gate branch.)
3. **`Pkgs` and the same key.** `P : Pkgs ι dom` is a function `Name → Option (Pkg ι dom)`. From `P q.decl = some q` and `P c = some q'` with `c = q.decl`, `q = q'` is `Option.some.inj` after rewriting the key; it is not an extra "injectivity of `P` on names" assumption. The §12.5 sentence "injectivity of `P` on names … was not re-checked" is replaced by this. (`q'.decl = c` still has to come from `ShipsResI`'s `I.decl = c`, i.e. the memo invariant's content, which is not supplied.)

### 13.3 T-FIN: a nested candidate in the ClosingRun work (investigated; not used; no definition copied)
- Source: Issue `sparkle-gen5-dg-closingrun`, agent `g5cr-r2`, branch `kjob/g5cr-r2` (head `6f3c8ee5` when read; the Issue is that agent's, not changed here). `Tools/ShippingGen5ClosingRun.lean` has `stop_of_run`: `h1 : 1 ≤ dv w`, `hKI : ChildKeepsInv L P Reach (dv w + 1)`, `hst : InvAt … (dv w) w`, `hrun : RunsTo (synthesizeCombinationalCore X [] false) … w (raw, D) w'` ⊢ `InvAt … (dv w) w'`, proved by `triple_runs (core_tripleAInv L P Reach hA (dv w) h1 X (fun … => keepBody L P Reach (dv w + 1) hKI …)) hst hrun`. `core_tripleAInv` is at `Tools/ShippingGen2KeepChild.lean:133` and `keepBody` at `Tools/ShippingGen2Keep.lean:54`; `Tools/ShippingGen2KeepChild.lean` is on that lineage and is not in this worktree.
- What it would give a fallback proof: `InvAt D w'` of the WHOLE core run, for `1 ≤ D`, directly from `hI`, `hC` and `hr` — NOT through `InvAt (D+1) w₅` and a `coreFinally` split (§12 "What must not be confused"). It would therefore supply the T-FIN row of §12.7 for `D ≥ 1`. It does not use `R4RunInvT`.
- Open: (i) the depth-0 case (`core_tripleAInv` requires `1 ≤ D`; for `D = 0` the cache clear is excluded and the ClosingRun freeze marks it unsupplied); (ii) integration: this tree would have to import the ClosingRun lineage (`ShippingGen2KeepChild`) or `stop_of_run` would have to be consumed through that Issue's own export — not decided here, no definition is copied or re-stated in this unit; (iii) its premises (`ChildKeepsInv … (dv w + 1)`, `dv w` as the depth read at `w`) must be matched with `R4OutStmt`'s `InvAt L P Reach D w`, `ChildKeepsInv … (D + 1)` (the `D` of `R4OutStmt` versus `dv w`); this unit only compared the printed statements, nothing was built across the two lineages.
- Status: candidate supplier for T-FIN at `D ≥ 1`, unbuilt in this tree. It is a preservation fact; it says nothing about the meaning of the module.

### 13.4 Still unsupplied / unapproved
T-LEG (miss arm meaning), T-MEMO hit and K4, `MemoInv`/`LM : RefLawsM` (new-law candidate D-MEMO-LAW, undecided), T-PP, K-TSPLIT, T-SHAPE/T-STATE/T-INST/T-REACH. No new law, no scope change, no FG/guarantee change was made or assumed. Whole-Issue status unchanged: fallback / legacy / memo success routes, M4 and FG are not complete.

---

## 14. FB-6: T-FIN for `D ≥ 1` by consuming the ClosingRun `stop_of_run` — complete types (rev8; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only, committed BEFORE any Lean. No new law, no `Laws` field, no shared-definition edit (this unit edits none of `Tools/ShippingGen2Defs.lean`, `ShippingGen2T1*`, `Elab*.lean`; the ClosingRun lineage changes `ShipsRes` in `ShippingGen2Defs.lean` itself, see §14.3), no change of FG or of a guarantee. T-FIN here is a **preservation** fact (P): the heap invariant `InvAt` holds again at the END `w'` of the whole core run. It says nothing about what `(m, d)` computes.
- **What this section reads (not changed).** `kjob/g5cr-r2` at `6f3c8ee5` (Issue `sparkle-gen5-dg-closingrun`, another owner; clean build `crv-6f3c8ee5` exit 0, reviewer confirmation pending when this unit started). `Tools/ShippingGen5ClosingRun.lean` exports `Tools.ShippingGen5ClosingRun.stop_of_run` (quoted in §13.3). Depth 0 is NOT covered by it (`h1 : 1 ≤ dv w`).

### 14.1 Row T-FIN (D ≥ 1) — complete type
```lean
theorem tFin_stop {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w') :
    InvAt L P Reach D w'
```
Premises are exactly those of `R4OutStmt` (§12.4) / the K-RUNT extraction (`hA`, `hI`, `hC`, `hr`) plus `h1`. `D` is the `D` of `InvAt L P Reach D w`: `hI` contains `JQ … D w`, whose last conjunct is `dv w = D`, so no separate `dv w = D` premise is needed (this resolves open item (iii) of §13.3 for the matching of `dv w` against `R4OutStmt`'s `D`).

Planned proof (consumption, no restatement): `obtain ⟨⟨⟨_, _, hD⟩, _⟩, _⟩ := hI`-style extraction of `hD : dv w = D` from `hI`, rewrite `D := dv w`, then `exact Tools.ShippingGen5ClosingRun.stop_of_run L P Reach hA h1 hC hI hr`. If the rewrite does not go through, the step is reported "not closed in this attempt".

Companion (same run, no second existential):
```lean
theorem a4_inv_tail_fin  -- binders as K-RUNT (§12.3) plus (h1 : 1 ≤ D)
    … (h1 : 1 ≤ D) (hA : AdmCtx L.O.quiet mctx cctx)
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       R4RunInvT L P Reach mctx cctx D declName shape m d w w') ∧ InvAt L P Reach D w'
```
Proof: `⟨a4_inv_tail_machine_or_R4RunInvT … hr entry, tFin_stop … hr⟩`. Both conjuncts are about the SAME `hr` and the SAME `w'`; `InvAt D w'` is NOT derived from the `w₅` fact (§12 "What must not be confused" stands) and the (a)/(b) split is not used by it.

### 14.2 How `stop_of_run` is consumed
- `import Tools.ShippingGen5ClosingRun` in the new file; the single use is the application `Tools.ShippingGen5ClosingRun.stop_of_run L P Reach hA h1 hC hI hr` (with `dv w` identified with `D` as above). **No definition, statement or proof of `stop_of_run`, `core_tripleAInv` or `keepBody` is copied or re-stated.** The check asserts that `stop_of_run` is in the value-closure of `tFin_stop` (consumed, not re-proved) — this is a check of what the term uses, not of semantics.
- Depth 0 (`D = 0`) stays UNSUPPLIED: `h1 : 1 ≤ D` is a premise; no theorem here has a conclusion at `D = 0`, and no statement says depth 0 is impossible or underivable. The reason (cache clear at the depth-0 `coreFinally`) is the ClosingRun freeze's, not re-derived here.

### 14.3 Integration (decision for this unit)
Chosen: a LOCAL, non-pushed `git merge --no-ff kjob/g5cr-r2` (`6f3c8ee5`) into `kjob/g4fb-fb6`, committed after this section. Reason: the file needs `Tools/ShippingGen5ClosingRun.lean` and its imports (`ShippingGen5RunReads`, `ShippingGen5T1ND`, `ShippingGen2Served`, `ShippingGen2KeepChild`, …) in the tree; the alternative (waiting for the closingrun Issue's approval and an integration branch) would leave the T-FIN row unbuilt. Consequences recorded, not hidden:
1. The only textual conflict is `lakefile.lean` (both sides only ADD `lean_lib` blocks); resolved by keeping both, no entry removed or changed.
2. The merge brings the closingrun lineage's edit of the shared `Tools/ShippingGen2Defs.lean`: `ShipsRes` gains a third conjunct `InstClosed r` (and `TopShips`' `rst`/`clk` premises are conditional). Those are that lineage's changes under its own review; this unit makes no edit to the file. The FB-1…FB-4 files do not mention `ShipsRes` by name; whether they still build on the merged tree is established only by the build, not assumed.
3. If the closingrun Issue is changed in review, this unit's merge commit must be redone on its new head; the merge is a local convenience, not an acceptance of that lineage.
4. Pod build of the merged tree is not a clean issue-linked build; the coder runs that.

### 14.4 Audit improvement (new Check; existing `FbTailInvCheck` unchanged)
The value-closure detector of `FbTailInvCheck` does `let some ci := env.find? c | continue`: a reached constant missing from the environment is skipped silently, so "no `Tools.ShippingMemo.*` reached" could hold only because a branch was not followed. The new Check's detector instead records every reached constant that `env.find?` does not resolve in a `missing` list, prints its count, and **fails** if the count is non-zero for a declaration under audit (the result would be "not established", never "no reference"). Controls with the same detector: (a) a root that is not in the environment → `missing` non-empty → the assertion fails (caught and logged as the expected control outcome); (b) the existing flagged fixtures (direct, two-helper indirect, raw `Expr.proj`) are still flagged; (c) unrelated and built FB-3 theorems are not flagged and have `missing = 0`. Opaque constants and constants without a body keep being counted (`noBody`, `opaques`), as before.

### 14.5 Checks planned (after approval; nothing run)
New files only: `Tools/ShippingGen4FbFin.lean` (`tFin_stop`, `a4_inv_tail_fin`), `Tests/Gen4/FbFinCheck.lean`, `lean_lib` entries in `lakefile.lean`.
1. TYPE: `tFin_stop`, `a4_inv_tail_fin` against `Expected…` typed again in the check file (`checkExpected`); `a4_inv_tail_fin` also projects (theorem) to the K-RUNT statement.
2. MUTANTS (one well-typed change each, rejected by the SAME comparator; signature/defeq rejections, NOT semantic counterexamples): `tFin_stop` without `h1`; with `hC` at `D` instead of `D + 1`; with conclusion at `D + 1`; with conclusion at `w` instead of `w'`; `a4_inv_tail_fin` without the `InvAt D w'` conjunct; without `h1`.
3. AXIOMS ⊆ {propext, Classical.choice, Quot.sound}; `sorry` 0; no `native_decide`.
4. Value closure (§14.4): no `Tools.ShippingMemo.*`, `missing = 0`, `stop_of_run` reached, with the controls above.
5. Build record: clean issue-linked build `fb14v-67756b3c` exit 0 (812 jobs, dirty=false), approved by the reviewer at 67756b3c with a limited scope (PPRel = real postpass top-name condition, `dropZeroWidth`, optional `mergeChecked`); reviewer note: the unknown-name type fixture was root-direct, not root → helper-type-only (addressed in FB-15).

### 14.6 What this section does not claim
- Not a T1 / FG / M5 / M4 completion, and not an acceptance of the ClosingRun lineage. `stop_of_run` is consumed as published by `6f3c8ee5`; its own review is that Issue's.
- T-FIN depth 0 is unsupplied. T-LEG, T-MEMO, K4, `MemoInv`/`LM`, T-PP, K-TSPLIT, T-SHAPE/T-STATE/T-INST/T-REACH remain unsupplied (§13.4); §12.4–§12.6 remain a roadmap. No new law, scope change or guarantee change is made or assumed.

---

## 15. FB-7: addenda to §14 before any Lean — full K-RUNT telescope, the `h1` position, integration record, target manifest (rev9; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only, committed BEFORE the new Lean files. Base = `5b668ab7` (§14 scoped approved as a DESIGN; not an approval of production, of a new law or of a guarantee change). §14.1/§14.2/§14.4/§14.5 stand; this section only (a) expands the elided telescope, (b) fixes the position of `h1`, (c) records the integration that was performed and what it brought in, (d) fixes the target manifest for the coder's clean build. OPEN and NOT claimed: depth 0, T-LEG, T-MEMO, K4, T-PP, memo law, K-TSPLIT; Issue / M4 / FG are not complete.

### 15.1 The companion `a4_inv_tail_fin`, with the telescope of §14.1 written out
The `…` of §14.1 stood for the binders of `a4_inv_tail_machine_or_R4RunInvT` (K-RUNT, `Tools/ShippingGen4FbTailInv.lean`, `4a1c7bc4`/`f8470c1c`, §12.3). Full text (binders in K-RUNT order; `h1` is the ONE added binder, §15.2):
```lean
theorem a4_inv_tail_fin {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D)
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       R4RunInvT L P Reach mctx cctx D declName shape m d w w') ∧ InvAt L P Reach D w'
```
and `tFin_stop` of §14.1 keeps its binder order (`hA`, implicit `X D w w' raw dsg`, `h1`, `hC`, `hI`, `hr`). The `R4RunInvT` that occurs in the conclusion is the built definition, whose body (the K-RUNT conjunct list, copied from `Tools/ShippingGen4FbTailInv.lean` lines 96–139 at the base; this is the text the Expected of the new Check is typed against again, not imported from the built check) is:
```lean
def R4RunInvT (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))
```
The companion's proof is `⟨a4_inv_tail_machine_or_R4RunInvT L P Reach hA hI hC hr entry, tFin_stop L P Reach hA h1 hC hI hr⟩`: both conjuncts are about the same `hr`, `w`, `w'`; no witness of the `R4RunInvT` package is identified with anything in `tFin_stop`.

### 15.2 The position of `h1`
`h1 : 1 ≤ D` is bound AFTER `D` (and after every implicit/instance binder that does not mention hypotheses) and BEFORE `hI` — in `tFin_stop` directly after the implicit block and before `hC`/`hI` (the §14.1 order), in `a4_inv_tail_fin` directly before `hI`. The reason: `D` is the depth read from `hI` (`InvAt … D w` contains `JQ … D w`, whose last conjunct is `dv w = D`; `InvAt = JQC ∧ CacheShips`, `JQC = JQ ∧ CacheInvA`, `JQ = quiet ∧ sv = some synthesizeChild ∧ dv w = D`, so `dv w = D` is `hI.1.1.2.2`), and `h1` is a statement about that `D`. The Check does not rely on a name or a comment for this: the `Expected…` declarations are typed independently with `h1` at that position and compared with `checkExpected` (telescope comparison, binder by binder), and a mutant with `h1` moved after `hI` (everything else equal) is compared by the same comparator and must be rejected. The mutant is a signature/defeq rejection, not a semantic counterexample (the two orders are logically equivalent).

### 15.3 Integration performed (local; not pushed)
- `git merge --no-ff 6f3c8ee5` (pin = `6f3c8ee5`, `DG-CLOSINGRUN: header counts (comment only)`, branch `kjob/g5cr-r2`) into `kjob/g4fb-fb7` (base `5b668ab7`); merge commit `b81f4f09`. The merge base is `d0ddc50b`; no history was rewritten.
- **Conflict:** only `lakefile.lean`; both sides append `lean_lib` blocks at the end of the file. Resolution: keep all blocks of both sides (ours: `Tools/Tests ShippingGen4Fb{Tail,R4,Inv,TailInv}`; theirs: `Tools.ShippingGen2T1`, `Tests.Gen3.T1Check`, `Tools.ShippingGen5ClosingRun`, `Tests.Gen5.ClosingRunCheck` and the others of that lineage), conflict markers removed, nothing deleted or edited. Count check: merge base 1192 `lean_lib`, ours 1200 (+8), theirs 1208 (+16), result 1216 = 1192 + 8 + 16; no duplicated `lean_lib` name.
- **What the merge brings in (48 files, `git diff --stat b81f4f09^1 b81f4f09`):**
  1. `Tools/ShippingGen2Defs.lean` (shared definition file; modified by that lineage, not by this unit): `InstClosed (r : Res) : Prop` is NEW (every module of the result's design is instantiated by name in the body of the top or of some module of its design); **`ShipsRes` gains a third conjunct `InstClosed r`** (`RealChildA ∧ (∃ q n, …ChildShips…) ∧ InstClosed r`); **`TopShips`**' `rst` / `clk` premises become conditional (`"rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0`, same for `clk`; R-G of `scripts/gen2/TOP_CONTRACT_REVISION.md` §2). Consumers changed with it: `ShippingGen2FitChain`, `Leaf`, `MemTop`, `OneOut`, `OneOutTop`, `OneOutTopO`, `SlotlessLeaf`, `TopNC`, `TopVacuity`, `ShippingGen3Arity`, `ShippingGen5T2Conn`, `ShippingGen5T2Tie`, `Tests/Gen2/{PkgCompat,S5Check,TopNCCheck}`.
  2. New Lean (that lineage): `Tools/ShippingGen2{InstKeep,KeepChild,KidsInst,PostFacts,PostFactsProof,Served,ServedRun,T1,TopClkIn,TopContract}`, `Tools/ShippingGen5ClosingRun` (contains `stop_of_run`), `Tests/Gen3/{InstKeepCheck,PostFactsCheck,ServedCheck,T1Check}`, `Tests/Gen5/ClosingRunCheck`.
  3. Documents (that lineage): `scripts/gen2/*` (GPOST_*, KEEPCHILD_*, SERVED_*, T1_CONNECT_RESULT, TOP_CTRL_FREEZE, TOP_CONTRACT_REVISION, GEN2_DEFS.lean.txt), `scripts/gen3/*`, `scripts/gen5/DG_CLOSINGRUN_FREEZE.md`.
  - Of the FB-1…FB-4 Lean files none mentions `ShipsRes`, `InstClosed` or `TopShips` by name (grep); whether they still build is established only by the build. `Tools.ShippingGen4FbR4` does not have `ShippingGen2Defs` in its import closure.
- This unit edits none of `Tools/ShippingGen2Defs.lean`, `T1Hyp*`, `Elab*.lean`, `Tools/ShippingGen2*` on this lineage; the merge is a local convenience and not an acceptance of that lineage (§14.3 items 3–4 stand). If `kjob/g5cr-r2` changes after review, this merge is redone.

### 15.4 Plan for the new Check, positions fixed
`Tests/Gen4/FbFinCheck.lean`: (1) TYPE: `ExpTFinStop`, `ExpA4InvTailFin` typed independently (full `∀`, `h1` at the §15.2 position, `R4RunInvT` written with its §15.1 body via a local `ExpR4RunInvT` copy typed again); (2) the §14.5 mutants plus `h1` after `hI` (rejected by the same comparator); (3) projection `a4_inv_tail_fin → K-RUNT statement` and `→ tFin_stop` as theorems; (4) AXIOMS standard three; (5) value closure per §14.4 with `missing` list: no `Tools.ShippingMemo.*`; `missing = 0` required (fails otherwise); `stop_of_run` reached; controls (a) absent root → failure caught as expected, (b) flagged fixtures (direct, two-helper, raw `Expr.proj`) flagged, (c) unrelated and FB-3 theorem not flagged with `missing = 0`; also a control that a theorem which RE-PROVES the keep without `stop_of_run` does not reach it. `missing` counts constants that `env.find?` does not resolve; these never silently pass. missing (`env.find?` absent) ⇒ fail, i.e. "not established", never "no reference".

### 15.5 Target manifest (for the coder's clean issue-linked build at the exact integration SHA)
[Record fix after review of 8c7e5ff6: the Tier-B list below is renumbered 8–48 (it originally repeated number 7), so the manifest has **48 modules** = 7 + 41. The build was run as **one multi-target build** (not one target per build) with **47 target arguments**: `Tests.Gen5.EnvCheck` (#48) was not passed; it is built through `Tests.Gen5.EnvRCheck`. All 48 modules have Built/Replayed lines in log `fb7w-8c7e5ff6` (exit 0, 1090 jobs, scoped approved at 8c7e5ff6).]
The exact SHA to build is the commit that contains this section AND the Lean files of §15.4 (recorded in the Issue note; do not build an earlier SHA). Order: new → FB → ClosingRun → Defs-affected.
1. `Tools.ShippingGen4FbFin`
2. `Tests.Gen4.FbFinCheck`
3. `Tests.Gen4.FbTailInvCheck` (existing FB checks on the merged tree; imports `ShippingGen2Defs`, whose `ShipsRes` changed)
4. `Tests.Gen4.FbInvCheck`
5. `Tests.Gen4.FbTailCheck`
6. `Tests.Gen4.FbR4Check` (no `ShippingGen2Defs` in its closure; built as a regression control)
7. `Tests.Gen5.ClosingRunCheck` (the consumed lineage on the merged tree)
Tier B (affected by the `ShippingGen2Defs` / `ShipsRes` / `TopShips` change on the merged tree; these are that lineage's checks, listed so that a failure caused by the merge is separated from a failure of this unit; computed from the `import` graph: every `Tests.*` module whose import closure contains a modified module of §15.3 item 1):
8. `Tests.Gen2.AdaptInstance`
9. `Tests.Gen2.LeafInstance`
10. `Tests.Gen2.CallDecInstance`
11. `Tests.Gen2.TopNCCheck`
12. `Tests.Gen2.SlotlessCheck`
13. `Tests.Gen2.MemParentInstance`
14. `Tests.Gen2.S4StageACheck`
15. `Tests.Gen2.QuantInstance`
16. `Tests.Gen2.PkgCompat`
17. `Tests.Gen2.PMem4Check`
18. `Tests.Gen2.DataBridgeCheck`
19. `Tests.Gen2.S4StageBCheck`
20. `Tests.Gen2.OneOutCallField`
21. `Tests.Gen2.SlotlessLeafInstance`
22. `Tests.Gen2.U0Check`
23. `Tests.Gen2.S3GroupCheck`
24. `Tests.Gen2.S4FitCheck`
25. `Tests.Gen2.S5Check`
26. `Tests.Gen3.ArgSupplyCheck`
27. `Tests.Gen3.PortWidthsPrepCheck`
28. `Tests.Gen3.PostFactsCheck`
29. `Tests.Gen3.ServedCheck`
30. `Tests.Gen3.ChildPortWidthsCheck`
31. `Tests.Gen3.ArgSupply3Check`
32. `Tests.Gen3.ArgWidthCheck`
33. `Tests.Gen3.T1Check`
34. `Tests.Gen3.ArgWidthSrcCheck`
35. `Tests.Gen3.SlotlessPortWidthsCheck`
36. `Tests.Gen3.ArgSupply2Check`
37. `Tests.Gen3.ArityCheck`
38. `Tests.Gen3.ArgSupply4Check`
39. `Tests.Gen5.T2DecCheck`
40. `Tests.Gen5.EnvQCheck`
41. `Tests.Gen5.T1NDCheck`
42. `Tests.Gen5.T2TieCheck`
43. `Tests.Gen5.RunReadsCheck`
44. `Tests.Gen5.T2OutTyCheck`
45. `Tests.Gen5.T2ConnCheck`
46. `Tests.Gen5.T2RangeCheck`
47. `Tests.Gen5.EnvRCheck`
48. `Tests.Gen5.EnvCheck`
Not claimed by building these: no acceptance of any lineage, no Issue completion.

### 15.6 What this section does not claim
- Nothing here is Lean-checked. Depth 0, T-LEG, T-MEMO, K4, T-PP, memo law, K-TSPLIT remain unsupplied; §12.4–§12.6 remain a roadmap. T-FIN (D ≥ 1) is preservation only. Mutants are signature/defeq rejections, not semantic counterexamples. No new law, `Laws` field, shared-definition edit by this unit, FG or guarantee change.

---

## 16. FB-7 implementation status (docs; Pod build only)
- `Tools/ShippingGen4FbFin.lean` (`tFin_stop`, `a4_inv_tail_fin`) and `Tests/Gen4/FbFinCheck.lean` at `b103bd90` (header-sync commit follows, comments only), `lean_lib` entries appended to `lakefile.lean`. Types as §14.1 / §15.1 with `h1` at the §15.2 position. `tFin_stop` is `hI.1.1.2.2 : dv w = D`, `subst`, then the single application of `stop_of_run`; no definition or proof of `stop_of_run`/`core_tripleAInv`/`keepBody` is copied. No `sorry`/`axiom`/`native_decide`, no new law or field.
- Pod builds (exit 0, each alone, NOT clean issue-linked builds): `Tools.ShippingGen4FbFin` (758 jobs), `Tests.Gen4.FbFinCheck` (764: TYPE OK ×2, the companion accepted by logged `isDefEq` against the independent `ExpR4RunInvT2` copy; MUTANT REJECTED ×8 incl. `h1` after `hI`, signature/defeq rejections not semantic counterexamples; REACH: no `Tools.ShippingMemo.*`, `missing = 0`, `stop_of_run` reached by `tFin_stop`; controls: absent root → missing 1 and assertion failed as expected, direct/indirect/raw-proj flagged, unrelated and FB-3 theorem not flagged with missing 0, consumer sees `stop_of_run` and the FB-3 theorem does not; AXIOMS standard three ×4), and on the merged tree `Tests.Gen4.FbTailInvCheck` (713), `FbInvCheck` (709), `FbTailCheck` (703), `FbR4Check` (353), `Tests.Gen5.ClosingRunCheck` (755). The Tier-B targets of §15.5 were NOT built by this unit.
- Not supplied: depth 0, T-LEG, T-MEMO, K4, T-PP, memo law, K-TSPLIT. T-FIN (D ≥ 1) is a preservation fact. The clean issue-linked build at the exact SHA recorded in the Issue note is the coder's. Issue / M4 / FG are not complete.

---

## 17. FB-8: survey of the unsupplied rows from existing theorems, and the next unit (K-TSPLIT) — complete types (rev10; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only. Base `3c45dcbf` (record fix: §15.5 is 48 modules, built as ONE multi-target build with 47 target arguments, `Tests.Gen5.EnvCheck` via `EnvRCheck`; log `fb7w-8c7e5ff6` exit 0, 1090 jobs, scoped approved at `8c7e5ff6`). No new law, no `Laws` field, no TRUSTED boundary, no shared-definition or compiler edit, no FG/guarantee change, `stop_of_run` untouched. "Not found" below means "this survey found no supplier / route in the files read"; it is NOT a claim that a row is false or underivable. Mutants in the planned check are signature/defeq rejections, not semantic counterexamples.
- Method: `grep` of `Tools/` for the names of §12.4–§12.6 (`outer_miss`, `memoInv_*`, `legacy_entry_*`, `PPRel`-shaped `hpost`, `dropZeroWidthModule`, `mergeChecked`) and reading of the statements (not proofs) listed below.

### 17.1 Survey (row → real names and types → verdict)
| row | existing names (file) | what they state | gap to the §12.4–§12.6 type | verdict |
|---|---|---|---|---|
| depth 0 of T-FIN | `core_tripleAInv` (`ShippingGen2KeepChild`) requires `1 ≤ D`; `stop_of_run` (ClosingRun) inherits `h1 : 1 ≤ dv w` | `InvAt D w'` for `D ≥ 1` | at `D = 0` the cache clear (`coreFinally` with all seven maps `{}`, the `D = 0 → sf = {} ∧ …` conjunct of `R4RunInvT`) is part of the run; `JQC L.O 0 w'` is the only fact at `w'` in this tree | **unsupplied / no route found** in this survey |
| T-MEMO, depth 0 (outer miss) | `outer_miss` (`Tools/ShippingLegacySemMemoWalk.lean:495`), `outer_reset_reaches` (`Tools/ShippingMemoLaws.lean:160`), `memo_miss_after_reset` (superseded sketch with its own `MemoLaws`) | in a returning core run from `L.dval w = 0 ∧ L.quiet w`, THIS run's memo read returns a map with no entry; the premises include `(L : RefLawsM mref cref)` | `Laws` has fields `O`, `T` only; `RefLawsM extends RefLaws` and adds `mval`, `memoGet/Set/Modify`, `distinct`, `memoFrame` (a larger trust base). On the existing route examined here, supplying `outer_miss` to an R4 statement about `Laws` needs `RefLawsM` as a new premise or a field; this survey did not prove that every route needs it. This is the open D-MEMO-LAW (§5.6, §7) | **on the route examined: would need a user decision (new law); not introduced here.** The supplier exists in the repo; the premise is the issue |
| T-MEMO, nested (K4) | `memoInv_hit`, `memoInv_write`, `memoInv_of_empty/same/reset/frame/read` (`Tools/ShippingMemoInv.lean`), `ArmObligations`, `MemoSound` (statements only, `:152/:209`; the only other mention is `Tests/Compiler/LegacySemMemoTest.lean`) | `MemoInv LM Φ w := ∀ n r, (LM.mval w).get? n = some r → Φ n r` and its preservation laws | all over `RefLawsM`; `MemoInv … w₆` at a nested tail start has no supplier (K4 "memo names ⊆ `childCache` names ∪ {top}" is a reading of the source, not a theorem) | **unsupplied; the statements read are all over `RefLawsM` (no other route was examined)** |
| T-LEG | `legacy_entry_walk_in` (`ShippingLegacySemEntryIn.lean:47`, MReturns form), `legacy_entry_walk` (`ShippingLegacySemEntryWalk.lean:133`), `legacy_entry_walk_at`/`_start` (`…MemoWalk.lean:93/227`, RunsTo form, needs `RefLawsM`), `legacy_entry_output`, `legacy_entry_output_walked`, `proj_entry_output_outer` | meaning of the legacy arm for the scalar-combinational / projection classes, with `hmach : machineShape? … = none` | in R4 the machine attempt ran first and the tail starts at `w₆` after `closeInsts` (§12.5); the `…_at` forms are about `synthesizeFromConst` from a fresh world, not about `legacyTail` from `w₆`; `LegacyDom`/`Value` are scalar-combinational (U4); no register/instance contract | **unsupplied / no route found** to `LegMissStmt` (§12.5) |
| T-PP | `refineCheck_transfer`, `refineCheck_ports` (`ShippingRefineSoundness.lean:1039/1067`: run-level transfer and port equality for `refineCheck m o = true`), `mergeChecked_cases`, `mergeChecked_ports` (`Sparkle/IR/RefineCheck.lean`), `dropZW_wires` (`ShippingOutsExtractedParts`), consumers with `hpost : b = dropZeroWidthModule M ∨ b = mergeChecked (dropZeroWidthModule M)` (`ShippingCallSelf`, `ShippingCallsChildPorts`, `ShippingCallWidthsChildRealA`) | port/wire/body facts relating `b` to `M` | no statement `ChildShipsI I n raw dsg → ChildShipsI I n out dout` (`PPTransportStmt`); also `dout` is `top …` on the design (§12.4), and the `hpost` consumers state only module-level facts (`b.body = M.body`, wires, ports) | **unsupplied / no route found** to `PPTransportStmt` |
| K-TSPLIT | `RunsTo.bind`, `RunsTo.ite` (`ShippingEntrySoundness.lean:946/957`), `runsTo_ite_pos/neg`, `runsTo_pure` (`MemoWalk.lean:69-86`), `RunsTo.pure_world` (`ShippingChildInv.lean:874`); the model proof is the memo-read prefix of `legacy_entry_walk_at` | structural inversions of `bind`/`ite`/`pure` | none: the statement is about the named program `legacyTail` (`ShippingMachineOutcomeA.lean:54`) and mentions no `mval`, no `RefLawsM`, no law | **proof plan at freeze time (22147275): expected to be supplied from existing parts.** Implemented in `777f89cc` (see §18); the plan itself was not evidence |

### 17.2 Selection and reason
First unit: **K-TSPLIT** (FB-9). Reasons: (1) it is the only row of §17.1 whose proof uses only existing structural lemmas, with no law, no `RefLawsM`, no field of `Laws`; every other row stops, on the routes read, at `RefLawsM` (user decision D-MEMO-LAW) or at a statement with no supplier found; (2) it is the hinge of §12.5 (T-LEG-miss and T-MEMO-hit are the two arms; `LegMissStmt`'s premise "the tail's memo read at `w₆` missed" becomes a term only once the split exists with the same `w₆`); (3) it consumes the already-built `R4RunInvT` package unchanged. It is a structural fact about control flow: it does not say anything about the meaning of `(m, d)` and does not advance (S).

### 17.3 K-TSPLIT: complete types (target; each hypothesis and binder written out)
Namespace `Tools.ShippingGen4FbSplit` (new file `Tools/ShippingGen4FbSplit.lean`); same `variable`/`open` context as `Tools/ShippingGen4FbTailInv.lean` (`mctx cctx mref cref`, `TranslateFn`, `Res := Module × Design`).
```lean
theorem legacyTail_hit_or_miss
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {translate : TranslateFn} {logProf : String → IO Unit} {declName : Name} {ci : ConstantInfo}
    {w w₅ : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : RunsTo (legacyTail translate logProf declName [] false ci) mctx mref cctx cref w (m, d) w₅) :
    ∃ (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) (w₁ : Void IO.RealWorld),
      RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w memo w₁ ∧
      (memo.get? declName = some (m, d) ∨ memo.get? declName = none)
```
(`symbolicMode := false`, `parameters := []` fixed, as in `R4RunInvT`.) The read is the FIRST action of `legacyTail` (its `if !symbolicMode` arm), so it runs at the start world `w`. The hit arm records that the returned pair IS the cached entry (`return cached`); no equation `w₅ = w₁` is claimed (the profile log between them is a lifted `IO` action whose world effect is not constrained here). The miss arm records only `memo.get? declName = none`; the build that follows is not named.
```lean
theorem r4RunInvT_tail_hit_or_miss
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {D : Nat} {declName : Name} {shape : MachineShape}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (h : R4RunInvT L P Reach mctx cctx D declName shape m d w w') :
    ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (w₅ w₆ : Void IO.RealWorld)
      (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) (w₁ : Void IO.RealWorld),
      InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
      RunsTo (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false
        (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv) (structEnv tenv)))
        mctx mref cctx cref w₆ (m, d) w₅ ∧
      RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w₆ memo w₁ ∧
      (memo.get? declName = some (m, d) ∨ memo.get? declName = none)
```
The `w₅`, `w₆`, `tenv`, `pb`, `ci` are those of the `R4RunInvT` package (destructure `h`, apply `legacyTail_hit_or_miss` to its tail-run conjunct, repackage); no second existential for the worlds, so the read is at the package's `w₆`. The `InvAt` conjuncts are copied from `h` (they are the existing FB-4 facts, not new).

Proof plan: `unfold legacyTail at h`; the `if !false = true` arm is taken (`runsTo_ite_pos`); `RunsTo.bind` gives `memo w₁` for the read and a remaining program `f memo`; `cases hc : memo.get? declName`: `none` → `Or.inr`; `some c` → the `if let` takes the hit arm, `bind` of the `logProf` lift then `pure cached`; `RunsTo.pure_world`/`runsTo_pure` give `(m, d) = c`, hence `Or.inl`. If the lifted `logProf` bind needs a lemma that is not a one-liner, the unit reports "not closed in this attempt" with the failing step (not a claim that the split is false).

### 17.4 Planned checks (new files only; nothing run)
Files: `Tools/ShippingGen4FbSplit.lean`, `Tests/Gen4/FbSplitCheck.lean`, two `lean_lib` entries in `lakefile.lean`; imports `Tools.ShippingGen4FbTailInv` (and `Tools.ShippingLegacySemMemoWalk` only if the `runsTo_*` helpers are reused; its closure is expected to contain `Tools.ShippingMemo.*`, so the REACH audit below decides — if it does, the helpers are re-proved locally in the new file instead).
1. TYPE: both theorems against `Expected…` typed again in the check file from §17.3 (not copied from the Lean file), same reducible comparator (`==` then logged `isDefEq`) for the positive and every negative case.
2. MUTANTS (signature/defeq rejections, NOT semantic counterexamples), each must be REJECTED by the same comparator: hit arm with a free pair `some (m', d')`; miss arm `= some _`; `symbolicMode := true`; read located at `w₅` instead of `w`/`w₆`; dichotomy replaced by the hit arm only; dichotomy without the read; `InvAt` at depth `D` instead of `D + 1`; `w₆` replaced by a fresh existential in the corollary.
3. REACH/closure audit: the value closure of both theorems (type and body, raw `Expr.proj` structure names included) contains no `Tools.ShippingMemo.*` (so no `RefLawsM`, `MemoInv`, `outer_miss`); an unknown constant (not found in the environment) FAILS the audit (it is counted in `missing`, which must be 0); controls with the same search: a fixture using `outer_miss` is flagged, a fixture using `memoInv_hit` through a helper is flagged, an absent root gives `missing ≥ 1` and the assertion fails as expected, an unrelated theorem is not flagged.
4. AXIOMS `⊆ {propext, Classical.choice, Quot.sound}` for both theorems; `sorry` 0; no `native_decide`.
5. Counts in the report are the actual numbers of checks that ran (no summary line counted). The clean issue-linked build is the coder's; a Pod build by this unit is not a clean build.

### 17.5 What this section does not claim
- No row of (S) is supplied: T-LEG, T-MEMO (depth 0 `outer_miss` exists but needs `RefLawsM`; nested K4), T-PP, depth 0 of T-FIN stay unsupplied; the split does not relate `(m, d)` to `q.S`.
- It does not say `RefLawsM` cannot be obtained from `Laws`; it says this survey found no such derivation. Whether to add it is the user's decision (D-MEMO-LAW); a decision document is not written here because K-TSPLIT does not need it.
- Whole-Issue status unchanged: fallback / legacy / memo success routes, M4 and FG are not complete.

---

## 18. FB-9 implementation status (docs; Pod build only)
- `Tools/ShippingGen4FbSplit.lean` (`legacyTail_hit_or_miss`, `r4RunInvT_tail_hit_or_miss`) and `Tests/Gen4/FbSplitCheck.lean` at `777f89cc` (header-sync commit follows, comments only); two `lean_lib` entries appended to `lakefile.lean`. Types exactly as §17.3; no extra premise was needed, no definition shared or built file touched. Proof: `unfold legacyTail`, `if_pos` on `(!false) = true`, `RunsTo.bind` for the read, `split` on the `match`; hit arm `RunsTo.bind` (the lifted `logProf`) then `RunsTo.pure_world`; miss arm from the match's negative hypothesis. No `sorry`/`axiom`/`native_decide`, no new law or field.
- Pod builds (exit 0, each alone, NOT clean issue-linked builds): `Tools.ShippingGen4FbSplit` (709 jobs), `Tests.Gen4.FbSplitCheck`. Check output: TYPE OK 2 (the corollary's hypothesis accepted by logged `isDefEq` against the independent `ExpR4RunInvT3` copy); MUTANT REJECTED 8 (signature/defeq rejections, not semantic counterexamples); REACH: both theorems `missing = 0`, no `Tools.ShippingMemo.*` in the closure; controls 7 (absent root → missing 1 and the assertion failed as expected, raw `Expr.proj` of `RefLawsM` flagged, fixtures using `memoInv_hit` directly / through a helper / `outer_miss` flagged, an unrelated theorem and the FB-3 theorem not flagged with missing 0); AXIOMS OK 2 (standard three). Counts exclude summary lines.
- Not supplied: T-LEG, T-MEMO, K4, T-PP, depth 0 of T-FIN, memo law. The split is control-flow only and says nothing about the meaning of `(m, d)`. The clean issue-linked build at the exact SHA in the Issue note is the coder's. Issue / M4 / FG are not complete.

---

## 19. FB-10: supplier survey from the K-TSPLIT split, and the next unit (T-FIN at depth 0) — complete types (rev11; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only. Base `912a5124` (= `28c069d3`, scoped approved, clean build `fb9v-28c069d3` exit 0, 760 jobs, plus a Check-only commit that parenthesises `MutLegHitFreePair`, see §19.6). No new law, no `Laws` field, no TRUSTED boundary, no shared-definition or compiler edit, no FG/guarantee change, `stop_of_run` untouched. Method: reading the statements (not the proofs) of the names below in this tree. "No route found" means this survey found no supplier in the files read; it does NOT say the row is false or underivable. Mutants in the planned check are signature/defeq rejections, not semantic counterexamples.
- **Names that §12/§17 use but this tree does not contain.** `ChildShipsI`, `ChildIface.ofPkg`, `childShipsI_ofPkg`, `ShipsResI` are the gate Issue's names (§0 table); `grep` finds them only in this document. In this tree the child guarantee is `ChildShips q n mc Dc` (`Tools/ShippingGen2Defs.lean:87`), and `ChildIface c n b design` (`Tools/ShippingCallsGate.lean`, a different shape: `ChildComb b ∧ b.inputs.length = n ∧ b.name = … ∧ design.modules = []`) is a gate-side predicate. A statement for T-LEG/T-PP implemented in this tree would therefore read `∃ n, ChildShips q n out dout`, not `ChildShipsI (ChildIface.ofPkg q)`; the relation between the two is the gate Issue's lemma and is not used or checked here.

### 19.1 What the split gives (entry point)
`r4RunInvT_tail_hit_or_miss` (§17.3, built): from `R4RunInvT … D declName shape m d w w'` it yields the package's `tenv pb ci w₅ w₆`, `InvAt (D+1) w₆`, `InvAt (D+1) w₅`, the tail run `RunsTo (legacyTail … ci) … w₆ (m,d) w₅`, the read `RunsTo (sparkleSubModuleCache.get) … w₆ memo w₁` and `memo.get? declName = some (m,d) ∨ = none`. Every row below is read as "what would consume the hit arm / the miss arm / the run end".

### 19.2 Survey (row → real names and types → what the split adds → verdict)
| row | existing names (file:line) | what they state | gap, with the split in hand | verdict |
|---|---|---|---|---|
| depth 0 of T-FIN (`R4RunInvT` side) | `RefLawsAOps.depthModify'` (`ShippingChildInvA.lean:465`): `O.quiet w → RunsTo (ST.Ref.modify sparkleSynthDepth f) … w u w' → cv w' = cv w ∧ sv w' = sv w ∧ dv w' = f (dv w)` (`O := L.O`, `hA : AdmCtx`); `FinallyRestores` (`ShippingMachineOutcomeA4.lean:79`), whose `D = 0` conjunct is `∃ y0, RunsTo (sparkleSynthDepth.modify (· - 1)) … w₅ () y0 ∧ w' = y0`; `R4RunInvT` conjuncts `InvAt (D+1) w₅` (so `L.O.quiet w₅` and `CacheShips (cv w₅)`) and `JQC L.O D w'` | at `D = 0` `coreFinally` is only the depth decrement (no restoring `set`; `sparkleChildCache` is not touched, Elab.lean `coreFinally` model in `ShippingMachineOutcomeA3.lean:66`). So `cv w' = cv w₅`, and `InvAt L P Reach 0 w' = JQC L.O 0 w' ∧ CacheShips L P Reach (cv w')` is the given `JQC` plus `CacheShips (cv w₅)` transported along `cv w' = cv w₅` | **supplied by existing parts on the `R4RunInvT` side** (route found in this survey; proof not yet written). §17.1's "no route found" for this row is superseded by this survey; §17.1 searched `core_tripleAInv`/`stop_of_run` only. The `A4MachineSideA` side carries no `InvAt` conjunct and is not covered |
| T-PP | `refineCheck_transfer` (`ShippingRefineSoundness.lean:1039`: for `refineCheck m o = true`, a `runModule` of `m` from `seedIn m ins` has a `runModule` of `o` with equal outputs); `mergeChecked_cases`/`mergeChecked_ports`/`mergeChecked_seq` (`Sparkle/IR/RefineCheck.lean:280/291/361`); `dropZW_name`, `dropZW_inputs`, `dropZW_wires` (`ShippingMachineDepthRun`, `ShippingOutsExtractedParts:176/182`); `dzStmt_assign_pos` (`ShippingGateDesignPost:78`), `dzStmt_assign` (`ShippingRegisterSoundness`); `machine_ships_wiredSW` (`ShippingMachineShipsSW.lean:~230`) which proves `MachineShipsSW … (dropZeroWidthModule raw) … b` for the MACHINE route | module-level facts and statement-level run facts of the post-processing for specific classes; the machine route's transport is inside `machine_ships_wiredSW`, from `MachineTraceL`, `hnoI : d.shape.insts = []`, `hsl`, `hSS`, `houtTy` and `soundL` | no theorem of the form `ChildShips q n raw dsg → ChildShips q n out dout` (or its `runModule` core for `dropZeroWidthModule`) for an arbitrary `raw`; `ChildRunN` contains `ResetN`/`RunOn` over the whole `dsn`, and `dout` is a rewrite of `dsg` (`PPRel`, §12.4). The tail's `raw` carries none of the machine route's premises | **unsupplied / no route found** to `PPTransportStmt` for the legacy tail. Not claimed false |
| T-LEG (miss arm) | `legacy_entry_walk` (`ShippingLegacySemEntryWalk.lean:133`), `legacy_entry_walk_in` (`ShippingLegacySemEntryIn.lean:47`), `legacy_entry_walk_at` (`ShippingLegacySemMemoWalk.lean:93`), `legacy_entry_output(_walked)` | about `synthesizeFromConst … false cfe (.defnInfo dv) isInst` with the premises `cfe = true → certifiedShape? … = none`, `… mixedCertifiedShape? … = none`, **`cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none`** | R4 runs `synthesizeFromConst … false true ci` and `R4RunInvT` carries `machineShape? false [] (entryConst true false [] ci …) (structEnv envR') = some shape`. The `hmach` premise is the negation of that conjunct (for `entryConst … ci` standing for `.defnInfo dv`; the correspondence of `ci`/`dv` was read, not proved). So these forms cannot be applied to the R4 tail as they stand, and none of them is stated about the named `legacyTail` from `w₆` | **unsupplied / no route found** to `LegMissStmt`. The split gives the miss term (`memo.get? declName = none` at `w₆`) but nothing relates the module built after it to `q.S` |
| T-MEMO, depth-0 miss | `outer_miss` (`ShippingLegacySemMemoWalk.lean:495`): premises `L : RefLawsM`, `L.dval w = 0`, `L.quiet w`, `EntryConstIs`, `old`, `mixed`, **`hmach : ∀ projs, machineShape? … = none`**, `hr : core run`; conclusion `∃ memo wr wr', RunsTo (get) wr memo wr' ∧ L.mval wr = {} ∧ ∀ n, memo.get? n = none` | the read of THIS run is empty | same `hmach` premise as T-LEG (negation of R4's machine-shape conjunct), and `RefLawsM` is not part of `Laws`; the read it locates is the one inside `synthesizeFromConst`'s legacy arm, not `legacyTail`'s read at `w₆` | **unsupplied on the examined route (`outer_miss`, which takes `RefLawsM`); on that route a law would be a user decision, see §19.4. This survey did not examine other routes, so it does not say a law is required on every route** |
| T-MEMO, hit and nested miss (K4) | `memoInv_hit` (`ShippingMemoInv.lean:88`): `MemoInv LM Φ w → (LM.mval w).get? n = some r → Φ n r`; `memoInv_write` (`:~100`), `memoInv_of_empty/same/reset/frame/read`; `MemoInv LM Φ w := ∀ n r, (LM.mval w).get? n = some r → Φ n r` | preservation of a memo-content invariant | the split supplies `memo.get? declName = some (m,d)` for the memo READ by `sparkleSubModuleCache.get`; connecting that read to `LM.mval w₆` is `memoGet` (a `RefLawsM` field). `MemoInv LM Φ w₆` has no supplier (K4 is a reading of the source) | **unsupplied on the examined route (`memoInv_hit` / `memoGet`, which go through `RefLawsM`; a law there would be a user decision) and no K4 invariant supplier found; other routes were not examined, so this does not say a law is required on every route** |
| K4 | none in `Tools/` | — | — | **unsupplied / no route found** |

### 19.3 Selection and reason
First unit: **T-FIN0** (FB-11). Reasons: (1) it is the only unsupplied row whose supply is made of existing theorems of this tree and the already-built `R4RunInvT` (no `RefLawsM`, no `MemoInv`, no new law or field, no shared definition); (2) every other row stops, on the routes read, at a missing law (`RefLawsM`), at a premise contradicted by `R4RunInvT` (`hmach`), or at a statement with no supplier; (3) it extends the preservation line of FB-3…FB-7 (`InvAt` at `w₄ w₆ w₅`, then at `w'` for `D ≥ 1`) to the one remaining depth, which the downstream `InvAt D w'` consumers (`R4OutStmt`'s caller, `IHAt` at the parent) need. It is preservation (P), not (S): it does not relate `(m, d)` to `q.S` and does not advance T-LEG/T-MEMO/T-PP.

### 19.4 Rows whose examined route goes through a law: the exact text, NOT added
No law is added and no `Laws` field is introduced by this Issue. If the user decides to admit the memo boundary, the text that would be needed is:
- **L-MEMO (candidate, not adopted).** `Laws` (or a sibling structure over the SAME `mref`, `cref`, worlds as `L.O`) gains the memo part of `RefLawsM` (`ShippingMemoLaws.lean:90`): `mval : Void IO.RealWorld → Std.HashMap Name Res`; `memoGet : RunsTo (sparkleSubModuleCache.get) w m w' → m = mval w ∧ mval w' = mval w`; `memoSet : RunsTo (sparkleSubModuleCache.set v) w u w' → mval w' = v`; `memoModify : RunsTo (sparkleSubModuleCache.modify f) w u w' → mval w' = f (mval w)`; `distinct : MemoOther r → ¬ HEq r sparkleSubModuleCache`; `memoFrame : MemoFrameOp p → RunsTo p w a w' → mval w' = mval w`; plus the `RefLaws` it extends over the same refs. Impact: enlarges the trust base by these six assumptions about the world model (the `RefLaws` part is a second, partially overlapping family next to `RefLawsAOps`, whose compatibility with `L.O` is itself unchecked); it changes what "Laws" assume and therefore every theorem quantified over `Laws`. Reversible only by removing the field and re-checking all dependants.
- Even with L-MEMO, the depth-0 miss through `outer_miss` additionally needs its `hmach` premise, which `R4RunInvT` contradicts; the miss at `w₆` would instead need a statement that the machine attempt (`synthesizeMachineCertified … none`) leaves `mval` unchanged, i.e. a `memoFrame`-type fact about that program, which this survey did not look for. This is the statement that would have to be formulated, not something derived here.
- T-LEG and T-PP are not law-shaped on this survey: they are missing theorems (a legacy-tail meaning theorem; a run-level `dropZeroWidthModule` transport). Whether a new contract for the legacy route (registers/instances; D-LEGACY-SCOPE) is needed is the user's decision and is not taken here.

### 19.5 T-FIN0: complete types (target; each hypothesis and binder written out)
Namespace `Tools.ShippingGen4FbFin0` (new file `Tools/ShippingGen4FbFin0.lean`); same `open`/`variable` context as `Tools/ShippingGen4FbFin.lean`; imports `Tools.ShippingGen4FbFin` (for the companion).
```lean
theorem tFin0_of_r4RunInvT {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : R4RunInvT L P Reach mctx cctx 0 declName shape m d w w') :
    InvAt L P Reach 0 w'

theorem a4_inv_tail_fin0 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∨
      (R4RunInvT L P Reach mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w')
```
Premises: exactly `hA` (and, for the companion, `hI`, `hC`, `hr`, `entry` as in `a4_inv_tail_machine_or_R4RunInvT`, `D := 0`, so `D + 1 = 1`). No `RefLawsM`, no new hypothesis. The `A4MachineSideA` disjunct has no `InvAt` conclusion (the machine side of `R4Run` carries none); this is stated, not hidden.

Proof plan (a plan, not a result): `obtain ⟨tenv, pb, ci, envR', w₁, …, w₅, w₆, h4, h6, h5, …, ⟨sf, sw, sl, sp, sc, ss, sg, _, hfr, _, _⟩, hJ', …⟩ := h`; `obtain ⟨y0, hmod, h0, -⟩ := hfr`; `have hw' : w' = y0 := h0 rfl`; `obtain ⟨hcv, -, -⟩ := L.O.depthModify' hA (· - 1) h5.1.1.1 hmod` (the `quiet w₅` is the first component of `JQ` in `h5.1`; its exact projection path is fixed when the file is written, and the document is synchronised to what is used); conclude `⟨hJ', by rw [hw', hcv]; exact h5.2⟩`. The companion is `rcases a4_inv_tail_machine_or_R4RunInvT … with hside | hT` and `Or.inr ⟨hT, tFin0_of_r4RunInvT … hT⟩`. If `depthModify'` does not apply as stated (`ST.Ref.modify` vs `sparkleSynthDepth.modify` elaboration), the unit reports "not closed in this attempt" with the failing step; this is not a claim that the fact is false.

### 19.6 Check-only correction made before this freeze
`Tests/Gen4/FbSplitCheck.lean` (`912a5124`): `MutLegHitFreePair` is now `… ∧ ((∃ m' d', memo.get? declName = some (m', d')) ∨ memo.get? declName = none)`, so it differs from `ExpLegacyTailHitOrMiss` in the pair of the hit arm only and the miss arm keeps its read. The Pod build `Tests.Gen4.FbSplitCheck` exit 0 (760 jobs, not a clean build): MUTANT REJECTED 8, TYPE OK 2, AXIOMS OK 2, REACH 2 with missing 0, controls 7 — unchanged counts; `MutLegHitFreePair` still REJECTED. The clean issue-linked build of this Check change is the coder's. The header now records `fb9v-28c069d3`.

### 19.7 Planned checks for T-FIN0 (new files only; nothing run)
Files: `Tools/ShippingGen4FbFin0.lean`, `Tests/Gen4/FbFin0Check.lean`, two `lean_lib` entries in `lakefile.lean`.
1. TYPE: both theorems against `Expected…` typed again in the check file from §19.5 (the `R4RunInvT` hypothesis through an independent copy of its body as in `ExpR4RunInvT2/3`, accepted by the same reducible comparator `==` then logged `isDefEq`, the logged fallbacks counted separately).
2. MUTANTS (signature/defeq rejections, NOT semantic counterexamples), each by the SAME comparator: conclusion `InvAt … 1 w'` (depth `1` instead of `0`); conclusion at `w₅` is not expressible, so `InvAt … 0 w` (start world) instead of `w'`; conclusion `JQC L.O 0 w'` only (the `CacheShips` conjunct dropped); `hA` dropped; hypothesis `R4RunInvT … 1` instead of `0`; companion with `InvAt … 0 w'` stated on the `A4MachineSideA` disjunct too (a stronger, unsupplied statement); companion with the conjunction of the `Or.inr` arm replaced by `R4RunInvT` alone (drops the new conclusion); companion `hC` at depth `0`.
3. REACH/closure audit as in `FbSplitCheck` (value closure of type and body, raw `Expr.proj` structure names included): no `Tools.ShippingMemo.*` (so no `RefLawsM`/`MemoInv`/`outer_miss`/`memoInv_hit`); unknown constants counted in `missing`, which must be 0 (fail otherwise); controls: absent root → missing ≥ 1 and assertion fails as expected, a fixture using `memoInv_hit` directly, through a helper, and `outer_miss` flagged, an unrelated theorem and a built FB theorem not flagged.
4. AXIOMS `⊆ {propext, Classical.choice, Quot.sound}`, `sorry` 0, no `native_decide`.
5. Counts in reports are the actual numbers of checks that ran, by category (TYPE, MUTANT, REACH, controls, AXIOMS), with the aggregation rule stated; summary lines are not counted. The clean issue-linked build is the coder's; a Pod build by this unit is not a clean build.

### 19.8 What this section does not claim
- No row of (S) is supplied: T-LEG, T-MEMO (hit, depth-0 miss, K4), T-PP stay unsupplied; "unsupplied" means this survey found no route in the files read, not that none exists.
- T-FIN0 (when implemented) is a preservation fact on the `R4RunInvT` side at depth 0; it does not cover the `A4MachineSideA` side, does not relate `(m, d)` to `q.S`, and does not make `R4OutStmt` provable.
- The correspondence between the `ci`/`dv` of `R4RunInvT` and the `.defnInfo dv` of `outer_miss`/`legacy_entry_*` is read, not proved.
- No new law is proposed for adoption; §19.4 states the text of a candidate for the user to decide. Whole-Issue status unchanged: fallback / legacy / memo success routes, M4 and FG are not complete.

---

## 20. FB-11 implementation status (docs; Pod build only)
- `Tools/ShippingGen4FbFin0.lean` (`tFin0_of_r4RunInvT`, `a4_inv_tail_fin0`) and `Tests/Gen4/FbFin0Check.lean`; two `lean_lib` entries appended to `lakefile.lean`. Types exactly as §19.5; no extra premise was needed; no built file, shared definition or compiler touched. Proof as the §19.5 plan: the `JQ`-quiet component of `InvAt (D+1) w₅` feeds `RefLawsAOps.depthModify'`, giving `cv w' = cv w₅`; the `JQC … 0 w'` conjunct of `R4RunInvT` is the first half. The §19.5 plan said "`h5.1.1.1`"; the file uses exactly that projection. The `A4MachineSideA` side has no `InvAt` conclusion (not covered).
- §19.2 / §19.4 wording narrowed in this commit: "needs a law" is stated only for the examined routes (`outer_miss`, `memoInv_hit`/`memoGet`); no claim that a law is required on every route. No new law is adopted.
- Not supplied: T-LEG, T-MEMO, K4, T-PP, `A4MachineSideA` depth 0 `InvAt`. Issue / M4 / FG are not complete. The clean issue-linked build (including `FbSplitCheck` for the `912a5124` parenthesisation) is the coder's.
- Pod builds (exit 0, each alone, NOT clean issue-linked builds): `Tools.ShippingGen4FbFin0`, `Tests.Gen4.FbFin0Check` (810 jobs). Check output: TYPE OK 2 (both accepted by logged `isDefEq` against the independent `ExpR4RunInvT4` copy; logged fallbacks counted separately); MUTANT REJECTED 8 (signature/defeq rejections by the same comparator, not semantic counterexamples; 5 on the first theorem, 3 on the companion, including the dropped-conjunct and the `A4MachineSideA`-gets-`InvAt` variants); REACH 2 (`missing = 0`, no `Tools.ShippingMemo.*`); controls 8 (absent root → missing 1 and assertion failed as expected, raw proj flagged, 3 bad fixtures flagged, unrelated/FB-3/FB-7 theorems not flagged); AXIOMS OK 2 (standard three). `sorry` 0. Counts are numbers of checks that ran by category; summary lines excluded.

---

## 21. FB-12: survey of the A4MachineSideA side, T-LEG, T-MEMO, T-PP from K-TSPLIT / T-FIN0, and the next unit (T-MACH-INV) — complete types (rev12; text for review; NOT Lean, NOT implemented)

- **Status.** Docs only. Base `3335410d` (= `438d2448`, T-FIN0 scoped approved, clean build `fb11v-438d2448` exit 0, 812 jobs, plus a comment-only commit: trailing space in `Tools/ShippingGen4FbFin0.lean:3`, the `FbFin0Check` Expected reference §17.3 → §19.5, build record synced; `git diff --check` clean). No new law, no `Laws` field, no TRUSTED boundary, no shared-definition or compiler edit, no FG/guarantee change, `stop_of_run` untouched. Method: reading the statements (and, for the extraction, the proof text) of the names below in this tree. "Unsupplied / route not found in this survey" means this survey found no supplier in the files read; it does NOT say a row is false or underivable. Mutants in the planned check are signature/defeq rejections, not semantic counterexamples.
- **Entry points used.** K-TSPLIT (`legacyTail_hit_or_miss`, `r4RunInvT_tail_hit_or_miss`, §17.3/§18) for the tail rows; T-FIN / T-FIN0 (`tFin_stop`, `a4_inv_tail_fin`, `tFin0_of_r4RunInvT`, `a4_inv_tail_fin0`, §14/§19.5) for the world at `w'`.
- **Names §12 uses but this tree lacks** are as recorded in §19 (`ChildShipsI`, `ChildIface.ofPkg`); statements implemented here read `ChildShips q n out dout`. Not repeated.

### 21.1 Survey (row → real names and types → what K-TSPLIT / T-FIN0 add → verdict)
| row | existing names (file:line) | what they state | gap, with the entry points in hand | verdict |
|---|---|---|---|---|
| **A4MachineSideA, `InvAt` (P)** | `A4MachineSideA` (`ShippingGen4FbR4.lean:71`); `a4_inv_machine_or_R4RunInv` (`ShippingGen4FbInv.lean:242`), whose proof holds `hIA : InvAt (D+1) wA` and `hI6 : InvAt (D+1) w6` for BOTH branches and then `Or.inl ⟨…⟩` DROPS them; `machineAttempt_keepsInv` (`:69`); `keepsA_framed … (FramedA.sideModify _ .subModule)` (the memo insert, already used in `ShippingGen4FbTailInv.lean:76`); `RefLawsAOps.depthModify'` (used in `ShippingGen4FbFin0.lean`); `tFin_stop` (`ShippingGen4FbFin.lean:22`, any run, `1 ≤ D`) | the A-side data has `JQC` conjuncts at `w₄ w₆` only; `InvAt` is available inside the extraction proof but is not part of the A-side type | (i) `InvAt (D+1)` at the A-side `w₄`, `w₆` is already proved inside `a4_inv_machine_or_R4RunInv` and only needs to be exported with the same witnesses; (ii) `InvAt (D+1) w₅` (`w₅` = end of `profLog` lift then `sparkleSubModuleCache.modify (·.insert declName (m,d))`) from `hI6` by `Keeps.bind (by vca)` for the lifted `profLogIO` (the same step shape that `legacyTail_keeps_generic` closes by `by vca`) and `keepsA_framed … sideModify .subModule`; (iii) `InvAt 0 w'` from `w₅` by the proof of `tFin0_of_r4RunInvT` (depth decrement only, `cv w' = cv w₅`); `D ≥ 1` is already `tFin_stop` | **to be proved from existing parts on the route read (証明予定; not counted as supplied until the implementation, §22, succeeds)**. Step (ii) rests on `by vca` accepting the `liftM profLogIO` step of the A-side; if it does not, the unit reports "not closed in this attempt" at that step |
| A4MachineSideA, meaning (S) | `synthesizeMachineCertified_runsS` (`ShippingGen2ServedRun.lean:445`): from `IHAt L P Reach n`, `ChildKeepsInv L P Reach n`, **`InvAt L P Reach n w`** and a run of `synthesizeMachineCertified … w (some (m,d)) w'` it gives `∃ t t' d₀, MReturns (synthesizeMixedCertified …) (t,d₀) ∧ closeLets … = some t' ∧ (no-insts ∨ CloseCalls … ∧ ChildrenShipsI L P Reach shape children)`; `closeInstsM_ships` (`:353`); `machine_ships_wiredSW` (`ShippingMachineShipsSW.lean:216`, premises `soundL`, `hnoI`, `hsl`, `hSS`, `houtTy`, `MachineCloses`) | the module-level meaning of the machine route | the `InvAt n w` premise of `runsS` at the machine start world (`wA`, `n = D+1`) is exactly the item (i) above; with it the first conclusion of `runsS` is a term for the A-side. The step from `CloseCalls` / `MachineTraceL` to `ChildShips q n out dout` after the memo insert and `PPRel` uses the machine-route premises of `machine_ships_wiredSW` (not read beyond signatures here) and T-PP below | **partially reachable: the supplier of `runsS`' `InvAt` premise is the unit below; the remaining machine-route premises and T-PP were not examined further** |
| T-LEG (miss arm) | as §19.2 (`legacy_entry_walk(_in/_at)`, `legacy_entry_output(_walked)`, `outer_miss` all carry `hmach : machineShape? … = none`; `R4RunInvT` carries `… = some shape`); `r4RunInvT_tail_hit_or_miss` gives the miss term `memo.get? declName = none` at the package's `w₆` | meaning of the legacy arm of `synthesizeFromConst` from a fresh world, for the scalar-combinational / projection classes | unchanged: no statement is about the named `legacyTail` from `w₆`; `LegacyDom`/`Value` are scalar-combinational; no register/instance contract. `grep legacyTail Tools Tests` finds it only in the FB/OutcomeA/LegacyTailA/Compose/Pin files (preservation, split), none stating a meaning | **unsupplied / route not found in this survey** (no new route since §19.2) |
| T-MEMO, hit | `memoInv_hit` (`ShippingMemoInv.lean:88`), over `RefLawsM`; the split's hit arm gives `memo.get? declName = some (m,d)` for the READ `sparkleSubModuleCache.get` | content invariant of the memo | `MemoInv LM Φ w₆` has no supplier; linking the read to `LM.mval w₆` is `memoGet` (a `RefLawsM` field, not in `Laws`) | **unsupplied on the examined route (goes through `RefLawsM`); a law there would be the user's decision (§19.4 text unchanged); other routes were not examined** |
| T-MEMO, nested miss / K4 | `memoInv_write/of_*` (all over `RefLawsM`); `ArmObligations`, `MemoSound` (statements only) | | K4 ("memo names ⊆ `childCache` names ∪ {top}") has no theorem; the only cache invariant in the tree about the memo-adjacent state is `CacheShips (cv w)`, which is `sparkleChildCache`, not `sparkleSubModuleCache` | **unsupplied / route not found in this survey** |
| T-PP | `refineCheck_transfer` (`ShippingRefineSoundness.lean:1039`), `mergeChecked_*`, `dropZW_name/inputs/wires`, `machine_ships_wiredSW` (machine route only) | module-level / run-level facts for specific classes | `grep` for a lemma of the form `ChildShips … raw dsg → ChildShips … out dout` (or `PPTransport*`) in `Tools/` finds none; the only transport is inside `machine_ships_wiredSW` for the machine route | **unsupplied / route not found in this survey** |

### 21.2 Selection and reason
First unit: **T-MACH-INV** (FB-12): export `InvAt (D+1)` at the machine start world `wA`, the machine end `w₆` and the memo-insert end `w₅` on the `A4MachineSideA` side with the same witnesses as the run data, and `InvAt 0 w'` at depth 0 for that side. Reasons: (1) it is the only unsupplied row whose supply is made of existing theorems plus a re-packing (no `RefLawsM`, no `MemoInv`, no new law or field, no shared-definition edit); (2) it closes the preservation line that FB-3/FB-4/FB-7/FB-11 closed only for the `R4RunInvT` side, so that BOTH disjuncts of the extraction carry `InvAt` at `w'` for every `D` (D ≥ 1 by `tFin_stop`, D = 0 here); (3) it supplies the `InvAt n w` premise that `synthesizeMachineCertified_runsS` needs on this side, i.e. the first non-trivial hypothesis of the machine-side meaning route (no meaning claim is made by the unit). It is preservation (P), not (S). Every other row stops, on the routes read, at `RefLawsM` (user decision) or at a statement with no supplier found.

### 21.3 Rows needing a law or a user decision: text and impact only, NOT added
No law or `Laws` field is added. For T-MEMO (hit / K4) on the examined route the text is §19.4 (L-MEMO candidate, six memo assumptions over the same refs and worlds as `L.O`; enlarges the trust base; changes every theorem quantified over `Laws`; reversible only by removing the field and re-checking dependants). In addition, a K4 statement would have to be formulated (not derived here): "every key of `sparkleSubModuleCache` at a nested tail start is the name of a package in `Reach` or the top name, and its value satisfies `PhiPP`"; without it `MemoInv LM (PhiPP …) w₆` at a nested tail start has no source even with L-MEMO. For T-LEG a legacy-route contract for registers/instances (D-LEGACY-SCOPE) and for T-PP a run-level `dropZeroWidthModule` transport are missing THEOREMS, not laws; whether to narrow scope is the user's decision and is not taken. FG is not narrowed.

### 21.4 T-MACH-INV: complete types (target; each hypothesis and binder written out)
Namespace `Tools.ShippingGen4FbMachInv` (new file `Tools/ShippingGen4FbMachInv.lean`); imports `Tools.ShippingGen4FbFin0` (which brings `FbInv`, `FbTailInv`, `FbFin`); same `open`/`variable` context as `Tools/ShippingGen4FbFin0.lean` plus `Tools.ShippingGen4FbFin0`.
```lean
/-- `A4MachineSideA` (ShippingGen4FbR4.lean:71) with the three `InvAt (D+1)` conjuncts, in this order, placed FIRST like
`R4RunInvT`: at the machine start world (the A-side `w₄`), the machine end (`w₆`) and the memo-insert end (`w₅`). -/
def A4MachineSideInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
    -- followed by EXACTLY the conjuncts of the `A4MachineSideA` body after its binders
    -- (Tools/ShippingGen4FbR4.lean:71-96 at 3335410d), same order, same text, `O := L.O`

theorem a4_inv_side_or_tail (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideInv L P Reach mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w'

theorem tFin0_of_a4MachineSideInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : A4MachineSideInv L P Reach mctx cctx 0 declName shape m d w w') :
    InvAt L P Reach 0 w'

theorem a4_inv_tail_fin0_both (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    (A4MachineSideInv L P Reach mctx cctx 0 declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx 0 declName shape m d w w') ∧ InvAt L P Reach 0 w'
```
Premises: exactly `hA`, and for the extraction `hI`, `hC`, `hr`, `entry` as in `a4_inv_tail_machine_or_R4RunInvT`. No `RefLawsM`, no `IHAt`, no new hypothesis. The `InvAt` conclusion of `a4_inv_tail_fin0_both` is outside the disjunction (it holds for both sides); for `D ≥ 1` the same shape is `a4_inv_tail_fin` with `A4MachineSideInv` in place of `A4MachineSideA`, NOT part of this unit.

Projections (theorems in the check file): `A4MachineSideInv → A4MachineSideA L.O` (drop the three leading `InvAt` conjuncts); the extraction projects to `a4_inv_tail_machine_or_R4RunInvT` (hence to FB-3/FB-2 extractions).

Proof plan (a plan, not a result). `a4_inv_side_or_tail`: the proof text of `a4_inv_machine_or_R4RunInv` (FbInv.lean:242-278) up to `hI6`, then `rcases hout` as there; (a) branch: after `rfl, rfl` (`res = some (m,d)`), take `hl : RunsTo (profLogIO …) hw6 () wl`, `hm : RunsTo (… modify (·.insert …)) wl () w4'`; `InvAt … w4'` by `triple_runs (keeps_iff.mp (Keeps.bind (by vca) fun _ => keepsA_framed L.O hA (stableA_invAt L P Reach (D+1)) (FramedA.sideModify _ .subModule)))` on the lifted pair, or two `triple_runs`; re-pack `Or.inl ⟨…, hIA, hI6, hI5, …⟩` with the SAME `envR b ci envR' w1 w2 w3 wA w4 w6`; (b) branch: `Or.inr` with `a4_inv_tail_machine_or_R4RunInvT`'s re-pack (FIXED at implementation, §22: `a4_inv_side_or_tail` repeats the FbInv prefix proof up to `hIA`/`hI6` with the same witnesses and adds `hI5`; the tail branch applies `legacyTail_keepsInv` to the same data. It does NOT `rcases` an existing extraction and reuse an `InvAt` from another `obtain`.). `tFin0_of_a4MachineSideInv`: destructure like `tFin0_of_r4RunInvT` (`FinallyRestores` `D = 0` conjunct, `depthModify'` with `quiet w₅` from `h5.1.1.1`). `a4_inv_tail_fin0_both`: `rcases a4_inv_side_or_tail …` and `tFin0_of_a4MachineSideInv` / `tFin0_of_r4RunInvT`. If the `by vca` step on the lifted `profLogIO` or the `sideModify` bind does not apply, the unit reports "not closed in this attempt" with the failing step; this is not a claim that the fact is false.

### 21.5 Planned checks for T-MACH-INV (new files only; nothing run)
Files: `Tools/ShippingGen4FbMachInv.lean`, `Tests/Gen4/FbMachInvCheck.lean`, two `lean_lib` entries in `lakefile.lean`. Independent of the Lean text:
1. TYPE: the three theorems against `Expected…` typed again in the check file from §21.4 (the `A4MachineSideInv` body through an independent copy typed from the `A4MachineSideA` text of `ShippingGen4FbR4.lean:71-96` plus the three conjuncts; `R4RunInvT` through the independent copy used in `FbFin0Check`), by ONE reducible comparator (`==` then logged `isDefEq` fallback), the same for positive and negative cases; fallbacks counted separately. The definition value of `A4MachineSideInv` is also compared.
2. MUTANTS (well-typed single changes only; signature/defeq rejections, NOT semantic counterexamples): the `w₅` conjunct dropped from the def; `InvAt (D+1) w₅` replaced by `JQC (D+1) w₅`; `InvAt` at depth `D` instead of `D+1`; `w₅` replaced by `w₆` in the third conjunct; `tFin0_of_a4MachineSideInv` concluding `InvAt … 1 w'`, or `InvAt … 0 w`, or `JQC L.O 0 w'` only; hypothesis at depth `1`; `hA` dropped; `a4_inv_side_or_tail` without `hC`, or with `A4MachineSideA` in place of `A4MachineSideInv`; the `_both` conclusion with the `InvAt` conjunct moved inside the second disjunct only; and a conclusion-conjunct-dropped variant of each of `_both` and the extraction (the conjunction of the conclusion is not dropped silently).
3. REACH/closure audit as in `FbFin0Check` (value closure of type and body, raw `Expr.proj` structure names included): no `Tools.ShippingMemo.*`; unknown constants counted in `missing`, which must be 0 (the assertion fails otherwise); controls: absent root → `missing ≥ 1` and the assertion fails as expected, fixtures using `memoInv_hit` directly / through a helper / `outer_miss` flagged, an unrelated theorem and the built `a4_inv_tail_fin0` not flagged.
4. AXIOMS `⊆ {propext, Classical.choice, Quot.sound}`, `sorry` 0, no `native_decide`.
5. Counts in reports are actual numbers of checks that ran by category (TYPE, MUTANT, REACH, controls, AXIOMS) with the aggregation rule stated; summary lines are not counted. A Pod build by the implementing unit is not a clean build; the clean issue-linked build is the coder's.

### 21.6 What this section does not claim
- No (S) row is supplied: T-LEG, T-MEMO (hit, nested miss, K4), T-PP stay "unsupplied / route not found in this survey"; the A-side meaning (`runsS` → `ChildShips`) is only noted as reachable after T-MACH-INV and the machine-route premises, which were not examined.
- T-MACH-INV (when implemented) is preservation (P): it does not relate `(m, d)` to `q.S`, does not make `R4OutStmt` provable, and says nothing about the memo content written by the A-side insert (that would be `memoInv_write`, over `RefLawsM`).
- No new law is proposed for adoption; §19.4 / §21.3 give the text of a candidate and the missing statements for the user to decide. Whole-Issue status unchanged: fallback / legacy / memo success routes, M4 and FG are not complete.

---

## 22. FB-13 implementation status (docs; Pod build only)
- `Tools/ShippingGen4FbMachInv.lean` (`A4MachineSideInv`, `a4_inv_side_or_tail`, `tFin0_of_a4MachineSideInv`, `a4_inv_tail_fin0_both`) and `Tests/Gen4/FbMachInvCheck.lean`; two `lean_lib` entries appended to `lakefile.lean`. Types exactly as §21.4; no extra premise; no built file, shared definition or compiler touched. The file uses `variable {ι} {dom} {mref} {cref}` (as `FbTailInv`); the statements carry them as implicit binders in that order, so the intended types are unchanged (Fin0 has no common variable block; the Check binds `ι dom mref cref` explicitly in every Expected).
- Proof as the §21.4 plan, route fixed (see §21.4): the `profLog` step is `keepsA_diag … (Diag.profLog b _)` and the memo insert is `keepsA_framed … (FramedA.sideModify _ .subModule)`, applied in two `triple_runs` from `hI6` (no `by vca` was needed). Both closed in this attempt. The depth-0 step is the proof of `tFin0_of_r4RunInvT` with the `w₅` conjunct.
- Check: `A4MachineSideInv` value and type compared with `ExpSideInv` (body of `A4MachineSideA` ShippingGen4FbR4.lean:77-101 with `O := L.O`, plus the three conjuncts, fully expanded) and the three theorems with Expected typed again; two projection theorems (`sideInv_to_sideA`, `extract_to_fb4`) in the check file.
- Not supplied: T-LEG, T-MEMO, K4, T-PP, machine-route meaning (`runsS` → `ChildShips`); no law adopted; Issue / M4 / FG are not complete. The clean issue-linked build is the coder's.
- Pod builds (exit 0, each alone, NOT clean issue-linked builds): `Tools.ShippingGen4FbMachInv` (760 jobs), `Tests.Gen4.FbMachInvCheck` (811 jobs). Check output, by category: TYPE OK 5 (definition value 1, definition type 1, theorems 3; the 3 theorem comparisons are accepted by logged `isDefEq` against the `ExpSideInv`/`ExpR4RunInvT5` copies, fallbacks 3 counted separately; the definition value/type comparisons were syntactic); MUTANT REJECTED 16 (well-typed single changes, signature/defeq rejections by the same comparator, NOT semantic counterexamples: 4 on the definition value [w₅ conjunct dropped, `JQC` for `InvAt`, depth `D`, `w₆` for `w₅`], 5 on `tFin0_of_a4MachineSideInv` [conclusion depth 1, start world, `JQC` only, hypothesis depth 1, `hA` dropped], 3 on the extraction [`hC` dropped, `A4MachineSideA` in place, `R4RunInv` in place of `R4RunInvT` (dropped conjunct)], 4 on `_both` [conclusion conjunct dropped, conjunct inside the second disjunct only, `hC` at depth 0, `A4MachineSideA` in place]); REACH 6 (4 theorems/def + 2 projections; `missing = 0`, no `Tools.ShippingMemo.*`); controls 9 (absent root → missing 1 and assertion failed as expected, raw proj flagged, 3 bad fixtures flagged, 4 non-flag: unrelated, FB-3, FB-7, FB-11 theorems); AXIOMS OK 6 (standard three). `sorry` 0. Counts are numbers of checks that ran by category; summary lines excluded.

---

## 23. FB-14: survey of T-LEG / T-MEMO / T-PP from T-MACH-INV, and the next unit (T-PP-PORTS: the port/shape part of the post-processing) — complete types (rev13; text for review)

- **Status.** Docs, committed BEFORE the Lean file of this unit. Base `c435c90a` (= `4e639a94`, T-MACH-INV, FB-13 approved: `A4MachineSideInv` / `a4_inv_side_or_tail` / `tFin0_of_a4MachineSideInv` / `a4_inv_tail_fin0_both`; clean build `fb13vb-c435c90a` exit 0, 811 jobs). No new law, no `Laws` field, no TRUSTED boundary, no shared-definition / compiler edit, no FG/guarantee change, `stop_of_run` untouched. "Unsupplied / route not found in this survey" means this survey found no supplier in the files read; it does NOT say a row is false or underivable. Mutants in the planned check are signature/defeq rejections, not semantic counterexamples.
- **Process note.** The unit instruction orders "freeze commit, then implement". The common rule asks for freeze approval before Lean. This unit follows the unit instruction; the Issue stays `doing`, and the Lean commit is reported as written before a reviewer saw §23. If the reviewer rejects §23.3, the Lean commit is the thing to revert; nothing built here is relied on by an approved file.
- **Names §12 uses but this tree lacks** are as in §19 (`ChildShipsI`, `ChildIface.ofPkg`); statements here read `ChildRunN` / `ChildShips`, which exist in this tree (`Tools/ShippingGen2Defs.lean:60-92`).

### 23.1 Survey (row → names read in this pass → gap → verdict)
| row | existing names (file:line) | what they state | gap | verdict |
|---|---|---|---|---|
| T-LEG (miss arm) | unchanged since §21.1: `legacy_entry_walk(_in/_at)`, `legacy_entry_output(_walked)`, `outer_miss` carry `hmach : machineShape? … = none`; `grep -rl legacyTail Tools Tests` finds it only in the FB files, `ShippingMachineOutcomeA/A3/A4`, `ShippingChild{ComposeA,ComposeC,LegacyTailA,PinC,MainA}`, `ShippingGen2Keep`, `ShippingGen5RunReads`, `Tests/Compiler/ChildVertAuditTest`, `Tests/Gen5/RunReadsCheck`: all preservation or run-extraction statements, none states what `(m,d)` computes | — | the tail starts at `w₆` after the machine attempt; no register/instance contract; `LegacyDom`/`Value` scalar | **unsupplied / route not found in this survey** (no new route since §21.1) |
| T-MEMO, hit | `memoInv_hit` (`ShippingMemoInv.lean:88`) over `RefLawsM`. This pass also read `RefLawsAOps` (`ShippingChildInvA.lean:263-294`): its fields frame `cv`/`sv`/`dv` and set `cv`/`dv`, there is NO field about the VALUE of `sparkleSubModuleCache` (the memo insert is only a framed `sideModify`, which is why FB-13 could keep `InvAt` across it) | | linking `sparkleSubModuleCache.get` to a content invariant needs `RefLawsM.memoGet`/`mval` on the route examined | **unsupplied on the examined route (goes through `RefLawsM`); a law there is the user's decision (§19.4 text unchanged, nothing added); other routes not examined** |
| T-MEMO, nested miss / K4 | `memoInv_*`, `ArmObligations`, `MemoSound` (statements only) | | no theorem for "memo names ⊆ `childCache` names ∪ {top}" | **unsupplied / route not found in this survey** |
| T-PP, run level | `dropZeroWidth_entry` (`ShippingPostSoundness.lean:519`), `dropZeroWidth_entry_order` (:953), `postprocess_sized`/`_facts`/`_order`: all take `PostReady M n` with `0 < n` (the shape of the ENTRY module); `refineCheck_transfer` (`ShippingRefineSoundness.lean:1039`) transfers runs for `refineCheck m o = true` (the `mergeChecked` accept case); `mergeChecked_inst` (`ShippingMachineShipsHier.lean:69`) / `mergeChecked_of_hasInst` (`ShippingMachineDepthRun.lean:85`): instance-containing body ⇒ `mergeChecked r = r`; `machine_ships_wiredSW` (machine route only) | run/body facts for specific classes | no theorem `ChildRunN … raw … → ChildRunN … out …` for an arbitrary `raw`: `PostReady` is not available for a legacy-tail `raw`, and the `dropZeroWidthModule` body rewrite (`dzStmt`) has no run-level transport lemma outside `PostReady` modules | **run part: unsupplied / route not found in this survey** |
| T-PP, port/shape level | `dropZW_name` (`ShippingMachineDepthRun.lean:98`), `dropZW_inputs` (`ShippingOutsExtractedParts.lean:176`); `Sparkle.IR.ZeroWidth.dropZeroWidthModule` is `m` or `{ m with body, wires }` (`Sparkle/IR/ZeroWidth.lean:113`), so `outputs` is unchanged by construction; `mergeChecked_ports` (`Sparkle/IR/RefineCheck.lean:291`: inputs, outputs, wires), `mergeChecked_name` (`ShippingMachineDepthRunR.lean:51`) | name / inputs / outputs / wires preserved | the six non-run conjuncts of `SeqChildRunN` / `CombChildRunN` read only `mc.inputs` and `mc.outputs` (plus the interface data `bsC`, `outsC`), so they transfer along `PPRel` | **to be proved from existing parts (this unit)** |

### 23.2 Selection and reason
First unit: **T-PP-PORTS** (FB-14). The port/shape part of T-PP is the only unsupplied piece whose supply is made of existing lemmas plus a case split on `PPRel`: no `RefLawsM`, no law, no shared definition. It is a **partial** supply of T-PP: it covers the non-run conjuncts of `ChildRunN` (and the module names of the rewritten design) and **not** the run conjunct (`∀ T ins s vals … RunOn …`), which stays unsupplied. T-LEG and T-MEMO have no closable piece in this survey. Preservation-class (P)/shape-class only: nothing here relates `(m, d)` to `q.S`.

### 23.3 Complete types (target; each hypothesis and binder written out)
Namespace `Tools.ShippingGen4FbPP` (new file `Tools/ShippingGen4FbPP.lean`, `import Tools.ShippingGen2Defs`, `set_option autoImplicit false`). `ChildRunN` is `Tools.ShippingGen2.ChildRunN`, `SeqChildRunN` is `Tools.ShippingMachineDepth.SeqChildRunN`, `CombChildRunN` is `Tools.ShippingGen2.CombChildRunN`, `argPorts` is `Tools.ShippingMachineCompose.argPorts`, `MixedGateBinder` is `Sparkle.Compiler.Elab.MixedGateBinder`, `OutField` / `WEnv` as in those files.
```lean
/-- Elab.lean 5598-5606: the post-processing of `synthesizeCombinationalWith` (§12.6). -/
def PPRel (raw : Sparkle.IR.AST.Module) (dsg : Sparkle.IR.AST.Design)
    (out : Sparkle.IR.AST.Module) (dout : Sparkle.IR.AST.Design) : Prop :=
  let top : (Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) → Sparkle.IR.AST.Design →
      Sparkle.IR.AST.Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name == raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = Sparkle.IR.RefineCheck.mergeChecked m' ∧ dout = top Sparkle.IR.RefineCheck.mergeChecked d₁)

/-- The six non-run conjuncts of `SeqChildRunN` (Tools/ShippingMachineDepth.lean:67-71), in order. -/
def SeqPortFacts (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧ "clk" ∈ mc.inputs.map (·.name) ∧
  "rst" ∈ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

/-- The six non-run conjuncts of `CombChildRunN` (Tools/ShippingGen2Defs.lean:61-67), in order. -/
def CombPortFacts (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧
  "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

theorem ppRel_ports {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout) :
    out.name = raw.name ∧ out.inputs = raw.inputs ∧ out.outputs = raw.outputs

theorem ppRel_design_names {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout) :
    dout.topModule = dsg.topModule ∧ dout.modules.map (·.name) = dsg.modules.map (·.name)

theorem ppRel_seqPortFacts {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : SeqPortFacts raw bsC outsC) : SeqPortFacts out bsC outsC

theorem ppRel_combPortFacts {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : CombPortFacts raw bsC outsC) : CombPortFacts out bsC outsC

theorem ppRel_childRunN_portFacts {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : PPRel raw dsg out dout) (hr : ChildRunN children dsn n raw bsC outsC S) :
    SeqPortFacts out bsC outsC ∨ CombPortFacts out bsC outsC
```
(`Port`, `OutField`, `WEnv`, `Design` are written exactly as in the files cited when the Lean is typed; if a name needs a namespace prefix, the Lean text uses the prefix and §24 records it. The binder names above are the ones the Check's `Expected…` copies use.)

Proof plan (a plan, not a result): `ppRel_ports` — `rcases h` into the four equations, then `dropZeroWidthModule` is `m` or `{ m with … }` (`unfold; split <;> rfl` for name/inputs/outputs) and `mergeChecked_ports` / `mergeChecked_name`. `ppRel_design_names` — `rcases h`; `List.map_map` and the name of `if x.name == raw.name then f x else x` is `x.name` because `f` preserves names. The `SeqPortFacts`/`CombPortFacts` transfers rewrite `out.inputs`, `out.outputs` with `ppRel_ports` (each conjunct reads only those two fields and `bsC`/`outsC`). `ppRel_childRunN_portFacts` — `rcases hr` into `SeqChildRunN`/`CombChildRunN`, take its first six conjuncts (they ARE `SeqPortFacts`/`CombPortFacts raw`, by the definitions above) and apply the transfers. If a step does not go through the unit reports "not closed in this attempt" with the failing step.

### 23.4 Supplier table
| part | supplier | status |
|---|---|---|
| `out.name/inputs/outputs = raw.…` | `dropZW_name`, local `inputs`/`outputs` unfolding, `mergeChecked_ports`, `mergeChecked_name` | proof planned |
| design names / `topModule` | `List.map_map` + the above | proof planned |
| six non-run conjuncts of `SeqChildRunN` / `CombChildRunN` for `out` | `ppRel_ports` rewriting | proof planned |
| the run conjunct (`RunOn … T ins s vals`) for `out` | none found: needs `ChildRunN raw → ChildRunN out` for `dzStmt`-rewritten body outside `PostReady`; for the `mergeChecked` accept case `refineCheck_transfer` is the closest | **unsupplied / route not found in this survey** |
| the design side (`moduleByName dsn.modules out.name = some out`, `Dc`-extension premise of `ChildShips`) | not looked at beyond names | not in this unit |

### 23.5 Planned checks (new files only; nothing run)
Files: `Tools/ShippingGen4FbPP.lean`, `Tests/Gen4/FbPPCheck.lean`, two `lean_lib` entries in `lakefile.lean`. The common checker shape requested for this unit:
1. TYPE: `PPRel`, `SeqPortFacts`, `CombPortFacts` (definition VALUES) and the five theorems against `Expected…` typed again in the check file from §23.3 (not copied from the Lean file), by ONE reducible comparator (`==`, then logged `isDefEq` fallback, fallbacks counted separately), the same comparator for positive and negative cases.
2. MUTANTS (well-typed single changes to the Expected; signature/defeq rejections, NOT semantic counterexamples): `PPRel` with `!=` in `top`; with the second disjunct's `dout` not rewritten by `mergeChecked`; with `mergeChecked` missing in the second `out`; `ppRel_ports` with a conjunct dropped / `out.inputs = dsg…` replaced by `out.outputs = raw.inputs`; `ppRel_design_names` without `topModule`; `ppRel_seqPortFacts` concluding `CombPortFacts`; `ppRel_combPortFacts` with the hypothesis `SeqPortFacts`; `SeqPortFacts` with the `"rst" ∈` conjunct dropped; `CombPortFacts` with `"clk" ∉` turned into `"clk" ∈`; `ppRel_childRunN_portFacts` concluding the `Seq` disjunct only; with the `PPRel` hypothesis dropped.
3. REACH/closure audit (common form): the walker tests the ROOT itself against the forbidden prefix `Tools.ShippingMemo` before expanding (root self-judgement), then the type and body of every reached constant (raw `Expr.proj` structure names included); a constant not found in the environment is recorded in `missing`, and `missing ≠ 0` makes the audit FAIL ("not established"). Controls with the same walker: root = a forbidden constant itself (flagged); absent root; a helper whose VALUE mentions an absent name; an existing helper whose TYPE only mentions an absent name; fixtures using `memoInv_hit` directly, through one helper, and `outer_miss` (flagged); a clean fixture and the built `a4_inv_tail_fin0_both` (not flagged, `missing = 0`). The invalid fixtures (declarations that mention absent names) are added with `addDeclWithoutChecking` inside `withoutModifyingEnv`, so the Check leaves the environment unchanged. The intended names are asserted (the audit list is compared with the expected list of new declarations; a name absent from the environment fails).
4. AXIOMS ⊆ {propext, Classical.choice, Quot.sound}, `sorry` 0, no `native_decide`.
5. Counts in reports are actual numbers of checks that ran by category with the aggregation rule stated; summary lines excluded. A Pod build by this unit is not a clean build; the clean issue-linked build is the coder's.

### 23.6 What this section does not claim
- T-PP is NOT supplied: only its port/shape part. The run part of `ChildRunN` after `dropZeroWidthModule` / `mergeChecked` is unsupplied (route not found in this survey), so `PPTransportStmt` (§12.6) is not provable from this unit.
- T-LEG, T-MEMO (hit, nested miss, K4) are unsupplied; no law is added; §19.4 / §21.3 remain the text for the user to decide. `R4OutStmt` is not provable from it; Issue, M4 and FG are not complete.

---

## 24. FB-14 implementation status (docs; Pod build only)
- `Tools/ShippingGen4FbPP.lean` (`PPRel`, `SeqPortFacts`, `CombPortFacts`, `dropZW_outputs`, `ppRel_ports`, `ppRel_design_names`, `ppRel_seqPortFacts`, `ppRel_combPortFacts`, `ppRel_childRunN_portFacts`) and `Tests/Gen4/FbPPCheck.lean`; two `lean_lib` entries appended to `lakefile.lean`. Types as §23.3 plus the helper `dropZW_outputs` (a local lemma, `unfold; split <;> rfl`; `mergeChecked_name` is `Tools.ShippingMachineDepthRun.mergeChecked_name`). No built file, shared definition or compiler touched. The Lean was written after the §23 commit (3d58fd03) but before any review of §23.
- Pod builds (exit 0, each alone, NOT clean issue-linked builds): `Tools.ShippingGen4FbPP` (701 jobs), `Tests.Gen4.FbPPCheck`. Check output by category: TYPE OK 8 (3 definition values, 5 theorems; all syntactic, logged isDefEq fallbacks 0); MUTANT REJECTED 12 (5 on definition values, 7 on theorems; well-typed single changes, signature/defeq rejections, NOT semantic counterexamples); REACH 9 (new declarations incl. helper; `missing = 0`, no `Tools.ShippingMemo.*`); controls 10 (absent root; forbidden root judged itself; 3 unknown-name fixtures added with `debug.skipKernelTC` inside `withoutModifyingEnv`: helper value / helper type / via helper, each missing 1 and not passed; clean fixture not flagged, env restored; raw proj; 3 bad real fixtures flagged; 3 clean not flagged); AXIOMS OK 9 (standard axioms or fewer). `sorry` 0. Counts are numbers of checks that ran by category; summary lines excluded.
- Not supplied: the RUN conjunct of `ChildRunN` after `dropZeroWidthModule`/`mergeChecked` (so `PPTransportStmt` is not provable from this), T-LEG, T-MEMO (hit, nested miss, K4), machine-route meaning; no law adopted; Issue / M4 / FG are not complete. The clean issue-linked build is the coder's.

## 25. FB-15: next unit after T-PP-PORTS — survey of the unsupplied rows and the design lookup of `PPRel` (rev14; text for review; NOT Lean, NOT implemented)

- **Status.** Docs, committed BEFORE any Lean of this unit; Lean waits for the reviewer's approval of this section. Base `beb75594` (header sync of FB-14, comments/docs only; FB-14 `67756b3c` approved with limited scope, build `fb14v-67756b3c` exit 0, 812 jobs). No new law, no `Laws` field, no TRUSTED boundary, no shared-definition / compiler edit, no FG/guarantee change. "Unsupplied / route not found in this investigation" means this investigation found no supplier in the files read; it does not say a row is false or underivable. Mutants in the planned check are signature/defeq rejections, not semantic counterexamples.

### 25.1 Rows (unsupplied rows and what closes from existing lemmas)
| row | existing names read (file) | closes from existing lemmas? | verdict |
|---|---|---|---|
| real run → `PPRel` (that the entry's `(out, dout)` IS `PPRel raw dsg …`) | `synthesizeCombinational_design` (`ShippingMachineDepthRunR.lean`, concludes `M' = dzm M ∨ M' = mergeChecked (dzm M)` and `∀ y ≠ M.name, moduleByName D'.modules y = moduleByName D.modules y`, i.e. NOT the `PPRel` equation for the design `dout`); `moduleByName_post_other` (`ShippingSeqParentAt.lean`, takes `y2 = topMap … ∨ …` as hypothesis); `topshare_entry_run4_ret` (`y.2 = topMap M.name f Dg`) | the module part and the "other names" lookup are already supplied; `PPRel`'s design equation (`dout = top … dsg` as a value) is a restatement of `topMap`/`RunsTo` data I did not connect here | **real run → `PPRel`: unsupplied / route not found in this investigation** (a route probably goes through `topshare_entry_run4_ret`; not examined to the end) |
| `PPRel` design lookup of the entry's OWN name | `moduleByName_map_other` (other names only), `moduleByName_post_other` (other names only); `grep moduleByName.*topMap`, `moduleByName_map_self/same` found no lemma for the entry's own name | **yes**: one induction on the list with `dropZW_name` / `mergeChecked_name` | **selected (this unit)** |
| `ChildRunN` run conjunct across `dzStmt` / `mergeChecked` | `refineCheck_transfer` (`ShippingRefineSoundness.lean:1039`), `dropZeroWidth_entry` family needing `PostReady` | no: unchanged from §23.1 | unsupplied / route not found in this investigation |
| T-LEG (miss arm) | unchanged from §23.1 | no | unsupplied / route not found in this investigation |
| T-MEMO hit | `memoInv_hit` over `RefLawsM`; a law there is the user's decision | no, and no law is added | unsupplied on the examined route; no law proposed here |
| T-MEMO nested miss / K4 | statements only | no | unsupplied / route not found in this investigation |

### 25.2 Selection and reason
First unit: **T-PP-LOOKUP**. It is the one row whose supply is existing lemmas plus a list induction, with no law and no shared definition, and it is a premise of the design side of `ChildShips` (`moduleByName dsn.modules out.name = some out`, `ShippingGen2Defs.lean:90-91`): FB-14 §23.4 listed that side as "not in this unit". It is a partial supply: it relates lookups in `dout` to lookups in `dsg`; it does not transport `ChildRunN`, nor `DesignSV`, nor the run conjunct. It is not "real run → PPRel".

### 25.3 Complete types (target)
New file `Tools/ShippingGen4FbPPLookup.lean` (`import Tools.ShippingGen4FbPP`, `import Tools.ShippingMachineDepthRunR`, `set_option autoImplicit false`), namespace `Tools.ShippingGen4FbPPLookup`; `moduleByName` is `Sparkle.IR.Machine.moduleByName`, `mergeChecked_name` is `Tools.ShippingMachineDepthRun.mergeChecked_name` (prefix written as the files have it when typed; recorded in §26). `Module` is `Sparkle.IR.AST.Module`.
```lean
theorem moduleByName_map_self (N : String) (f : Module → Module) (hf : ∀ x, (f x).name = x.name) :
    ∀ (l : List Module) (x : Module), moduleByName l N = some x →
      moduleByName (l.map fun y => if y.name == N then f y else y) N = some (f x)

theorem ppRel_lookup_self {raw : Module} {dsg : Design} {out : Module} {dout : Design}
    (h : Tools.ShippingGen4FbPP.PPRel raw dsg out dout)
    (hraw : moduleByName dsg.modules raw.name = some raw) :
    moduleByName dout.modules out.name = some out

theorem ppRel_lookup_other {raw : Module} {dsg : Design} {out : Module} {dout : Design}
    (h : Tools.ShippingGen4FbPP.PPRel raw dsg out dout) :
    ∀ y : String, y ≠ raw.name → moduleByName dout.modules y = moduleByName dsg.modules y
```
Proof plan (a plan, not a result): `moduleByName_map_self` — induction on `l`; head `y` with `y.name == N`: `find?` returns `f y` (name `N` by `hf`), and `moduleByName (y :: _) N = some y` gives `x = y`; head with `y.name ≠ N`: unchanged head, `find?` continues, `ih`. `ppRel_lookup_self` — `rcases h` into the two disjuncts, `subst`, `ppRel_ports`-style name equations (`out.name = raw.name`) and `moduleByName_map_self` once (disjunct 1: `f = dzm`) or twice (disjunct 2: `dzm` then `mergeChecked`; the result of the first map is `some (dzm raw)` and the second maps it to `some (mergeChecked (dzm raw))`, which is `out`). `ppRel_lookup_other` — `rcases h`, `moduleByName_map_other` once or twice (existing, `ShippingMachineDepthRunR.lean:60`). If a step does not go through the unit reports "not closed in this attempt" with the failing step.

### 25.4 Planned checks (new files only; nothing run)
Files: `Tools/ShippingGen4FbPPLookup.lean`, `Tests/Gen4/FbPPLookupCheck.lean`, two `lean_lib` entries in `lakefile.lean`; the FB-14 Check gets the type-only-helper fixture of §25.5 (same Lean commit). Same requirements as §23.5: (1) TYPE against independently typed `Expected…` by one comparator (`==` then logged `isDefEq`, fallbacks counted separately); (2) MUTANTS, well-typed single changes only (`ppRel_lookup_self` with `out.name` replaced by `raw.name` is NOT a mutant (defeq after `ppRel_ports`), so the mutants are: conclusion `none`; hypothesis `hraw` dropped; `ppRel_lookup_other` with `y ≠ raw.name` dropped or `dout`/`dsg` swapped; `moduleByName_map_self` conclusion `some x`; hypothesis `hf` dropped); (3) closure audit with root self-judgement, `missing` failing the audit, controls inside `withoutModifyingEnv` (absent root, forbidden root, helper VALUE unknown, **root → existing helper whose TYPE only is unknown**, via helper, raw proj, real bad/good fixtures); (4) AXIOMS standard only, `sorry` 0; (5) real counts and the aggregation rule. A Pod build by this unit is not a clean build; the clean issue-linked build is the coder's.

### 25.5 Audit supplement for FB-14's check (same Lean commit)
`fxTypeUnknown` of `Tests/Gen4/FbPPCheck.lean` is a root whose TYPE is the unknown name (direct). Added: an existing helper `fxTypeHelper` whose TYPE only is `ghostName`, and a root `fxRootViaTypeHelper : True := (fun (_ : True) => True.intro) fxTypeHelper` that mentions `ghostName` nowhere (not in its type, value or λ-binder types), so the walker can only see the ghost through the helper's type. Assertion: `fbReach fxRootViaTypeHelper` has `ghostName ∈ missing` (the intended name, not just `missing.size ≥ 1`) and `auditOk` is false; all inside `withoutModifyingEnv`; the environment is checked to be restored. Also the misleading comment above `fxViaHelper` is reworded.

### 25.6 What this section does not claim
Real run → `PPRel`, the run conjunct of `ChildRunN` after the clean-up, T-LEG, T-MEMO (hit, nested miss, K4) stay unsupplied; no law is adopted; `PPTransportStmt` and `R4OutStmt` are not provable from this unit; Issue, M4 and FG are not complete.

## 26. FB-15 freeze corrections (reviewer's §25 approval notes; docs; committed BEFORE the Lean of this unit)

- **§25.4 correction.** The clause "`ppRel_lookup_self` with `out.name` replaced by `raw.name` is NOT a mutant (defeq after `ppRel_ports`)" is replaced by: `out.name` and `raw.name` are interchangeable in that statement by a **propositional** equation (`ppRel_ports h : out.name = raw.name ∧ …`, used as a rewrite inside the proof), not by definitional equality; an equation obtained from a proof is not a defeq. The statement with `raw.name` is therefore not planned as a mutant, which is a choice of the plan (the comparator might or might not distinguish them), not a claim about defeq.
- **Own-name lookup already exists on another branch.** `moduleByName_topMap_self` / `find_map_self` in `Tools/ShippingGen5DCEntryN.lean` (`kjob/g5dc-r13` `6d6c9b22`, approved there) state the same own-name first-match fact for `topMap`. This unit does not investigate the overlap further. `moduleByName_map_self` of §25.3 is written locally (this branch does not contain that file); at integration the existing supply is to be reused and the local theorem may then be derived from it or dropped. No claim of equivalence of the two statements is made here.
- **Nodup.** No `Nodup` of module names is assumed by any of the three theorems; they are about the first match of `List.find?`, which is what `moduleByName` is.
- **Audit supplement (§25.5), exact form.** The root `fxRootViaTypeHelper` mentions `ghostName` nowhere (not in type, value, or λ-binder types); the assertion is `ghostName ∈ missing` (the intended name) and `auditOk = false`, inside `withoutModifyingEnv`, with the environment checked to be restored.
- Counting rule for the Check (§25.4 (5)): TYPE = number of `checkExpected` calls; MUTANT = number of `checkMutant` calls (signature/defeq rejections, not semantic counterexamples); AXIOMS = number of `checkAxioms` calls; REACH = intended names audited; CONTROL = number of control log lines.

## 27. FB-16: build record of FB-15, and the next unit — real run → `PPRel` (rev15; text for review; NOT Lean, NOT implemented)

- **Status.** Docs, committed BEFORE any Lean of this unit; Lean waits for the reviewer's approval of this section. Base `18c4fc76` (comments-only header sync of `43b31a15`). No new law, no `Laws` field, no TRUSTED boundary, no shared-definition / compiler edit (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean` untouched), no FG/guarantee change. "Unsupplied / route not found in this investigation" means this investigation found no supplier in the files read; it does not say a row is false or underivable. Mutants in the planned check are signature/defeq rejections, not semantic counterexamples.
- **FB-15 build record.** Clean issue-linked build `fb16v-43b31a15` exit 0 (814 jobs, dirty=false); `FbPPLookupCheck` + `FbPPCheck`: TYPE 11 / MUTANT 20 / AXIOMS 12 (standard axioms only), `sorry` 0; reviewer approved at `43b31a15`, scope limited to `moduleByName_map_self` / `ppRel_lookup_self` / `ppRel_lookup_other` and the type-only-helper audit supplement. Not Issue completion.

### 27.1 Rows (what closes from existing lemmas)
| row | existing names read (file) | closes from existing lemmas? | verdict |
|---|---|---|---|
| **real run → `PPRel`** (that a run of the full entry returning `(M', D')` has `PPRel M D M' D'` for the core run's `(M, D)`) | `synthesizeCombinational_design` (`ShippingMachineDepthRunR.lean:82`) and `synthesizeCombinational_designTop` (`ShippingDesignWriterRun.lean:69`): both `unfold synthesizeCombinational synthesizeCombinationalWith`, take `RunsTo.bind`, `RunsTo.ite`, `RunsTo.pure`, and after `subst` of the returned pair have `M'` as the one or two cleaned-up forms and `D'` as the literal `{ D with modules := … map … }` term. They keep the module disjunction and the lookups but discard the design equation. `PPRel` (FB-14) is that very disjunction paired with the design equation. | **yes**: the same proof text with the design equation kept (`rfl` in each branch). | **selected (this unit)** — earlier text (§25.1) said "a route probably goes through `topshare_entry_run4_ret`, not examined to the end"; this investigation found that it does not need `topshare_entry_run4_ret`. |
| `ChildRunN` run conjunct across `dzStmt` / `mergeChecked` | `refineCheck_transfer` (`ShippingRefineSoundness.lean:1039`), `dropZeroWidth_entry` family needing `PostReady` | no (unchanged from §23.1/§25.1) | unsupplied / route not found in this investigation |
| T-LEG (miss arm) | unchanged from §23.1 | no | unsupplied / route not found in this investigation |
| T-MEMO hit | `memoInv_hit` over `RefLawsM`; a law there is the user's decision | no, and no law is added | unsupplied on the examined route; no law proposed here |
| T-MEMO nested miss / K4 | statements only | no | unsupplied / route not found in this investigation |

### 27.2 Selection and reason
First unit: **T-PP-RUN** (`synthesizeCombinational_ppRel` and a lookup corollary). It is the only remaining row whose supply is an existing proof pattern with one extra `rfl`; it connects FB-14/FB-15 (`PPRel`, `ppRel_*`) to an actual run of the full entry, so `PPRel` is no longer only a hypothesis. It does NOT transport `ChildRunN`'s run conjunct, `DesignSV`, or anything about what `(M, D)` computes. Overlap: the `top`-rewrite lemmas of `kjob/g5dc-r13` (`moduleByName_topMap_self`) are for integration, not re-investigated here.

### 27.3 Complete types (target)
New file `Tools/ShippingGen4FbPPRun.lean`, namespace `Tools.ShippingGen4FbPPRun`; imports `Tools.ShippingGen4FbPPLookup` and `Tools.ShippingMachineDepthRunR` (the second is already in the Lookup file's closure; `Tools.ShippingDesignWriterRun` is NOT imported); `set_option autoImplicit false`; `open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine Sparkle.Compiler.Elab`, `open Tools.ShippingEntrySoundness (RunsTo)`, `open Tools.ShippingGen4FbPP Tools.ShippingGen4FbPPLookup`. `Module` is `Sparkle.IR.AST.Module`, `Design` is `Sparkle.IR.AST.Design`, `synthesizeCombinational` / `synthesizeCombinationalCore` are `Sparkle.Compiler.Elab.…`. Binder names are those of `synthesizeCombinational_design`.
```lean
theorem synthesizeCombinational_ppRel {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      Tools.ShippingGen4FbPP.PPRel M D M' D'

theorem synthesizeCombinational_lookup {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      Tools.ShippingGen4FbPP.PPRel M D M' D' ∧
      (Sparkle.IR.Machine.moduleByName D.modules M.name = some M →
        Sparkle.IR.Machine.moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        Sparkle.IR.Machine.moduleByName D'.modules y = Sparkle.IR.Machine.moduleByName D.modules y)
```
Proof plan (a plan, not a result): first theorem — exactly the text of `synthesizeCombinational_design` up to `rcases RunsTo.ite h`; in the `SPARKLE_NO_REGDEDUP` branch (`(m', d)`) after `subst` close `PPRel` by `Or.inl ⟨rfl, rfl⟩`, in the other branch by `Or.inr ⟨rfl, rfl⟩` (after `unfold PPRel` / `show`; the `let top` of `PPRel` is the `let top` of `synthesizeCombinationalWith`, so both sides are the same term — to be seen by the elaborator, not assumed). Second theorem — first theorem, then `ppRel_lookup_self` and `ppRel_lookup_other` (FB-15). If a step does not go through the unit reports "not closed in this attempt" with the failing step; the `top`-binder `raw.name` vs `m.name` match is the step most likely to need a `show`.

### 27.4 Planned checks (new files only; nothing run)
Files: `Tools/ShippingGen4FbPPRun.lean`, `Tests/Gen4/FbPPRunCheck.lean`, two `lean_lib` entries in `lakefile.lean`; no change to FB-14/FB-15 files. Same requirements as §23.5/§25.4: (1) TYPE: both theorems against independently typed `Expected…` in the Check (one comparator: `==`, then logged `isDefEq`, fallbacks counted separately); (2) MUTANTS, well-typed single changes only: first theorem — conclusion `PPRel M D M' D'` replaced by `PPRel M' D' M D`; `PPRel M D M' D` (design not the returned one); the core run `synthesizeCombinationalCore declName [] true` (flag changed); `w1` replaced by `w'`; second theorem — `PPRel` conjunct dropped; `y ≠ M.name` dropped; the self-lookup conclusion `… M.name = some M`; the hypothesis premise `… = some M` dropped; `D'`/`D` swapped in the other-name conjunct; (3) closure audit with root self-judgement, `missing` failing the audit, controls inside `withoutModifyingEnv` (absent root, forbidden root `Tools.ShippingMemo`, helper VALUE unknown, root → existing helper whose TYPE only is unknown, raw proj, real bad/good fixtures) — reusing `fbReach`/`auditOk`/`addFixture`; (4) AXIOMS standard only, `sorry` 0; (5) real counts by category and the aggregation rule. A Pod build by this unit is not a clean build; the clean issue-linked build is the coder's.

### 27.5 What this section does not claim
The `ChildRunN` run conjunct across the clean-up, T-LEG, T-MEMO (hit, nested miss, K4), and the connection of `(M, D)` to what the entry computes stay unsupplied; no law is adopted; `PPTransportStmt` / `R4OutStmt` are not provable from this unit; Issue, M4 and FG are not complete.
