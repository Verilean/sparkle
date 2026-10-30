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
