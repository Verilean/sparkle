# M4: fallback / legacy / memo-hit success routes — freeze (rev3, FOR REVIEW; rev1 = f92e2410, rev2 = a7f9753b)

- **Issue:** `sparkle-gen4-fallback-supply` (milestone `sparkle-gen4`; depends on `sparkle-gen4-routes`, done).
- **Base:** branch `kjob/g4fb-d0ddc50b` at d0ddc50b (rev3 is written on `kjob/g4fb-r3`, branched from a7f9753b). All `file:line` below are at that SHA. `Sparkle/Compiler/Elab.lean`
  is identical to `par/gen2-spec` there, so the lines in `scripts/gen2/ROUTE_CENSUS.md` still apply.
- **Status:** docs only. No Lean, no build, no production edit. This freeze has to be approved before any Lean is written.
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
`MemoInvShips`, `MemoHitShips`, the K4 invariant `memo-names ⊆ childCache-names ∪ {top}`. Whether such a bundle/mapping is only a re-packaging or conditional transport of existing laws (design work) or adopts a new real-environment guarantee (the only case needing a user decision) is OPEN (§0 R3, §7 D-MEMO-LAW). K4 remains a reading of the source, **not proved**. Until this part is designed, the memo-hit case of `TookLegacyTail` (§5.2) is uncovered by any conclusion.

### 5.7 First implementation unit (applies only after rev3 is approved AND gate U-G1 is built)
Contents (small, definitions only): the `LegacyTailRunExists` definition of §5.2, in a new file of this Issue (e.g. `Tools/ShippingGen4FbTail.lean` + `lean_lib` entry in lakefile.lean; imports `Tools.ShippingGen2Defs`, `Tools.ShippingMachineOutcomeA`), and a check file that records its type and `#print axioms`, plus signature-level mutants (e.g. dropping `JQC O n w9`; replacing `legacyTail … ci` by another term) rejected by signature/defeq — **not** semantic counterexamples.
It contains: no interface record (gate U-G1), no `LegacyChildShips`, no memo definition, no claim about a run. If gate U-G1's built text differs from §0's table, the unit does not start until the table is re-frozen.
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

If this freeze is approved, the first Lean unit is §5.7 (new file; one existence-predicate definition; no supply; after gate U-G1 is built). The memo side (§5.6), L1-L4 and M-1 remain read-only research until their own design is frozen.

## 8. What is NOT claimed
- No statement that a fallback, legacy or memo-hit success is impossible, non-derivable or unreachable. K4 is a reading of the source, not a theorem.
- No result about the corpus (which declarations fall back); N2/`kidsCombB` is read from code, not measured.
- No change to FG, `T1Hyp`, `GenWF`, TRUSTED boundaries or any law. `T1Hyp.closes` is described, not edited.
- Nothing here is conditional-on-new-hypothesis presented as done; §6 lists where each path stops.
- rev3 does not claim that an R4-local producer is provable, that R6-direct is coverable, or that any memo statement holds; K4 is unproved; `LegacyTailRunExists` is an existence predicate and is not evidence about a given run; no Lean was written or built.
