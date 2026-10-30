# M4: fallback / legacy / memo-hit success routes — freeze (rev1, FOR REVIEW)

- **Issue:** `sparkle-gen4-fallback-supply` (milestone `sparkle-gen4`; depends on `sparkle-gen4-routes`, done).
- **Base:** branch `kjob/g4fb-d0ddc50b` at d0ddc50b. All `file:line` below are at that SHA. `Sparkle/Compiler/Elab.lean`
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

## 2. Run telescopes (complete, in execution order)

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

## 5. Proposed connection to the common semantic interface (types; NOT yet in Lean)

Today `ChildShips q n mc Dc` and `TopShips p n declName b raw D` are keyed on a machine package `q p : Pkg ι dom` (GEN2_DEFS.lean.txt:87, :273). The census (ROUTE_CENSUS §5) proposed
ONE common child interface with route-specific PRODUCERS. Stated here as types, for review. They are additive (new file, new names); no existing definition changes.
```lean
/-- The route-agnostic data `ChildShips` reads off a package (its exact right-hand side). -/
structure IfaceData (ι : Type) (dom : ι → DomainConfig) where
  bsC   : List (Name × MixedGateBinder)
  outsC : List OutField
  S     : ι → (Nat → List Nat) → List (Nat → Nat)

def Pkg.iface (q : Pkg ι dom) : IfaceData ι dom := ⟨q.d.bsIn.take q.kD, q.d.shape.layout.outs, q.S⟩

def ChildShipsD (I : IfaceData ι dom) (n : Nat) (mc : Module) (Dc : Design) : Prop :=
  ∀ dsn, (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) → moduleByName dsn.modules mc.name = some mc →
    ∀ i, ChildRunN (childMap dsn.modules) dsn n mc I.bsC I.outsC (I.S i)
-- bridge to prove: ChildShips q n mc Dc ↔ ChildShipsD q.iface n mc Dc   (by unfolding; expected `Iff.rfl`)
```
`TopShips` needs the machine-specific fields (`p.d.ss`, `p.extS`, `p.src`, `p.kD`). For a non-machine top the analogue is route data of a separate type
(`SemPkg` of DG-SEM in `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` §0 table); this freeze does NOT define it. A common top statement `TopShipsD` is therefore left as an open design
point (§7, D-IFACE).

The three connection statements this issue would have to prove (types only; `Fallback`/`Legacy`/`MemoHit` are the evidence predicates of §2):
```lean
-- R6 direct and R4's tail: the run took the legacy tail; produce interface data that ships
def LegacyShips (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c mctx cctx w w1 raw b D, Reach c → Start L mctx cctx w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) →
    TookLegacyTail c raw D w w1  →                               -- evidence of THIS run (analogue of `MachineTaken`), to be defined: R6 direct, or R4 with `r = none`
    ∃ (I : IfaceData ι dom) n, ChildShipsD I n b D

-- R5: the cached value ships because it was produced by a run that did (needs the K4 / K2 facts)
def MemoHitShips (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c w r, Reach c → MemoInvShips L P Reach w → (L.mval w).get? c = some r →
    ∃ I n, ChildShipsD I n r.1 r.2                              -- `MemoInvShips`: `MemoInv L (ShipsPre …)`, new; see §6 M-1
```
Also required, and not typed here because it depends on D-IFACE: the extension of `T1Hyp.closes` (Gen2Defs.lean:208, "declarations where it fails are route 4 (M4), not removed from FG")
to a route-indexed scope, so that a reached declaration that is NOT in `closes` is routed to `LegacyShips` rather than assumed away. `T1Hyp.closes` is the premise that currently
EXCLUDES R4 (`MachineClosesAtA`, ChildRunAKids:158); using R4 in FG means replacing that exclusion by a case split, which edits `T1Hyp` (shared; forbidden here, hence a proposal).

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
 If instead nested hits DO occur (K4 false), the memo returns the K2 raw value for a name whose `childCache` entry is absent, and `MemoHit ⇒ ShipsRes` needs the writer's `ShipsRes` carried as `MemoInv L (ShipsPre …)`. That carries a stored meaning for "SOME constant" (`stored Ψ`, K1), not for the reader's constant (docs/parallel/B-memo.md §5 per the MemoInv header).
**M-2 Memo at the top.** Path: `outer_miss` (proved from `RefLawsM`). No further obligation at the top; the top is never a hit.

**Summary of where the chain stops.** For the R6/R4-tail successes this investigation found NO path that supplies, from the declaration and the run, a `ChildRunN`/`TopShips`-level statement; the contract that exists is the scalar-combinational `RawValueAt`
under a hypothesised `LegacyDom`. Paths L-2 (and any D-IFACE option that changes shared semantic definitions) need a user decision. For R5, M-1 is a plausible but unproved invariant; no supplier was found.

## 7. Decision points surfaced by this freeze (user's, NOT decided here)

- **D-IFACE.** The common interface for non-machine tops (`TopShipsD`/`SemPkg`) — new definition(s); allowed only as new files, but the FG statement's meaning for non-machine tops is part of the guarantee.
- **D-LEGACY-SCOPE.** If L-1/L-2 cannot be completed, FG holds for legacy successes only with an explicit legacy contract (GENERAL_SPEC M4 risk, :485). Guarantee impact: declarations whose compilation falls to the legacy tail (R6, or R4 with `closeLets`/`closeInsts` = none)
  would be outside the proved guarantee, or covered by a stated contract. Accepting that is a user decision; scope reduction is not made here.
- **D-GUARD.** Rejecting R4 at compile time (a compiler guard making machine declines an error) is a compiler change under the output policy; not proposed for approval here.

If this freeze is approved, the first Lean unit would be (new file only): definitions `IfaceData`, `Pkg.iface`, `ChildShipsD` and the bridge `ChildShips ↔ ChildShipsD`, together with `TookLegacyTail` as an evidence predicate and an `EnvQCheck`-style type check; no supply is claimed by it. A later unit would be M-1's invariant statement. Neither is started.

## 8. What is NOT claimed
- No statement that a fallback, legacy or memo-hit success is impossible, non-derivable or unreachable. K4 is a reading of the source, not a theorem.
- No result about the corpus (which declarations fall back); N2/`kidsCombB` is read from code, not measured.
- No change to FG, `T1Hyp`, `GenWF`, TRUSTED boundaries or any law. `T1Hyp.closes` is described, not edited.
- Nothing here is conditional-on-new-hypothesis presented as done; §6 lists where each path stops.
