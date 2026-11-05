# BOUNDARY-AUDIT freeze r1 (docs only; no Lean yet)

Issue: `sparkle-gen5-boundary-audit` (M5, N1 / G5 / G7 audit). Base: `kjob/g5cr-r6` f3a29dbb.
Sources read: `scripts/gen2/GENERAL_SPEC.md` (§1.1-1.3, §4.3-4.4, §5, §6), `scripts/gen2/GEN2_DEFS.lean.txt`,
`docs/ShippingCompiler-Gaps-2026-10-28.md` (§1 N1/G5/G7 rows), `scripts/gen5/DG_CLOSINGRUN_FREEZE_R6.md`, and the Lean
text cited per row. "Not found" below means only that this survey did not find a supplier or route at f3a29dbb; it does
not say the row is impossible or underivable. Nothing here claims T1, FG, M5 or Issue completion.
No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing or GenWF strengthening is proposed.
Greps cited as "referenced in N files" count files that mention the field name; they are not a proof that FG's proof
term uses the field.

## 1. N1: name freshness

### 1.1 What is PROVED today
`Tools/ShippingModuleName.lean` (DECL, in tree): `decode_encode`, `encode_injective`, `ofDecl_injective`
(`ofDecl a = ofDecl b → a = b`), `ofDecl_ne`, `ofMem_injective`, `ofDecl_ne_ofMem (n) (c aw dw) : ofDecl n ≠ ofMem c aw dw`.
`Tools/ShippingNameSep.lean` `Enc.*`: decided-check wrappers (`hparent_of`, `hnames_of`, `not_mem_map_of_ne`, `nodup_map`, …).
`Tools/ShippingSrm12Corr.lean`: `kidTA_name : KidTA O o c y → (o.child? = none → RealChildA O c y → y.1.name = ofDecl c) →
y.1.name = kidModName (c, o)`; `Tools/ShippingSrm7Rank.lean`: `kidModName (c, .mem cb aw dw) = ofMem cb aw dw`, else `ofDecl c`.
These cover MODULE names only (Gaps §1 N1 row).

### 1.2 Where an N1-shaped premise enters the FG chain (real names)
In the FG statement (§1.1) there is no name binder. Searching `Tools/ShippingGen2*.lean`, `Tools/ShippingGen5*.lean` for
`outHead|hfresh|hsep|hparent|disjD|NameSep` finds no name premise in them. Among the routes searched, names enter inside the supplier of the
`T1Hyp.closes` field (`MachineClosesAtA`, Gen2Defs.lean:209, G-CLOSES, itself OPEN), whose general memory-parent supplier
is `Tools.ShippingSrm3Callee.memCallee_closesA` (Srm3Callee.lean:91) over `MemCalleeData`, which calls
`Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'` (CallsMemPinned.lean:330). This survey did not search every FG route, so no exclusivity of this entry point is claimed. The N1-shaped binders found are:

| # | binder (theorem / field) | exact Prop | derivable from existing theorems? | new lemma provable (this Issue)? |
|---|---|---|---|---|
| B1 | `hsep` (`MemCalleeData.sepK`) | `∀ k (hk : k < insts.length) k' (hk' : k' < insts.length), nameK k = nameK k' → insts[k].1 = insts[k'].1 ∧ memKey (originAt shape k) = memKey (originAt shape k')` | Only after `nameK k = kidModName (insts[k].1, org k)` is known (`kidTA_name` + its premise `hn`). Then ord/field vs ord/field: `ofDecl_injective`; ord/field vs mem: `ofDecl_ne_ofMem`; mem vs mem: `ofMem_injective` gives the memKey part only. No packaged lemma found. | YES for the ord/field and mixed cases (U1 below). mem vs mem: the conjunct `insts[k].1 = insts[k'].1` does NOT follow from names (two different callee declarations could build the same `(cb,aw,dw)` memory); stays an explicit premise `hmemSame` (see 1.3). |
| B2 | `hparent` (`MemCalleeData.parent`) | `∀ k, k < insts.length → nameK k ≠ ofDecl declName` | Same `hn` as B1, plus "no self call" `insts[k].1 ≠ declName` for non-memory kids. `ofDecl_ne`, `ofDecl_ne_ofMem` finish. | YES, with premise `hself` (non-memory kid is not the declaration itself). Supply of `hself` (acyclic call graph / rank, `Srm5Deep`/`Srm7Rank`): not found as an unconditional theorem. |
| B3 | `hparentD` (`parentD`) | `∀ k, k < insts.length → ofDecl declName ∉ namesK k` (`namesK k` = module names of the kid's design) | needs the kid's design contents (`ChildIfaceP.desNames`) and acyclicity | NO (not a name-only fact). Recorded OPEN, supplier = call-graph/rank track, not N1. |
| B4 | `hdisjD` (`disjD`) | `∀ k k', ¬(insts[k].1 = insts[k'].1 ∧ memKey = memKey) → nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'` | needs design contents of two kids | NO (not name-only). OPEN. |
| B5 | `hfresh` (`MemCalleeData.outHead` + `instName_ne_of_head`, CallsGate.lean:60) | machineClosesAtA_of_memKids' form: `∀ gi k (hk : k < insts.length), ∀ o ∈ shape.layout.outs, o.name ≠ s!"inst{gi}_{nameK k}"`; the data row is the stronger `∀ o ∈ outs, o.name.toList.head? ≠ some 'i'` (a `D` row, GENERAL_SPEC §4.4) | No. Output port names come from the declaration's structure fields; this survey did not find a compiler check or theorem excluding an output named like an instance wire. Whether such a design compiles successfully was NOT checked here. | NO. Neither U1 nor any name encoding covers it (an arbitrary user string vs `inst{gi}_…`). Recorded as OPEN, row "G-CLOSES-FRESH"; the exact Prop and the generator-side `outHead` check (`ShippingNoPortsMemSeqCommand.lean:380`, throwError) are the evidence. If FG must cover such designs, a decision item (compiler-side rename or restricted scope) is for the user; not proposed here. |
| B6 | `memT`, `memNames`, `nameIn` (MemCalleeData) | memory kid tables: `nameK k = y.1.name ∧ …`, `y.1.name ∈ names ∧ y.1.name ≠ ofDecl C` | `memNames`' second conjunct is `ofDecl_ne_ofMem` once `y.1.name = ofMem …` (`Tools.ShippingMemOnlyNames.memModule_name`). `nameIn` needs `names` content. | memNames-second-conjunct: YES but tiny; included in U1 as a corollary only if it falls out (not required). `nameIn`: NO (set membership of a supplied list). |
| B7 | `hn` itself: `RealChildA O c y → y.1.name = ofDecl c` for ordinary kids (premise of `kidTA_name`, `hname_of_iface` Srm15Graph.lean:58) | the child's synthesized module is named `ofDecl c` | `ChildIfaceP.name` after the child interface is established (Srm4Core5.lean:69, Srm5Deep `post_name`); `KeyTop` clause (LeafMissCoh.lean:44). An unconditional theorem for every `RealChildA` was not found. | NO (a fact about the synthesis run, not about encodings). Stays a premise of U1. |

### 1.3 Unit U1 (first implementation unit): kid module-name separation
File (new): `Tools/ShippingGen5NameKids.lean`; check file (new): `Tests/Gen5/NameKidsCheck.lean`; two `lean_lib` entries
(`Tools.ShippingGen5NameKids`, `Tests.Gen5.NameKidsCheck`). Imports: `Tools.ShippingSrm7Rank` (kidModName),
`Tools.ShippingMemClosesKidsT` (memKey, namespace `Tools.ShippingMemCloses`), `Tools.ShippingModuleName`. Namespace `Tools.ShippingGen5NameKids`.
`open Sparkle.IR.ModuleName (ofDecl ofMem)`, `open Sparkle.Compiler.MachInstOrigin (InstOrigin)`,
`open Tools.ShippingSrm7Rank (kidModName)`, `open Tools.ShippingMemCloses (memKey)` (the file is `Tools/ShippingMemClosesKidsT.lean`, but `memKey` is declared in namespace `Tools.ShippingMemCloses`).
All statements are Props about names only; no `Laws`, no runtime, no compiler definition.

```
theorem kidModName_inj_nonmem {c c' : Name} {o o' : InstOrigin}
    (h : memKey o = none) (h' : memKey o' = none)
    (e : kidModName (c, o) = kidModName (c', o')) : c = c'

theorem kidModName_ne_mem {c c' : Name} {o o' : InstOrigin} (h : memKey o = none) (h' : memKey o' ≠ none) :
    kidModName (c, o) ≠ kidModName (c', o')

theorem kidModName_inj_mem {c c' : Name} {o o' : InstOrigin} {k k' : Bool × Nat × Nat}
    (h : memKey o = some k) (h' : memKey o' = some k')
    (e : kidModName (c, o) = kidModName (c', o')) : k = k'

theorem hsep_of_kidNames {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1) :
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k = nameK k' →
      (insts[k]'hk).1 = (insts[k']'hk').1 ∧ memKey (org k) = memKey (org k')

theorem hparent_of_kidNames {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (declName : Name)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hself : ∀ (k : Nat) (hk : k < insts.length), memKey (org k) = none → (insts[k]'hk).1 ≠ declName) :
    ∀ (k : Nat), k < insts.length → nameK k ≠ ofDecl declName
```
Why the statements are not trivial restatements: `kidModName_inj_nonmem` needs the three-way case split on `InstOrigin`
(`ord`/`field`/`mem`) and `ofDecl_injective`; `kidModName_ne_mem` needs `ofDecl_ne_ofMem` and its symmetry; `hsep` and
`hparent` combine them by index, and `hsep`'s conjunct on `memKey` for ord/field is `none = none`.
`hmemSame` and `hself` are the residual premises; they are NOT discharged by this Issue and are not new TRUSTED rows.
Plain consumer-shape check: the Check file contains `example` terms that apply `hsep_of_kidNames`/`hparent_of_kidNames`
at `insts := d.shape.insts`, `org := originAt d.shape` to produce exactly the `hsep`/`hparent` binder types of
`machineClosesAtA_of_memKids'` (a use-site type check, not a semantic claim).

Reason this is the first unit: it is the only N1-shaped row above that is both pure name algebra (no dependence on a
synthesis run, a package, or a design's contents) and is a binder of the existing G-CLOSES supplier. B3/B4/B7 need runs or
designs; B5: no supplier was found by this survey (a decision item only if FG must cover it).

### 1.4 N1 residue after U1 (what stays OPEN)
B3 `hparentD`, B4 `hdisjD`, B5 `hfresh`/`outHead`, B7 `hn`, plus the premises `hn`, `hmemSame`, `hself` of U1 (they remain; U1 is not the supply of N1 as a whole). None is claimed.

## 2. G5: `Laws` / `Start` in FG

FG (GENERAL_SPEC §1.1) binders: `L : Laws mref cref` (`Laws.O : RefLawsAOps MkRefd mref cref`,
`Laws.T : RefLawsATele O.quiet mref cref`, Gen2Defs.lean ~47) and `Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`
(Gen2Defs.lean:52). `JQC O D w := JQ O.quiet D w ∧ CacheInvA O (cv w)`, `JQ quiet D w := quiet w ∧ sv w = some synthesizeChild ∧ dv w = D`,
`CacheInvA O m := ∀ c r, m.get? c = some r → RealChildA O c r`, `AdmCtx quiet mctx _ := ∀ f, mctx.canUnfold? = some f → InertUnfold quiet f`.

Status classes: PROVED = a theorem in tree; CONTRACT = a premise of the final statement (a Prop FG assumes; approved
boundary, `Gaps §1` G5 row "CONTRACT / OPEN"); TRUSTED = a trusted-by-design boundary. Nothing is reclassified here.

| item | where it appears in FG | status | "referenced in N files" (grep `O.f`/`L.O.f`, `Tools/*.lean`) |
|---|---|---|---|
| `Laws.O.quiet` | `Start`, all `InvAt`/`JQC` | CONTRACT (field of `L`) | — |
| `O.diag` | `ChildVCA`-level walks | CONTRACT | 2 |
| `O.frameT` | throw-path frame | CONTRACT | 3 |
| `O.excOk` | exception class | CONTRACT | 4 |
| `O.frameQ` | quiet preserved by framed ops | CONTRACT | 7 |
| `O.cacheSetQ`, `O.depthSetQ` | quiet preserved by `cache.set`/`depth.set` | CONTRACT | 5, 5 |
| `O.frame` | cv/sv/dv frame | CONTRACT | 13 |
| `O.cacheSet`, `O.depthSet` | value after `cache.set` / `depth.set` | CONTRACT | 7, 8 |
| `T.telescope`, `T.lamTelescope`, `T.localDecl`, `T.letDecl` | `RefLawsATele` keep-chain (stableA_invAt U0 PROVED uses the `I → quiet` frame) | CONTRACT | 3, 2, 2, 2 (`ChildTeleCP`, `ChildWalkA`, `ChildInvA`) |
| `Start.1` `AdmCtx` | binder `Start` | CONTRACT. PROVED only for `Command.mkMetaContext` (`mkMetaContext_canUnfold`); "the entry runs there" is a reading, not a theorem (Gaps row #10) | — |
| `Start.2` `JQC O 0 w` | binder `Start` | CONTRACT (start-world invariant at depth 0, Gaps row #14); `CacheInvA` of the empty cache is PROVED (`cacheInvA_empty`) | — |
| `ReflectsAll` | separate FG binder (G3) | not G5 | — |

Note on counting: the direct fields of `Laws` are `O` and `T`. `O` unfolds to 10 fields (`quiet` among them) and `T` to 4 fields (14 fields in total, all listed in the table above, `quiet` as a field of `O`); `quiet` is also the predicate parameter of `RefLawsATele O.quiet`, which is a different role from its being a field. The earlier "all 12" was wrong and is withdrawn.

This table and §3-§4 are a PRELIMINARY inventory, not an accepted final audit. Findings from this table, no more: (a) the `O` fields (10, including `quiet`), the `T` fields (4) and `Start` are classed CONTRACT here; none is classed TRUSTED, and none is PROVED except the pointwise facts named. (b) The Gaps §1 G5 note that the old `RefLaws.frame` was REFUTED applies to the old
boundary; the present boundary's runtime fit and joint satisfiability are OPEN (Gaps row 127). (c) A model of `Laws`
(GENERAL_SPEC §5 M5 "G5: a model of `Laws`, or an explicit TRUSTED status") was not found in tree; this Issue does not
add either. A per-field use trace "which field FG's proof actually needs" is not done: it needs the closed proof term of FG,
which does not exist yet. Only the grep counts above are recorded.

## 3. G7: where the guarantee ends

Exact conclusion level (`Tools.ShippingGen2.TopShips`, Gen2Defs.lean:282): after the hypotheses, 
`∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b)) (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧ envsO.length = T ∧ ∀ j hj k o f, outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]) o.name = f j`.
So the guarantee ends at the IR interpreter `runModuleTG` on `checkedOptimize b` with child map `childMap D.modules`.

| stage after IR | exact Prop | supplier | status |
|---|---|---|---|
| (G7-a) artifact = optimized top + children | `Tools.ShippingDesignWriterRun.writer_prints_endpoint_artifact` (DesignWriterRun.lean:119): from `h : RunsTo (synthesizeHierarchical declName) … dH`, `hr : RunsTo (synthesizeCombinational declName) … (b, design)`, `hcore : RunsTo (synthesizeCombinationalCore declName [] false) … (raw, D)`, `hno : ∀ x ∈ D.modules, x.name ≠ raw.name`, `htop : D.topModule = raw.name` ⊢ `designArtifact dH = D.modules ++ [checkedOptimize b] ∧ toVerilogDesignChecked dH = String.intercalate "\n" (D.modules.map emitModule ++ [emitModule (checkedOptimize b)]) ∧ ∀ mn r, childMap D.modules mn = some r → childMap (designArtifact dH) mn = some r` | PROVED, with binders `hno`, `htop` | PROVED for those binders. Whether `hno`/`htop` hold for every successful run: not covered by this survey (they are facts about the run's `D`; supplier not found). |
| (G7-b) `_sat` endpoints: forward simulation to emitted design objects (`DesignSV`) | `TrustBase.md:1635-1659`, Gaps row 129 | PROVED for the `_sat` endpoints (C4/C5 class); NOT shown for FG's `TopShips` | the step `runModuleTG` ⇒ `DesignSV` for arbitrary `TopShips` designs: no theorem found |
| (G7-c) printed bytes | `emitModule` text → Verilog/SystemVerilog source | TRUSTED (printer), parse-back is validation only | TRUSTED by design (Gaps row 129) |
| (G7-d) downstream tools (simulator/synthesis) | — | outside | — |

GENERAL_SPEC §5 M5 accepts "G7 is TRUSTED and stated". This Issue records the stages; it does not add a trust row.
The transition (G7-b) for FG's final `TopShips` is recorded as NOT found, not as underivable.

## 4. FG final-type binder supply skeleton (rows to be filled by the supplier Issues; no row is claimed supplied here)

| binder / field | where | supplier (Issue / unit) | state at f3a29dbb |
|---|---|---|---|
| `L : Laws mref cref` | FG | G5 (§2) | CONTRACT |
| `Start L mctx cctx w` | FG | G5 (§2) | CONTRACT |
| `RunsTo (synthesizeCombinational…) ∨ …WithParameters` | FG hypothesis | — | hypothesis |
| `ReflectsAll L declName parameters` | FG | M4/M5 G3 (T2/DGEN family, package coverage) | OPEN |
| `T1Hyp.pkg` (G3-GEN) | T1 | DGEN / generator soundness | OPEN |
| `T1Hyp.defines` (G3-SHAPE) | T1 | reader bridge (`readTerm_sound`, `machineDefines_of_readsAll`) | partial; not whole FG |
| `T1Hyp.closes` (G-CLOSES) | T1 | `memCallee_closesA` etc.; N1 binders B1-B7 (§1) | OPEN (N1: U1 reduces B1/B2 only) |
| `T1Hyp.dec` (G-CALLDEC) | T1 | G3-GEN-CALL | OPEN (`T1HypND` omits it; route from ND to `dec` not found, R6 §2) |
| `T1Hyp.closed` | T1 | — | OPEN |
| `StepStmt L P DataOk` | T1 | M2-b | OPEN (R6 §2) |
| `hrow` / `hrows` | closingRun_of_run | DG-CLOSINGRUN | OPEN (R6 §2) |
| `hGen` / `GeneratedAt` | closingRun_of_run | DG-COVER / DG-WFCOVER | OPEN (R6 §2) |
| `hIH`, `hKI` at depth 1 | closingRun0_of_run | `ih_allPF` (needs the rows above) | OPEN |
| depth-0 `stop` (`InvAt 0 w'`) | closing | — | route not found (R6 §2) |
| non-vacuity witness | closing / T1 | — | none in tree |
| G7 IR→DesignSV, printer | after `TopShips` | §3 | PROVED (G7-a with binders) / TRUSTED (G7-c) / not found (G7-b for FG) |

Supplier Issue IDs for the OPEN rows other than this Issue are not asserted here; they are read from `managerctl` when the
final audit table is made.

## 5. U1 checks (written from the statements above, not from the implementation's signatures)

* **Expected TYPEs**: in `Tests/Gen5/NameKidsCheck.lean`, each of the five theorems of §1.3 is re-stated as an independent
  `def Exp… : Prop` using only the text of §1.3 (no import of the implementation's signatures into the Expected defs).
  `Tests.Gen3.ExpectedType`/`ClosingRun2Check` comparator machinery (`cmpEqR`, `checkExpectedR`, `checkMutantR`, reducible
  `isDefEq` fallback) is the ONE comparator used for positives and mutants.
* **Positive controls** (same comparator): the five Expected statements accepted; one existing Expected from
  `ClosingRun2Check` re-accepted as a comparator sanity check.
* **Mutants** (single change, well-typed, written from the same text; rejection is by signature/defeq, NOT a semantic
  counterexample): (1) `c = c'` → `c ≠ c'` in `kidModName_inj_nonmem`; (2) `memKey o = none` → `memKey o ≠ none` for one
  hypothesis; (3) drop the conjunct `memKey (org k) = memKey (org k')` from `hsep_of_kidNames`; (4) drop the conjunct
  `insts[k].1 = insts[k'].1`; (5) drop `hmemSame`; (6) drop `hself`; (7) `ofDecl declName` → `ofMem true 0 0` in
  `hparent_of_kidNames`; (8) `nameK k = nameK k'` → `nameK k ≠ nameK k'`. Counts reported as: MUTANT n (rule: each distinct
  mutant def is counted once; a mutant accepted by the comparator is a FAIL of the run).
* **Closure** (value + type constants of each theorem, transitive over the project namespace): unknown/unresolved name ⇒
  `throwError`. Negative controls: a root fixture that references a forbidden constant (`Lean.ofReduceBool`, as in the ClosingRun2 fixtures), a helper-VALUE fixture reaching it through one helper theorem's proof, a helper-TYPE
  fixture reaching it through a helper definition's type; each must be rejected. Clean control: a fixture over a clean
  constant accepted. Counts reported as `controls n` with the aggregation rule stated in the file header.
* **AXIOMS**: `#print axioms` of each new theorem is a subset of `[propext, Classical.choice, Quot.sound]`; no `sorry`,
  no `native_decide`, no new `axiom`.
* Numbers in the result report are actual counts per category (TYPE, MUTANT, controls, closure, AXIOMS) with the
  aggregation rule written next to them; no total is quoted without its categories.
* Build: `kjob lake build Tools.ShippingGen5NameKids` then `kjob lake build Tests.Gen5.NameKidsCheck`, one at a time; the
  clean exact-head build is run by the coder (this Issue stays `doing` after the Lean commit).

## 6. What this freeze does not do
No change to any compiler, production, shared-definition file (`Tools/ShippingGen2Defs.lean`, T1Hyp, T1HypND, `Elab*.lean`).
No new TRUSTED boundary/law, no FG/guarantee change, no GenWF strengthening, no `sorry`/`axiom`/`native_decide`.
B5 (`hfresh`) is a candidate for a user decision only if FG is required to cover designs whose output is named like an
instance wire; this freeze does not raise that decision, it records the exact Prop and that no supplier was found.
