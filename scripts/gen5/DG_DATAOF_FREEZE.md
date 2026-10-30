# DG-DATAOF full-type freeze, rev1 (Issue sparkle-gen5-dg-dataof)

rev1 answers the review of rev0 (1bb9a0a7: R1 fully bound types, R2 total-reader claim split, R3 namespaces/binders and the nature of `dataOf_agrees`) and records the first implemented pure units (§5a). Changes against rev0 are marked **[rev1]**.

Design sources: `par/gen5-t2:scripts/gen5/` `DGEN_FREEZE.md` (rev2 c398021c; §2.1 `dataOf`/`GenData`/`dataOf_sound`, §2.4 R5,
§2.5 C1, unit rows DG-DATAOF / DG-COVER / DG-SEM), `T2COVER_FREEZE.md` rev2, `M5_INDEP_STUDIES.md` §B;
`kjob/g5rk-d0ddc50b:scripts/gen5/DG_READKINDS_FREEZE.md` rev2 (3f79600f). Line numbers were re-read on this branch
(base 9d26005c); `[B]` = this tree.

**Status [rev1]:** the pure units U-A, U-B, U-C (§5a) are written (`Tools/ShippingGen5DataOfPure.lean`, check
`Tests/Gen5/DataOfCheck.lean`, commit 462ea73d). They were elaborated by plain `lean` on the oleans of an earlier `kjob lake build`
(fast loop; this is NOT the evidence build). The `kjob lake build Tests.Gen5.DataOfCheck` result is recorded in the Issue note, not here.
`dataOfAt`, `dataOf`, `dataOfAt_sound`, U-D, U-E, U-F, U-G are design only, no Lean. Nothing here is a completion of the Issue.
New Lean goes in new files `Tools/ShippingGen5DataOf.lean` (design only; `dataOfAt` and the lemmas that mention it) and `Tools/ShippingGen5DataOfPure.lean` (exists, §5a) and a new check `Tests/Gen5/DataOfCheck.lean` (lakefile `lean_lib` additions only). No edit of the compiler,
`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`. No new TRUSTED boundary, law, FG/guarantee change.
`GenWF` is not strengthened. Everything that would need one of those is in §7, kept apart and not adopted.

Wording rule: "not supplied / this survey found no source or route" is a statement about this survey, not an
impossibility claim. A "mutant" in §6 is a rejection by signature / defeq of a changed statement, not a semantic
counterexample. Intermediate results are never written as completion.

---

## 1. What `dataOf` is, and what it is compared with

`readMachine` (`Tools/ShippingMachineCommand.lean:440-541` [B]) is the generation-time reader (MetaM). `dataOf` is its
**pure part as a total function**, producing `MachineData` (`Tools/ShippingMachineAuto.lean:172-190` [B]: `shape nIn dom
bposL vposL vwL ss ls outs nexts`) directly (readMachine's `Read` record, :390-413, keeps `nexts : List AnyTerm`;
`MachineData.nexts : Terms ss`, and `ss` is the list of the nexts' sorts).

Step-by-step correspondence (all line numbers [B] `ShippingMachineCommand.lean`):

| readMachine | dataOf | note |
|---|---|---|
| :443-445 `getEnv/getConstInfo`, universe check | not in `dataOf`; `E` is the entry the caller passes (`entry₀`, DGEN §2.5 C1) | the `entryConst … ci` call is in `entry₀`, not here |
| :451-452 the two gate refusals (`!allowGate`) | **not in `dataOf`** | route choice; the gate-miss fact is a run fact (DG-RUNREADS `gates`), not a `dataOf` input |
| :453 `machineShape? … = some shape` | `shape` is the **argument** `s` | `dataOf` never re-runs `machineShape?` (a `def` over `partial` helpers) |
| :455-459 `entry.value?` | `E.value?` | total |
| :462-463 `mixedGatePeel (packTupleInputs entryV)` | same expression, used as a **value** | `packTupleInputs` is `partial` (MachTupleIn.lean:79); its result is used, never unfolded |
| :466-467 `rootFloat entryBody` | same, as a value | `partial` (MachRawSurface.lean:198) |
| :468-475 `nDecl, nIn, nSlots, nLets`, binder count check | same, as `Bool` check → `none` | decidable |
| :476-501 `machRoot`, `srcDom`, `loopLet`, `resDom`, `depth` | same (structural `let rec`s are inlined as total local defs) | `machRoot` is a `def` (Elab.lean:4412) |
| :502-509 `srcDom'`, `machDom?` | same | `machDom?` is a `def` |
| :511-514 `tup?`, `machOuts?` / `machTupleKinds?` | same | |
| :515-522 `kinds, c, bposL, vposL, vwL` | same | |
| :523 **`unq c shape.body`** (`partial`) | **`readN (kindsCfg dom (isExpr dom) kinds) (lvl body) body`**, `lvl` a parameter (§2) | the only reader replaced |
| :524-531 `splitLets, splitFields, unField, typed` | same (they are total `def`s, :250/:257/:265) | |
| :532-537 `packed`, `q := quote …`, **`q.equal shape.body`** (opaque `Expr.equal`) | **`Term`-level structural check `bitsBeq ⟨W, whole⟩ ⟨_, packed⟩ = true`** (§5a) → `none` on mismatch | the opaque test is dropped; its job is done by the reader's soundness (`quote … whole = body`) + this check. **[rev1]** `bitsBeq` compares the width `W` against `(packLets …).1` as well as the term (it is `Sigma` equality). The check is mandatory, not a formality: `unField .bool ⟨w, .mux c a b⟩ = some ⟨.bool, c⟩` for ANY width `w` and ANY branches `a b` (not only `1#1`/`0#1`), `unField (.bits _) ⟨w,t⟩` ignores the declared width, and `(ks.zip fs).mapM` truncates to the shorter list; the re-pack through `toField`/`packLets`/`packAll` and the comparison with `whole` is what rejects all three |
| (no counterpart; the kernel checks `machine_ok` per declaration) | **`d.ok` guard → `none`** (§2.3) | the production reader does not run `MachineData.ok`; see §4 S-OK |

## 2. Full types (the freeze)

**[rev1] Namespaces and open-lists (R3).** Pure units: file `Tools/ShippingGen5DataOfPure.lean`, `namespace Tools.ShippingGen5DataOfPure`,
`open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMuxLoweringSoundness
Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab`. `Term`, `SType` are `Tools.ShippingUnifiedSource.*`; `Terms`, `tys`, `toField`,
`enc`, `encState` are `Tools.ShippingMachineDenote.*`; `MachineData`, `MachineData.ok/initOk`, `zipAllB` are
`Tools.ShippingMachineAuto.*`; `HList` is `Sparkle.Core.HList`; `SlotField` is `Sparkle.IR.Machine.SlotField`. `AnyTerm` and `BitsTerm`
(`Tools.ShippingMachineCommand`) are reducible `abbrev`s for `Σ s : SType, Term s` and `Σ w : Nat, Term (.bits w)`; the pure file does NOT
import `Tools.ShippingMachineCommand`, so its statements spell the Sigma types out (defeq, compared by the TYPE check on the spelled form).
`dataOfAt` file: `Tools/ShippingGen5DataOf.lean`, `namespace Tools.ShippingGen5DataOf`; `set_option autoImplicit false`. Imports only
existing modules (`Tools.ShippingMachineCommand` for `splitLets/splitFields/unField/outKind`, `Tools.ShippingReaderApp` for
`readN/readN_expr_sound`, `Tools.ShippingMachineAuto`, `Tools.ShippingMachineDenote`). `GenData`/`GenWF` are the DGEN §2.1
declarations and stay in the downstream file named there (`Tools/ShippingGen5Generated.lean`, DG-SEM), importing this one.

### 2.1 Pure helper definitions **[rev1: implemented, see §5a for the exact text]**

```lean
namespace Tools.ShippingGen5DataOfPure
def termsOfAny : (l : List (Σ s : SType, Term s)) → Terms (l.map (·.1))
def termBeq : {s s' : SType} → Term s → Term s' → Bool          -- across sorts
def anyBeq  (a b : Σ s : SType, Term s) : Bool                  -- sorts, then terms
def bitsBeq (a b : Σ w : Nat, Term (.bits w)) : Bool            -- widths, then terms
def decInit : (s : SType) → Nat → s.Type
def initsFrom (slots : List SlotField) : (ss : List SType) → HList (tys ss)
def initsOf (d : MachineData) : HList (tys d.ss)
```
`Term` has no `DecidableEq`; `deriving instance DecidableEq for Term` was tried and fails ("Dependent elimination failed … `m.add n`",
the `concat` index), so `termBeq` is hand written (21 constructors, index fields compared) with `termBeq_sound`/`termBeq_refl`.

### 2.2 `dataOfAt` and `dataOf`

```lean
/-- The pure part of `readMachine` as a TOTAL function. `lvl` is the level the applicative-lift reader `readN` is run at,
as a function of the expression it reads (DG-READKINDS supplies `exprSize`); soundness holds for EVERY `lvl`. -/
def dataOfAt (lvl : Lean.Expr → Nat) (E : ConstantInfo) (senv : StructEnv) (shape : MachineShape) :
    Option MachineData

/-- The frozen name of DGEN §2.1: `dataOfAt` at DG-READKINDS's level. Defined once DG-READKINDS exports `exprSize`. -/
def dataOf (E : ConstantInfo) (senv : StructEnv) (shape : MachineShape) : Option MachineData :=
  dataOfAt Tools.ShippingGen5ReadKinds.exprSize E senv shape
```
`dataOfAt` is the only definition that does not depend on READKINDS; `dataOf` is a one-line instance.
Decision recorded for review (Q1): `dataOfAt` keeps `lvl` abstract so that `dataOfAt_sound` (§3) and all of §5 are
independent of READKINDS; the final connection is the `dataOf` line, and the coverage statements (§4 S-COV) take
READKINDS U1-U4 as premises.

### 2.3 What `dataOfAt` returns `some` for

`dataOfAt lvl E senv shape = some d` iff every check of the table in §1 passes, **including** (a) `Term`-level
`repack = whole`, (b) `d.ok = true` (the guard), where `d` is the record assembled exactly as `readMachine`'s `return {…}`
(:535-537) with `ss := nexts.map (·.1)`, `nexts := termsOfAny nexts`.
The guard `d.ok` is the existing `MachineData.ok` (`ShippingMachineAuto.lean:216-243` [B]); nothing is added to it.
`initOk` is **not** a guard: it follows from `d.ok` by `initOk_of_ok` (§5a, **[rev1] proved**, so no second guard is added and coverage gains no extra check; the
stop-rule of the review ("report U-C failure, add no guard silently") did not trigger).

### 2.4 `dataOf_sound` **[rev1: fully bound]**

Open-list for this subsection: `open Tools.ShippingUnifiedSource Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge (inputExpr)
Tools.ShippingGen5DataOfPure Sparkle.Compiler.Elab`; `quote : Lean.Expr → (Nat → Lean.Expr) → (Nat → Lean.Expr) → Term s → Lean.Expr`
(Tools.ShippingUnifiedSource), `StructEnv`, `MachineShape` (Sparkle.Compiler.Elab), `ConstantInfo` (Lean).

```lean
theorem dataOfAt_sound (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData}
    (h : dataOfAt lvl E senv s = some d) :
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

theorem dataOf_sound {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData}
    (h : dataOf E senv s = some d) :
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true :=
  dataOfAt_sound Tools.ShippingGen5ReadKinds.exprSize h
```
(the third conjunct is the same text in both, `body_eq`; `dataOf_sound` is stated in full so a TYPE check can compare it with an independent
`Exp…` statement, not by unfolding `dataOfAt_sound`). Conjuncts are exactly `GenFacts.ok/body_eq/init` (`ShippingQuadComposed.lean:120-124`
[B]) and `CombFacts.ok/hbody/hinit` (`ShippingGen2CombPkg.lean:46-49`), `LoopFacts.ok/hbody/hinit` (`ShippingGen2Loop.lean:144-148`). `GenWF` is not touched.

Proof route (not tested), with the re-pack made explicit **[rev1]**:
1. the reader returns `r = ⟨.bits W, whole⟩` with `readN (kindsCfg dom (isExpr dom) kinds) (lvl body) body = some r`;
2. `readN_expr_sound` (`ShippingReaderApp.lean:356` [B]) at `dom := d.dom, ks := kinds`: `quote dom (fun j => inputExpr kinds.length ((posB 0 kinds).getD j 0)) (fun j => inputExpr kinds.length ((posV 0 kinds).getD j 0)) whole = body`;
3. U-D turns `posB 0 kinds`/`posV 0 kinds` into `d.bposL`/`d.vposL` (and `d.bpos j = d.bposL.getD j 0`, `inputExpr` count `kinds.length = d.shape.binders.length` by `kindsOf_length`);
4. the guard `bitsBeq ⟨W, whole⟩ ⟨_, d.packed⟩ = true` gives (`bitsBeq_eq`) `⟨W, whole⟩ = ⟨_, d.packed⟩` — widths AND terms — hence `whole` and `d.packed` agree after the width cast and `quote` of `d.packed` is `body`;
5. `ok` by the guard; `initOk` by `initOk_of_ok`.
No step uses `Expr.equal`/`Expr.eqv` soundness. Whether a sound `Expr.equal` could have replaced step 4 was not investigated here; this document does not say a new law is or is not required for that (§7 B1 is only the law that coverage would need to reuse production's own `q.equal`).

### 2.4a Totality: what is and is not claimed **[rev1, R2]**

Two different statements were conflated in rev0. They are separated:

* **(T-K) dependence on kernel-formable values.** `dataOfAt` is an ordinary `def` (no `partial`, structural/`List` recursion only) whose body mentions
  `packTupleInputs`, `rootFloat`, `machDom?`-style helpers and `Expr` functions. The `partial` ones (`packTupleInputs` MachTupleIn.lean:79, `rootFloat`
  MachRawSurface.lean:198; `machineShape?` if it were called) enter the kernel as **opaque constants**; `dataOfAt` is therefore a function of
  the arguments *and of those opaque values*, and `dataOfAt_sound` holds for every value those constants might denote (the proof never unfolds them).
  This is the only totality that is stated and the one the kernel statement type-checks.
* **(T-X) every execution terminates.** NOT proved and not stated: that the compiled code of `packTupleInputs`/`rootFloat`/… returns on every input the
  production reader can feed them. The kernel cannot evaluate them (`decide`/`rfl` stops at the opaque constant), and no termination argument for them is in this
  tree as far as this survey found. The closure audit (§6.3) counts opaque / body-less constants it meets and reports that their bodies (the `partial`
  internals) are **not explored**; zero reached `partial` constants is not claimed for `dataOfAt`.

Consequence for wording elsewhere: where DGEN says "total `dataOf`", read (T-K) only. "`dataOf = some _` on every successful run" is coverage (S-COV), also not claimed.

Design option **[rev1, Q5, not implemented]** that makes (T-K) explicit and gives kernel-checkable instances: split
`dataOfAt := dataOfFrom lvl E shape (packTupleInputs entryV) (rootFloat entryBody)` where `dataOfFrom` takes the *values* of the partial helper
results as ordinary arguments (`Option`/`Expr` typed) and contains no call to a `partial` function; then `dataOfFrom_sound` is stated for all
argument values and `dataOfAt_sound` is its instance. Kernel equalities of the kind `dataOfFrom lvl E shape lit₁ lit₂ = some X.machineData` for fixed
literal helper results (§2.5 K-instances) become possible when `readN` etc. reduce in the kernel; no such instance is claimed.

### 2.5 Agreement (validation) **[rev1, R3: two different things]**

`dataOf_agrees` is not a theorem about `readMachine` (it contains `partial` readers, §7 B2). Two forms, never mixed:

* **(E) evaluation record.** A check command `#gen5_dataof_agrees X` (MetaM) evaluates `dataOf` by compiled execution on the declaration `X` and
  compares the result with `readMachine`'s data field by field (`shape nIn dom bposL vposL vwL ls outs nexts`), via the generated constants
  (`X.machineData`, `dataE`, `ShippingMachineCommand.lean:591-601`). It yields a **log line, not a kernel fact**; it is evidence in the sense of T2COVER `READ_DIFF`
  and says nothing about inputs not run.
* **(K) kernel equality.** `dataOfFrom … = some X.machineData` by `rfl`/`decide` for fixed literal helper results (only after the Q5 split). Not
  expected in general: a result that goes through a `partial` function is not reduced by the kernel, so no `rfl` for `dataOfAt` on a real declaration is
  expected or claimed.

## 3. What READKINDS must give (by type) — and what it need not

U1-U4 types are those of the READKINDS freeze rev2 (3f79600f); they are cited, not restated.

| READKINDS item | used by `dataOfAt`/`dataOf_sound`? | used by | statement used |
|---|---|---|---|
| `readN` soundness (`readN_sound`, `readN_expr_sound`, **already in `ShippingReaderApp.lean`**) | **yes** (proof of `body_eq`) | `dataOfAt_sound` | existing |
| `exprSize`, `readTot` (def, READKINDS §2.0) | `dataOf` only (the one-line instance) | `dataOf` | defs only |
| U1 `readN_quote`, U1e `readN_expr_quote` | no | coverage S-COV | types as READKINDS §2.1 |
| U2 `readTot_quote`, `liftDepth_le_exprSize` | no | S-COV | READKINDS §2.2 |
| U3 `machine_body_of_readN`, `machine_wf_of_readN` | no (we use `readN_expr_sound` directly, so we need `hb hv`, not `hread`) | alternative route, not adopted | READKINDS §2.3 |
| U4 `readTot_of_quote_body` (premise `hq`) | no | S-COV | READKINDS §2.4 |
| U5 `RootFacts` (not supplied) | **no**: `dataOf` calls `rootFloat`/`packTupleInputs` as values | S-COV (needs a producer if coverage wants to talk about them) | READKINDS §2.5 |

Interface type (what `dataOf` hands back to coverage, so the join with READKINDS is one statement). With
`ReadsOk` the evidence "the reader is the total one at `exprSize`":

```lean
/-- Premise of coverage (DG-COVER), stated here so READKINDS's U4 plugs in as one argument. NOT a hypothesis of `dataOf_sound`. -/
def BodyQuoted (d : MachineData) : Prop :=
  d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
```
Direction of the join: `dataOf_sound` gives `BodyQuoted d` for the returned `d` (soundness). READKINDS U4 gives
`readTot … = some ⟨_, packed⟩` from `BodyQuoted d` plus the shape facts (completeness side). `dataOf = some _` for a
run needs the second direction **and** the other rows of §1; the conjunction is S-COV, not delivered by this Issue.

## 4. Supplier table

S = supplied by an existing lemma; P = pure lemma planned in §5 (needs no dependency); R = would be derived from a real
run (DG-RUNREADS / DG-ENV / DG-COVER); U = not supplied by this survey (stated, not claimed impossible).

| id | obligation | status | where / source |
|---|---|---|---|
| S-SHAPE | `d.shape = s` | S (by construction) | `dataOfAt` body |
| S-BODY | `body_eq` | S given `bitsBeq_eq` (§5a, implemented), U-D | `readN_expr_sound` (ShippingReaderApp.lean:356 [B]), `posB/posV/widV` (ShippingReaderInputs.lean) |
| S-INIT | `d.initOk (initsOf d)` | **[rev1] S: `initOk_of_ok` (§5a, written; kernel-checked by the evidence build only after it is recorded in the Issue note)** | `ShippingMachineAuto.lean:216-243`, `encState` (MachineDenote.lean:45) |
| S-OKGUARD | `d.ok = true` in the conclusion | S (guard) | by construction |
| S-OK | `d.ok = true` **for every successful machine-route run** | **U** | production does not run `ok` (the kernel does, per declaration: `machine_ok` by `Eq.refl`, DGEN §1). Pieces found: `outs_of_reader`/`outNames_of_reader` (ShippingReaderOutsInv.lean, ReaderOutNames.lean — their build status not checked by this survey), `ShapeDecomp.r5_of_lengths` (ShippingShapeDecomp.lean:143), `ShippingReaderLenOk.lean`; the term-level rows (`WF`, `LetsScoped`, `LetsTyped`, `slotsFitB`, `outsFitB`) have no run-level source found. This is DG-COVER / DG-WFCOVER work and is a **stop-condition item (DGEN D3)** if a successful source fails `ok`. |
| S-COV-Q | body is a quotation of a `Term` for every successful run | **U** (READKINDS §3, B1-B4) | not delivered here |
| S-COV-FLOAT | `rootFloat`/`packTupleInputs` values are consistent with what `machineShape?` used | **U** | READKINDS §2.5 `RootFacts`; this survey found no producer |
| S-COV-GATE | the two gate refusals (:451-452) | R (DG-RUNREADS `gates`) | not a `dataOf` obligation |
| S-ENV | `E` is `entry₀ env₀ X` for the run's env | R/U (DG-ENV) | DGEN §2.5 C0; not here |
| S-GENWF | `GenWF d = true` | U | DG-WFCOVER; rows unchanged |

No row above is a new premise of FG/T1/`dataOf_sound`. The unsupplied ones (S-OK, S-COV-Q, S-COV-FLOAT, S-ENV, S-GENWF) stay
named and belong to DG-COVER / DG-WFCOVER / DG-ENV; this Issue does not count them as supplied.

## 5. Units that need no dependency (pure lemma units) **[rev1: fully bound]**

All in `Tools/ShippingGen5DataOfPure.lean` (§5a: written) or `Tools/ShippingGen5DataOfPure2.lean` (U-D…U-G, design only). Each is a separate
lemma with a full type; none uses READKINDS, `Laws`, `T1Hyp*`. Open-lists as in §2.

### 5a. Written (commit 462ea73d), exact statements

```lean
namespace Tools.ShippingGen5DataOfPure
-- U-A
theorem termsOfAny_fields : ∀ (l : List (Σ s : SType, Term s)),
    (termsOfAny l).fields = l.map (fun t => toField t.1 t.2)
-- U-B
theorem termBeq_sound : ∀ {s : SType} (a : Term s) {s' : SType} (b : Term s'), termBeq a b = true → s = s' ∧ HEq a b
theorem termBeq_refl  : ∀ {s : SType} (a : Term s), termBeq a a = true
theorem anyBeq_eq   {a b : Σ s : SType, Term s} (h : anyBeq a b = true) : a = b
theorem anyBeq_refl (a : Σ s : SType, Term s) : anyBeq a a = true
theorem bitsBeq_eq  {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true) : a = b      -- Sigma equality: the width is part of it
theorem bitsBeq_refl (a : Σ w : Nat, Term (.bits w)) : bitsBeq a a = true
theorem bitsBeq_width {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true) : a.1 = b.1
-- U-C
theorem initOk_of_ok (d : MachineData) (h : d.ok = true) : d.initOk (initsOf d) = true
```
Notes. `termBeq` is across sorts (`Term s` against `Term s'`), so `anyBeq a b` first requires `a.1 = b.1` and `bitsBeq` requires `a.1 == b.1` (the
width is compared by the function itself, not only recovered from `termBeq_sound`). `termsOfAny` is on `Σ s : SType, Term s` (the `AnyTerm`
abbrev, spelled out). `initsOf d = initsFrom d.shape.layout.slots d.ss`, `decInit .bool n = decide (n ≠ 0)`, `decInit (.bits w) n = BitVec.ofNat w n`;
`initOk_of_ok` uses of `ok` the rows: `nIn + ss.length ≤ binders.length`, the `zipAllB` slot row (`f.width = machWidth b.2`, `f.init < 2^f.width`), and
`K (nIn + i) = ss[i]?`; it needs no other row. **U-C holds** (no guard added).

### 5b. Designed, not written

* **U-D position lists.** For `ks : List MixedGateBinder` (`posB posV widV`: `Tools.ShippingReaderInputs`):
  ```lean
  theorem bposL_eq (ks : List MixedGateBinder) :
      (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) => if pk.2 == .bool then some pk.1 else none) = posB 0 ks
  theorem vposL_eq (ks : List MixedGateBinder) :
      (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) => match pk.2 with | .bits _ => some pk.1 | _ => none) = posV 0 ks
  theorem vwL_eq (ks : List MixedGateBinder) :
      (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) => match pk.2 with | .bits w => some w | _ => none) = widV ks
  ```
  (proved through an offset generalization `List.range' o n`). These are `readMachine` :519-521 verbatim.
* **U-E inversions** (`splitLets splitFields unField`: `Tools.ShippingMachineCommand`; `packLets`: `Tools.ShippingMachineEntry`; `packList packAll`: `Tools.ShippingMachineDenote`/`Auto`):
  ```lean
  theorem splitLets_some {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))} {core : Σ w : Nat, Term (.bits w)}
      (h : splitLets n t = some (fs, core)) : fs.length = n ∧ t = packLets fs core.2
  theorem splitFields_some {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
      (h : splitFields n t = some fs) : 0 < n ∧ fs.length = n ∧ t = packAll fs
  theorem unField_bool {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField .bool f = some t) :
      ∃ (w : Nat) (c : Term .bool) (a b : Term (.bits w)), f = ⟨w, .mux c a b⟩ ∧ t = ⟨.bool, c⟩
  theorem unField_bits {n w : Nat} {u : Term (.bits w)} {t : Σ s : SType, Term s} (h : unField (.bits n) ⟨w, u⟩ = some t) : t = ⟨.bits w, u⟩
  theorem unField_domain {f : Σ w : Nat, Term (.bits w)} : unField .domain f = none
  theorem toField_unField {k : MixedGateBinder} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
      (h : unField k f = some t) (hre : toField t.1 t.2 = f) : sortOf k = some t.1
  ```
  `unField_bool` is deliberately weak (branches and width are NOT `1#1`/`0#1`/`1`): this is why the `repack = whole` check can not be dropped (§1 table);
  `toField_unField` is the pure statement that a field that survives the re-pack (`hre`) has the binder's sort. The first two `_some` lemmas are exact for the
  right-nested `concat` shapes of `packLets`/`packAll` (the width index `m + n` is part of the Sigma, so they are statements about Sigma values, not about `Expr`).
* **U-F shape preservation** (needs `dataOfAt`): `dataOfAt lvl E senv s = some d → d.shape = s` and
  `dataOfAt lvl E senv s = some d → d.shape.binders.length = d.nIn + d.ss.length + d.letBs.length`.
* **U-G** closed instances of §2.5 (K), after the Q5 split, evidence only.

Order after approval: U-D, U-E (step 1b); `dataOfAt` (or `dataOfFrom`) and its `_shape/_ok` (step 2); `dataOfAt_sound` (step 3); `dataOf` (step 4,
needs READKINDS's `exprSize`; until it lands only `dataOfAt` is delivered). Estimate for the rest 400-700 lines (an estimate, not a result).

## 6. Expected-type / closure / axiom audit plan

**[rev1]** `Tests/Gen5/DataOfCheck.lean` (written, commit 462ea73d) in the form of `Tests/Gen5/RunReadsCheck.lean` (imports `Tests.Gen3.ExpectedType`
and `Tools.ShippingGen5T1ND` for the `T1Hyp`/`T1HypND` fixtures). It currently covers §5a only: TYPE for the 9 lemmas and the 4 definitions' types, 7 MUTANT
rejections (signature / defeq of a changed statement, not semantic counterexamples), 8 concrete `decide` controls, REACH with 4 detector controls, AXIOMS.
The items below are the plan for the full file; those marked (§5a only) exist.

1. **TYPE.** `dataOf_sound`, `dataOfAt_sound`, `initOk_of_ok`, `anyBeq_eq`/`bitsBeq_eq`, `termsOfAny` facts against independently written
   `Exp…` statements, compared by `isDefEq` on the fully bound, universe-instantiated types.
2. **MUTANT** (signature / defeq rejections, **not** semantic counterexamples): `dataOf_sound` without the `ok` conjunct;
   without the `init` conjunct (DGEN rev2 R7 requires it); with `d.shape = s` replaced by `d.shape.body = s.body`;
   with `body_eq` stated at `d.vwL` instead of `d.vw`; `dataOfAt_sound` for a `lvl` restricted to `exprSize` (loses genericity);
   `initOk_of_ok` without `h`; `anyBeq_eq`/`bitsBeq_eq` as an iff (claims completeness); `dataOf` taking an extra `GenWF d = true` hypothesis
   (strengthening).
3. **REACH** (reachable closure over explicit bodies, `Rule`-based as in `T1NDCheck.lean` §5): **[rev1]** it also counts opaque and body-less constants it meets and prints the names of the opaque ones; `partial` definitions are opaque constants whose real body is NOT explored, so a clean REACH line is a statement about the explored part only (R2). Must NOT reach `T1Hyp`/`T1HypND` fields,
   anything in `Laws`, `Lean.Expr.equal`/`Lean.Expr.eqv` as a use, `Lean.ofReduceBool`. Controls: a fixture reaching `T1Hyp.dec`, one reaching
   `T1HypND.casesOn`, one using `Expr.equal`, one unrelated theorem.
4. **AXIOMS.** `collectAxioms` on every new theorem: only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, no native_decide.
5. **Concrete instances** (positive controls, not a substitute): `dataOfAt` on 1-2 fixed shapes where the partial helper results are
   literal; one negative control (`ok` fails ⇒ `none`).
6. Build discipline: one `kjob lake build` target at a time; logs outside the tree; the success SHA is written into the NOT BUILT
   header by a comment-only commit.

## 7. Where a new TRUSTED / law / compiler change would be needed (not adopted, not requested)

| id | what | why it comes up | status |
|---|---|---|---|
| B1 | `Expr.equal a b = true → a = b` | would give S-COV-Q from production's `q.equal` | new law; **not proposed** (READKINDS B1) |
| B2 | agreement of `dataOf` (or of total fuel versions) with the `partial` `rootFloat`/`packTupleInputs`/`unq` | S-COV-FLOAT, general `dataOf_agrees` | not supplied: this survey found no route under the present boundary; not claimed impossible; classification undecided here (D2 not re-opened) |
| B3 | coverage theorem takes `BodyQuoted`/`ok` as a premise | S-COV-Q, S-OK | conditional result, recorded as intermediate |
| B4 | compiler change: `readMachine` returns the certificate / runs `ok` | S-OK, S-COV-Q | compiler edit; forbidden for this Issue |

Nothing in §2-§5 needs B1-B4. Choosing one for DG-COVER is a user decision (new law / compiler change), prepared as a
separate decision document only if the reviewer agrees DG-DATAOF's acceptance depends on it.

## 8. Review questions

**[rev1] Reviewer's answer to rev0 (Issue history, 1bb9a0a7):** Q1 abstract `lvl` acceptable; Q2 `ok` as a guard acceptable provided DG-COVER stays unsupplied (it does);
Q3 width-carrying `Term` structural comparison acceptable (this is `bitsBeq`); Q4 soundness and coverage separated within this Issue acceptable.
New for review: **Q5** the `dataOfFrom` split of §2.4a (partial-helper results as explicit arguments) versus `dataOfAt` calling them in its body.

Original questions (rev0):

* **Q1.** `dataOfAt lvl` with abstract level plus `dataOf := dataOfAt exprSize` (this document), or `dataOf` fixed on READKINDS's
  `exprSize` from the start (then the Issue cannot start before READKINDS exports it)?
* **Q2.** `d.ok` as a guard of `dataOf` (this document: `dataOf_sound`'s `ok` conjunct is by construction; coverage carries S-OK), versus
  leaving `ok` out of `dataOf` and proving it from reader invariants (S-OK would become a soundness obligation; this survey found no
  run-level source for its term rows). Default: guard.
* **Q3.** `termBeq`/`bitsBeq` (new, §5a) for the `repack = whole` check, versus comparing at `Expr` level (needs a total
  structural `Expr` equality with soundness; not found in the tree).
* **Q4 (acceptance).** With S-OK / S-COV-Q / S-COV-FLOAT unsupplied, is the acceptance of this Issue
  "`dataOf`, `dataOf_sound`, §5 units, checks; coverage rows recorded as DG-COVER's open items", as READKINDS Q4 proposes for its side?

## 9. Not claimed

* Only §5a and the check file exist as Lean; everything else here is design, line counts are estimates. No claim that every `dataOfAt` execution terminates (§2.4a T-X).
* No claim that `dataOfAt` returns `some` on any successful run (coverage, DG-COVER); no claim that it does not.
* `initOk_of_ok` is written and passed plain `lean` elaboration on the oleans of an earlier build; its `kjob lake build` result is in the Issue note, not claimed here. No claim that `ok` is implied by anything in the run.
* No claim about `rootFloat` / `packTupleInputs` beyond using their values; no claim about `Expr.equal`.
* No claim that DG-READKINDS U1-U4 are proved; this document uses only the already-existing `readN_expr_sound`.
* The `dataOf` line (§2.2) is conditional on READKINDS exporting `exprSize`; until then only `dataOfAt` exists.
