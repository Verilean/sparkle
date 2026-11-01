# DG-DATAOF full-type freeze, rev2 (Issue sparkle-gen5-dg-dataof)

**rev2** answers the review of rev1 (bc9a300d): **R1** (the U-E statement `toField_unField` is false for `.bits n` binders; withdrawn, replaced; the declared width comes from `MachineData.ok` rows, not from the re-pack), **R2** (the comparison and the quotation witness are different run obligations; the auxiliary generator `readMachine` and the compiler's actual reader are different things), **Q5** (the complete type of `dataOfFrom`). Changes against rev1 are marked **[rev2]**.

rev1 answered the review of rev0 (1bb9a0a7: R1 fully bound types, R2 total-reader claim split, R3 namespaces/binders and the nature of `dataOf_agrees`) and records the first implemented pure units (§5a). Changes against rev0 are marked **[rev1]**.

Design sources: `par/gen5-t2:scripts/gen5/` `DGEN_FREEZE.md` (rev2 c398021c; §2.1 `dataOf`/`GenData`/`dataOf_sound`, §2.4 R5,
§2.5 C1, unit rows DG-DATAOF / DG-COVER / DG-SEM), `T2COVER_FREEZE.md` rev2, `M5_INDEP_STUDIES.md` §B;
`kjob/g5rk-d0ddc50b:scripts/gen5/DG_READKINDS_FREEZE.md` rev2 (3f79600f). Line numbers were re-read on this branch
(base 9d26005c); `[B]` = this tree.

**Status [rev2]:** besides U-A/U-B/U-C (below), the pure units **U-D and the corrected U-E** are written: `Tools/ShippingGen5DataOfPure2.lean`, check `Tests/Gen5/DataOfCheck2.lean` (§5b). They passed the clean issue-linked build do3v-62ea2479 (exit 0, 758 jobs) and were scoped-approved at 62ea2479. **[agent g5do-r4]** `Tools/ShippingGen5DataOf.lean` now holds `dataOfFrom`, `dataOfAt` (and the helpers `dataOfFront`, `dataOfCore`, `dataOfTail`, `checked`) with the CONDITIONAL theorems `dataOfFrom_sound` and `dataOfAt_sound` at exactly the §2.4a Q5 types, checked by `Tests/Gen5/DataOfCheck3.lean` (TYPE against independent statements, 6 well-typed one-point mutants rejected by the same comparison (signature/defeq rejection, not a semantic counterexample), explicit value closure with the detector controls, standard axioms only). Built only in the author's Pod (dev loop, `Tests.Gen5.DataOfCheck3` 761 jobs exit 0); NOT yet an issue-linked clean build (the coder's). Soundness comes from `readN_expr_sound`, the structural `bitsBeq` guard and the `d.ok` guard, not from the re-pack. Still not supplied: `dataOf` (no `exprSize` in this tree), that `dataOfAt` is `some` on any run, `tin`/`fl` versus the compiler's values (S-COV-FLOAT), agreement with `readMachine` or the compiler's reader, C-CMP / C-QWIT, quotation existence, T-X. Not an Issue/M5/FG completion.

**Status [rev1] (kept):** the pure units U-A, U-B, U-C (§5a) are written (`Tools/ShippingGen5DataOfPure.lean`, check
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
| :532-537 `packed`, `q := quote …`, **`q.equal shape.body`** (opaque `Expr.equal`) | **`Term`-level structural check `bitsBeq ⟨W, whole⟩ ⟨_, packed⟩ = true`** (§5a) → `none` on mismatch | the opaque test is dropped; its job is done by the reader's soundness (`quote … whole = body`) + this check. **[rev1]** `bitsBeq` compares the width `W` against `(packLets …).1` as well as the term (it is `Sigma` equality). **[rev2, R1 correction]** What the re-pack comparison rejects and what it does not: `unField .bool ⟨w, .mux c a b⟩ = some ⟨.bool, c⟩` for ANY width `w` and ANY branches `a b` (not only `1#1`/`0#1`) — the re-pack `toField .bool c = ⟨1, mux c 1#1 0#1⟩` differs from such a field, so the comparison with `whole` rejects it (the packed-bool-field case). `(ks.zip fs).mapM` truncates to the shorter list — the lengths are fixed by `splitLets nLets` / `splitFields (nOuts + nSlots)` and the `ok` row `shape.layout.lets = letBs.length` etc., not by the re-pack. **`unField (.bits n) ⟨w,t⟩ = some ⟨.bits w, t⟩` ignores `n` and ALWAYS survives the re-pack (`unField_bits_toField`, §5b): the re-pack comparison does NOT check the declared width of a `.bits n` binder.** The rev1 text "the re-pack … rejects all three" is withdrawn for this item; the declared width comes from `ok` rows (§4 S-WIDTH) |
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
3. U-D (**[rev2] written**: `bposL_eq`/`vposL_eq`/`vwL_eq`, §5b) turns `posB 0 kinds`/`posV 0 kinds` into `d.bposL`/`d.vposL` (and `d.bpos j = d.bposL.getD j 0`, `inputExpr` count `kinds.length = d.shape.binders.length` by `kindsOf_length`);
4. the guard `bitsBeq ⟨W, whole⟩ ⟨_, d.packed⟩ = true` gives (`bitsBeq_eq`) `⟨W, whole⟩ = ⟨_, d.packed⟩` — widths AND terms — hence `whole` and `d.packed` agree after the width cast and `quote` of `d.packed` is `body`;
5. `ok` by the guard; `initOk` by `initOk_of_ok`.
No step uses `Expr.equal`/`Expr.eqv` soundness. **[rev2, R2]** This is a statement about SOUNDNESS of the returned `d` only: `dataOfAt` runs `readN` itself, so the quotation property of the output comes from `readN_expr_sound` and the structural comparison, and `Expr.equal` is not needed. It does NOT say that a successful run's body is a quotation (that is the coverage rows C-CMP / C-QWIT of §4). Whether a sound `Expr.equal` could have replaced step 4 was not investigated here; this document does not say a new law is or is not required for that (§7 B1 is only the law that coverage would need to reuse production's own `q.equal`).

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

**[rev2] Q5 `dataOfFrom` split — complete types (reviewer agreed with the separation; design only, no Lean).** Namespace `Tools.ShippingGen5DataOf`, file `Tools/ShippingGen5DataOf.lean`, opens as in §2.4.

```lean
/-- `dataOfAt` with the results of the two `partial` helpers given as ordinary ARGUMENTS:
`tin` is the value `Sparkle.Compiler.MachTupleIn.packTupleInputs entryV` and `fl` is the function value
`Sparkle.Compiler.MachRawSurface.rootFloat`. Neither is unfolded, no `partial` function is called inside. -/
def dataOfFrom (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : Sparkle.Compiler.Elab.StructEnv)
    (shape : Sparkle.Compiler.Elab.MachineShape) (tin : Lean.Expr) (fl : Lean.Expr → Lean.Expr) :
    Option Tools.ShippingMachineAuto.MachineData

/-- The frozen shape of §2.2: the two helper applications are the only place the `partial` constants occur. -/
def dataOfAt (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : Sparkle.Compiler.Elab.StructEnv)
    (shape : Sparkle.Compiler.Elab.MachineShape) : Option Tools.ShippingMachineAuto.MachineData :=
  match E.value? with
  | none => none
  | some entryV =>
    dataOfFrom lvl E senv shape (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV)
      Sparkle.Compiler.MachRawSurface.rootFloat

theorem dataOfFrom_sound (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true
-- `dataOfAt_sound` (§2.4) is `dataOfFrom_sound` at `tin := packTupleInputs entryV`, `fl := rootFloat`; `dataOf_sound` is `dataOfAt_sound` at `exprSize`.
```
`dataOfFrom_sound` holds for EVERY `tin`, `fl` (the proof never looks at them), which is the precise form of (T-K). The **connection to the actual values** of `packTupleInputs entryV` / `rootFloat entryBody` — that they are what the compiler's shape layer used, and that the resulting `dataOfAt` is `some` — is **not** part of `dataOfFrom_sound`. It is kept as a coverage obligation, **DG-COVER (agent g5cv-r2)**, row S-COV-FLOAT of §4; this Issue does not discharge it. Kernel instances `dataOfFrom lvl E senv shape lit₁ lit₂ = some X.machineData` (§2.5 K) remain evidence-only, not claimed.

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
| S-BODY | `body_eq` for the RETURNED `d` (soundness) | S given `bitsBeq_eq` (§5a, implemented), U-D (**[rev2] written**, §5b) | `readN_expr_sound` (ShippingReaderApp.lean:356 [B]), `posB/posV/widV` (ShippingReaderInputs.lean) |
| S-INIT | `d.initOk (initsOf d)` | **[rev1] S: `initOk_of_ok` (§5a, written; kernel-checked by the evidence build only after it is recorded in the Issue note)** | `ShippingMachineAuto.lean:216-243`, `encState` (MachineDenote.lean:45) |
| S-OKGUARD | `d.ok = true` in the conclusion | S (guard) | by construction |
| S-OK | `d.ok = true` **for every successful machine-route run** | **U** | production does not run `ok` (the kernel does, per declaration: `machine_ok` by `Eq.refl`, DGEN §1). Pieces found: `outs_of_reader`/`outNames_of_reader` (ShippingReaderOutsInv.lean, ReaderOutNames.lean — their build status not checked by this survey), `ShapeDecomp.r5_of_lengths` (ShippingShapeDecomp.lean:143), `ShippingReaderLenOk.lean`; the term-level rows (`WF`, `LetsScoped`, `LetsTyped`, `slotsFitB`, `outsFitB`) have no run-level source found. This is DG-COVER / DG-WFCOVER work and is a **stop-condition item (DGEN D3)** if a successful source fails `ok`. |
| S-WIDTH **[rev2, R1]** | the declared width / sort of every `unField`-read field equals its binder's: lets (`.bits n` binder), nexts (`.bits n` slot binder), outs (`outKind o`) | **S inside `dataOfAt` (guard `d.ok`), U for a production run** | rows of `MachineData.ok` (`ShippingMachineAuto.lean:217-245`): **lets** conjunct `LetsTyped … d.K (nIn + ss.length) d.ls` (:242; `LetsTyped` row `K p = some l.1`, `ShippingMachineDenote.lean:366`, `K p = sortOf` of binder p, Auto:204) = `ok_letsTyped`; **nexts** conjunct `d.K (nIn + i) = d.ss[i]?` (:241; `ss` is the list of the nexts' own sorts) = `ok_K_nexts`, and also the `zipAllB` slot row `f.width = machWidth b.2` (:223-225) with `slotsFitB` `f.width = g.1` (:235, :113-120); **outs** conjunct `outsFitB` (:244; row `o.width = (toField t.1 t.2).1`, Auto:141) = `ok_outsFit`. Pure lemmas turning these into `sortOf (binder) = some t.1`: `unField_bits_sortOf_iff`, `unField_sortOf`, `unField_outKind_sort` (§5b). **Not from the re-pack** (`unField_bits_toField`: a `.bits n` field always survives it). In `readMachine` none of these rows is run (:520-527 `typed` only calls `unField`; the check at :533 is the opaque `q.equal`), so for a production run the width of a `.bits n` let/next field being `n` is part of S-OK (**U**), not of S-WIDTH-in-`dataOfAt` |
| C-CMP **[rev2, R2]** | the production comparison `q.equal shape.body = true` (`ShippingMachineCommand.lean:533`) held | **U** | a fact about an execution of the auxiliary generator `Tools.ShippingMachineCommand.readMachine` (a `MetaM` command; READKINDS freeze §1.1 / its provenance note: callers found by grep are generator / test / sweep commands, none in the compiler core or in `RunReadsAt`). This survey found no run supplier for it. Even where it held, `Lean.Expr.equal` is opaque: turning `true` into `q = body` is §7 B1 (new law, not proposed). It is **not** `dataOfAt`'s check (that is the structural `bitsBeq`, §1) |
| C-QWIT **[rev2, R2]** | for every successful machine-route run, `∃ t, shape.body = quote … t` with the `WF` facts (the premise `hq` of READKINDS U4 `readTot_of_quote_body`) | **U** | separate from C-CMP. What would be needed is the compiler's ACTUAL reader (the one the machine route runs, whose identity/location this Issue did not establish) producing a body that is a quotation; READKINDS `readN_quote` (U1; implemented on `kjob/g5rk-impl`, audited by agent g5rk-aud — status not claimed here) is the completeness side that consumes C-QWIT, it does not produce it. The auxiliary `readMachine` (`unq` + `q.equal`) is NOT the compiler's reader and its outcome is not evidence about the compiler's reader unless a link is stated (none found). §7 B1 alone does NOT supply C-QWIT: it would turn C-CMP into an equation but only on runs of `readMachine`, and says nothing about the compiler's reader |
| S-COV-Q | (umbrella of C-CMP + C-QWIT, rev1 wording) | **U** (READKINDS §3, B1-B4) | not delivered here; read it as the two rows above |
| S-COV-FLOAT | `rootFloat`/`packTupleInputs` values are consistent with what `machineShape?` used, and `dataOfFrom … (packTupleInputs entryV) rootFloat` is `some` | **U** | READKINDS §2.5 `RootFacts`; this survey found no producer. **[rev2]** this is the connection of the values of the partial functions to `dataOfFrom` (§2.4a Q5); held as a DG-COVER obligation (agent g5cv-r2) |
| S-COV-GATE | the two gate refusals (:451-452) | R (DG-RUNREADS `gates`) | not a `dataOf` obligation |
| S-ENV | `E` is `entry₀ env₀ X` for the run's env | R/U (DG-ENV) | DGEN §2.5 C0; not here |
| S-GENWF | `GenWF d = true` | U | DG-WFCOVER; rows unchanged |

No row above is a new premise of FG/T1/`dataOf_sound`. The unsupplied ones (S-OK, S-COV-Q, S-COV-FLOAT, S-ENV, S-GENWF) stay
named and belong to DG-COVER / DG-WFCOVER / DG-ENV; this Issue does not count them as supplied.

## 5. Units that need no dependency (pure lemma units) **[rev1: fully bound]**

All in `Tools/ShippingGen5DataOfPure.lean` (§5a: written) or `Tools/ShippingGen5DataOfPure2.lean` (U-D, U-E: **[rev2] written**, §5b; U-F, U-G: design only). Each is a separate
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

### 5b. U-D and U-E **[rev2: written]** (`Tools/ShippingGen5DataOfPure2.lean`, namespace `Tools.ShippingGen5DataOfPure2`)

`import Tools.ShippingMachineCommand Tools.ShippingReaderInputs`; `open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand Tools.ShippingMachineEntry Tools.ShippingReaderInputs Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab`. Exact statements:

```lean
-- U-D  (readMachine :512-514 verbatim; MixedGateBinder: Sparkle.Compiler.Elab; posB/posV/widV: Tools.ShippingReaderInputs)
theorem bposL_eq (ks : List MixedGateBinder) :
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) => if pk.2 == .bool then some pk.1 else none) = posB 0 ks
theorem vposL_eq (ks : List MixedGateBinder) :
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) => match pk.2 with | .bits _ => some pk.1 | _ => none) = posV 0 ks
theorem vwL_eq (ks : List MixedGateBinder) :
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) => match pk.2 with | .bits w => some w | _ => none) = widV ks
-- (proved through the offset forms bposL_aux/vposL_aux/vwL_aux with List.range' o ks.length, for all o)

-- U-E  splitLets/splitFields/unField: Tools.ShippingMachineCommand; packLets: Tools.ShippingMachineEntry; packAll: Tools.ShippingMachineAuto
theorem splitLets_some {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))} {core : Σ w : Nat, Term (.bits w)} :
    splitLets n t = some (fs, core) → fs.length = n ∧ t = packLets fs core.2
theorem splitFields_some {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
    (h : splitFields n t = some fs) : 0 < n ∧ fs.length = n ∧ t = packAll fs
theorem unField_bool {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField .bool f = some t) :
    ∃ (w : Nat) (c : Term .bool) (a b : Term (.bits w)), f = ⟨w, .mux c a b⟩ ∧ t = ⟨.bool, c⟩
theorem unField_bits {n w : Nat} {u : Term (.bits w)} {t : Σ s : SType, Term s} (h : unField (.bits n) ⟨w, u⟩ = some t) : t = ⟨.bits w, u⟩
theorem unField_domain {f : Σ w : Nat, Term (.bits w)} : unField .domain f = none
-- what the re-pack does NOT give, and the corrected statements (replace the withdrawn `toField_unField`):
theorem unField_bits_toField {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) : toField t.1 t.2 = f                                    -- ALWAYS: no information about n
theorem unField_bits_sortOf_iff {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) : sortOf (.bits n) = some t.1 ↔ f.1 = n
theorem unField_sortOf {k : MixedGateBinder} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField k f = some t) (hw : ∀ n, k = .bits n → f.1 = n) : sortOf k = some t.1
theorem unField_width_of_sortOf {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) (hs : sortOf (.bits n) = some t.1) : f.1 = n
theorem unField_outKind_sort {o : OutField} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (outKind o) f = some t) (hw : o.width = (toField t.1 t.2).1) : sortOf (outKind o) = some t.1
-- the `ok` rows that supply sorts / widths (projections of `d.ok = true`, MachineData: Tools.ShippingMachineAuto)
theorem ok_K_nexts {d : MachineData} (h : d.ok = true) : ∀ i, i < d.ss.length → d.K (d.nIn + i) = d.ss[i]?
theorem ok_letsTyped {d : MachineData} (h : d.ok = true) : LetsTyped d.bpos d.vpos d.kb d.kv d.vw d.K (d.nIn + d.ss.length) d.ls
theorem ok_outsFit {d : MachineData} (h : d.ok = true) : outsFitB d.kb d.kv d.vw d.fields d.shape.layout.outs d.outs = true
```
**Withdrawal (R1).** rev1's `toField_unField {k} {f} {t} (h : unField k f = some t) (hre : toField t.1 t.2 = f) : sortOf k = some t.1` is **false** in the present types: `unField (.bits n)` (`ShippingMachineCommand.lean:267`) ignores `n`. Counterexample (kernel `rfl`/`decide` in `Tests/Gen5/DataOfCheck2.lean` §3): `k = .bits 8`, `f = ⟨16, .bitsLit 16 0⟩`: `unField (.bits 8) f = some ⟨.bits 16, .bitsLit 16 0⟩`, `toField (.bits 16) (.bitsLit 16 0) = f`, but `sortOf (.bits 8) ≠ some (.bits 16)`. The check file also rejects the old statement as a MUTANT (signature/defeq rejection of the changed statement, not a semantic counterexample) next to the kernel counterexample. Nothing in this freeze depends on `toField_unField`; `dataOfAt_sound` does not use any `unField` lemma (its `ok` conjunct is the guard, §2.3).

**Where the declared width/sort of a field comes from, by `file:line` [B]** (answer to R1): see the row S-WIDTH of §4. In short: lets from `ok` conjunct :242 (`LetsTyped`), nexts from :241 (and :223-225 + :235), outs from :244 (`outsFitB`); the `splitLets` / `splitFields` lengths from `splitLets_some` / `splitFields_some` and the `ok` rows `layout.lets = letBs.length` (:219), `nIn + ss.length ≤ binders.length` (:218); the re-pack comparison (`bitsBeq`) contributes the shape of `.bool` fields (`mux c 1#1 0#1`) and the whole term, not the `.bits n` width. `unField_bool` is deliberately weak (any width, any branches), which is why the comparison cannot be dropped.

* **U-F shape preservation** (needs `dataOfAt`): `dataOfAt lvl E senv s = some d → d.shape = s` and
  `dataOfAt lvl E senv s = some d → d.shape.binders.length = d.nIn + d.ss.length + d.letBs.length`.
* **U-G** closed instances of §2.5 (K), after the Q5 split, evidence only.

Order **[rev2]**: U-D, U-E (step 1b) are written; then `dataOfAt` (or `dataOfFrom`) and its `_shape/_ok` (step 2); `dataOfAt_sound` (step 3); `dataOf` (step 4,
needs READKINDS's `exprSize`; until it lands only `dataOfAt` is delivered). Estimate for the rest 400-700 lines (an estimate, not a result).

## 6. Expected-type / closure / axiom audit plan

**[rev2]** `Tests/Gen5/DataOfCheck2.lean` (new Check, same form, imports `Tests.Gen5.DataOfCheck` for `reach`) covers §5b: TYPE for the 16 lemmas (independent `Exp…` statements with the same binder names), 8 MUTANT rejections (the withdrawn `toField_unField`, `unField_sortOf` without `hw`, the one-way iff, `unField_bool` with fixed branches, `splitLets_some` without the length, `splitFields_some` without `0 < n`, `bposL_eq` against `posV`, `ok_K_nexts` without `h`; rejections by signature / defeq of a changed statement, NOT semantic counterexamples), 12 kernel controls (the R1 counterexample `unField (.bits 8) ⟨16,…⟩` with the re-pack equal and the sorts different; `unField .bool` on a mux with any width/branches; refusals; the position lists on `[bool, bits 3, domain, bool]`), REACH (explicit walk through `DataOfCheck.reach`, with its four detector controls; body-less / opaque counts printed, e.g. `String.Internal.append` for the `ok_*` lemmas through `MachineData.ok`; bodies of opaque constants are not explored) and AXIOMS. **Value closure** is the explicit-body walk of REACH.

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
| B1 | `Expr.equal a b = true → a = b` | would turn C-CMP (§4) into an equation on runs of the auxiliary `readMachine`; **it does not by itself supply C-QWIT** (§4: the compiler's reader, the quote witness) | new law; **not proposed** (READKINDS B1) |
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

* **[rev2]** Lean exists for §5a (built, doc-bc9a300d) and for §5b U-D/U-E (`Tools/ShippingGen5DataOfPure2.lean`, `Tests/Gen5/DataOfCheck2.lean`: clean issue-linked build do3v-62ea2479 exit 0, 758 jobs, scoped approved at 62ea2479). The rev1 sentence follows for the older parts: Only §5a and the first check file exist as Lean (rev1); everything else here is design, line counts are estimates. No claim that every `dataOfAt` execution terminates (§2.4a T-X).
* No claim that `dataOfAt` returns `some` on any successful run (coverage, DG-COVER); no claim that it does not.
* `initOk_of_ok` is written and passed plain `lean` elaboration on the oleans of an earlier build; its `kjob lake build` result is in the Issue note, not claimed here. No claim that `ok` is implied by anything in the run.
* **[rev2]** No claim that a successful production run satisfies C-CMP or C-QWIT, and no claim that the auxiliary `readMachine` is (or is not) the compiler's reader beyond the READKINDS provenance note; no claim that `dataOfFrom`'s output equals `readMachine`'s for the real values of the partial helpers (S-COV-FLOAT, DG-COVER).
* No claim about `rootFloat` / `packTupleInputs` beyond using their values; no claim about `Expr.equal`.
* No claim that DG-READKINDS U1-U4 are proved; this document uses only the already-existing `readN_expr_sound`.
* The `dataOf` line (§2.2) is conditional on READKINDS exporting `exprSize`; until then only `dataOfAt` exists.

## 10. rev3 freeze addition: row 6b projection lemmas (DG-COVER `ShapeAgree`, `d` side) **[agent g5do-r6; written BEFORE the Lean]**

Source of the row: `kjob/g5cv-r9 8e01a9cf` `scripts/gen5/DG_COVER_FREEZE_REV5.md` row 6b (owner DG-DATAOF). Consumer: `kjob/g5cv-r11 9b9cdd55`
`Tools/ShippingGen5Cover5.lean` `shapeAgree_of_sides`, whose `d`-side premises are, for one `d` and one `sp`:
`hsp : d.shape = sp`, `hss : d.ss.length = sp.layout.slots.length`, `hls : d.ls.length = sp.layout.lets`, `hn : sp.insts.length ≤ d.nIn`.
(That branch is not in this tree; its text was read with `git show`; the match below is by reading, and `DataOfCheck4` states the four premises independently.)

New file `Tools/ShippingGen5DataOfDims.lean` (imports `Tools.ShippingGen5DataOf`; namespace `Tools.ShippingGen5DataOf`; nothing in an existing file changes).
Check: `Tests/Gen5/DataOfCheck4.lean`. No new law / TRUSTED / definition change.

### 10.1 Exact statements (full types)

```lean
theorem typedFields_length {ks : List MixedGateBinder} {fs : List (Σ w : Nat, Term (.bits w))}
    {r : List (Σ s : SType, Term s)} (h : typedFields ks fs = some r) :
    r.length = min ks.length fs.length

theorem dataOfFront_some {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {nIn : Nat} {dom : Lean.Expr}
    (h : dataOfFront E senv shape tin fl = some (nIn, dom)) :
    (∃ p, mixedGatePeel tin = some p ∧ nIn = p.1.length + shape.insts.length) ∧
    shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets

theorem dataOfTail_dims {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {W : Nat} {whole : Term (.bits W)}
    {d : MachineData} (hb : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
    (h : dataOfTail shape nIn dom W whole = some d) :
    d.nIn = nIn ∧ d.ss.length = shape.layout.slots.length ∧ d.ls.length = shape.layout.lets

theorem dataOfCore_dims (lvl : Lean.Expr → Nat) {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {d : MachineData}
    (hb : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
    (h : dataOfCore lvl shape nIn dom = some d) :
    d.shape = shape ∧ d.nIn = nIn ∧ d.ss.length = shape.layout.slots.length ∧ d.ls.length = shape.layout.lets

/-- Row 6b, `d` side, in the consumer's premise shape: the same `d` and the same `s`. -/
theorem dataOfFrom_dims (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn

/-- Sharper `nIn`: it is the peeled-binder count plus the instance count. -/
theorem dataOfFrom_nIn (lvl : Lean.Expr → Nat) {E senv s tin fl d}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    ∃ p, mixedGatePeel tin = some p ∧ d.nIn = p.1.length + s.insts.length

/-- Soundness and the row-6b facts about ONE `d` from ONE `h` (not two witnesses joined by `∧`). -/
theorem dataOfFrom_sound_dims (lvl : Lean.Expr → Nat) {E senv s tin fl d}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    (d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
      d.initOk (initsOf d) = true) ∧
    (d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn)

theorem dataOfAt_dims (lvl : Lean.Expr → Nat) {E senv s d} (h : dataOfAt lvl E senv s = some d) :
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn

theorem dataOfAt_sound_dims (lvl : Lean.Expr → Nat) {E senv s d} (h : dataOfAt lvl E senv s = some d) :
    (same conjunction as dataOfFrom_sound_dims)
```

(`{E senv …}` are shorthand here; the Lean has the full binder types of `dataOfFrom_sound`.)

### 10.2 Match with `shapeAgree_of_sides` (and the difference)

`dataOfFrom_dims h` / `dataOfAt_dims h` is, up to conjunction order, exactly `⟨hsp, hss, hls, hn⟩` with `sp := s`, so
`obtain ⟨hsp, hss, hls, hn⟩ := dataOfAt_dims lvl h; exact shapeAgree_of_sides hs hsp hss hls hn` has no glue lemma.
Difference: the consumer's `hs` (state side) and `sp` come from a fuel-model run (`machineShapeF`, DG-COVER); that `s` here (the argument
of `dataOfAt`) is the same `sp` as in that run is a hypothesis the CONSUMER has to state (`s` is a free argument of `dataOfFrom`/`dataOfAt`);
this file does not and cannot identify them. Soundness and dims are joined only through the single `h` (`*_sound_dims`), never by
conjoining two different `dataOf` walks.

### 10.3 Proof plan (no new facts)

`mkData`'s fields: `d.nIn = nIn`, `d.ls = ls`, `d.ss = nl.map (·.1)`, `d.shape = shape` by `rfl`. `splitLets_some` and `splitFields_some` (U-E) give
`lc.1.length = lets` and `fs.length = nOuts + nSlots`; `typedFields_length` (zip-then-`mapM`) gives the two lengths as `min`; the front guard
`shape.binders.length == nIn + nSlots + nLets` (`dataOfFront`) makes the `min`s the claimed values. Without that guard (i.e. for `dataOfCore` alone) the
lengths are NOT claimed: `dataOfCore_dims` takes it as a hypothesis, and `dataOfFrom_dims` discharges it from `dataOfFront_some`.

### 10.4 Check (`Tests/Gen5/DataOfCheck4.lean`): same discipline as Check3

TYPE against independently written `Prop`s (the consumer's four premises written from the Cover5 text, not copied from the Lean statement), by the same
reducible comparator (`checkExpected`); MUTANTS by `checkMutant` (single changes: `ss`↔`ls` swapped, `≤` → `<`, `lets` → `slots.length`, the `d.shape = s`
conjunct dropped, the conjunction of `dataOfFrom_sound_dims` cut to its first half) — signature/defeq rejections, NOT semantic counterexamples; closure by
the common `Tests.Gen5.DataOfCheck.reach` (unknown names fail); axioms standard only; no `sorry`. Counts are reported by the build log with the partition
(TYPE / MUTANT / REACH / AXIOMS) and the summing rule (each Check file counted separately).

### 10.5 Not supplied by §10

That `dataOfAt` is `some`; `s` being the run's `sp`; that `d.ss`/`d.ls` entries (not lengths) agree with the state; the state-side half (row 6a) and `LenOk`.

## 11. rev3 coverage / real-reader survey (agent g5do-r6) — what closes, what does not

Wording: "この調査では供給元・経路が見つからなかった" means this survey (grep of this tree and of `kjob/g5rk-impl`, `kjob/g5cv-r11` by `git show`) found none; it does not say the fact is false or underivable.
Goal of the survey: from existing theorems, a path to (Cov) "`dataOfAt lvl E senv s = some d` on every successful machine-route run" and (Rdr) agreement with the compiler's actual reader.

### 11.1 Row 6b (supplied, §10)
`d.shape = s`, `d.ss.length`, `d.ls.length`, `d.nIn` for the `d` of one success: supplied by `dataOfFrom_dims`/`dataOfAt_dims` (agent build, clean build pending). 

### 11.2 Conditions for `dataOfFrom … = some _` and where each could come from

| # | Condition read off `dataOfFront`/`dataOfCore`/`dataOfTail`/`checked` | Existing source | Status |
|---|---|---|---|
| 1 | `mixedGatePeel tin = some p` (tin = `packTupleInputs entryV`, a `partial def`) | none (opaque to the kernel; `RootFacts` U5 of READKINDS not supplied) | 未供給 / この調査で経路未発見 |
| 2 | `shape.binders.length = p.1.length + insts.length + slots.length + lets` | row 6a/6b-type length facts exist only in the fuel model (Cover5 T2/T3, `kjob/g5cv-r11`, needs `LenOk` and `ShapeFuelBridge`); no statement ties `shape.binders` to `p.1` | 未供給 / この調査で経路未発見 |
| 3 | `srcDomOf`, `srcDom'Of`, `machDom?`, `machTupleKinds?`/`machOuts?` all `some` | total functions in this tree, but no theorem says they are `some` for a production `E`/`entryBody` (`fl = rootFloat`, `partial`) | 未供給 / この調査で経路未発見 |
| 4 | `readN (kindsCfg …) (lvl shape.body) shape.body = some ⟨.bits W, whole⟩` | completeness `readN_quote` / `readTot_of_quote_body` exist ON `kjob/g5rk-impl` (U1–U4, audit status not claimed here), NOT in this tree; they have the premise `shape.body = quote … d.packed` with `WF` facts (C-QWIT), which has no run supplier. Even then `lvl shape.body` must dominate `liftDepth` (`readTot` uses `exprSize`; `dataOf` at `exprSize` is not defined in this tree) | 未供給 / C-QWIT 供給元未発見 |
| 5 | `splitLets lets ⟨W,whole⟩ = some _` and `splitFields (nOuts+nSlots) core = some _` | only the converse direction exists (`splitLets_some`, `splitFields_some`: output ⇒ `t = packLets/packAll …`, U-E). The direction "`packLets fs core` ⇒ `splitLets … = some (fs, core)`" for the packed term of a `MachineData` was not found in the tree | 未供給 / この調査で経路未発見 |
| 6 | `typedFields` successes (a `.bool` binder needs the field to be a `mux`) | the `ok` rows give sorts/widths (`ok_K_nexts`, `ok_letsTyped`, `ok_outsFit`, §5b) but only for a `d` that already exists; no source of the `mux` shape of a Bool field | 未供給 / この調査で経路未発見 |
| 7 | `bitsBeq ⟨W,whole⟩ ⟨_, d.packed⟩ = true` | `bitsBeq_refl` (§5a) gives it when `whole` is syntactically `d.packed`; that needs 4 and 5 for the same `d` (`mkData`'s `packed` is computed from `d`'s `letFields`/`core`, so it is the re-pack of 5's pieces) | 条件付き (4,5 が来れば閉じる見込みだが未証明) |
| 8 | `d.ok = true` | S-OK (§4) | 未供給 (DG-COVER / DG-WFCOVER) |

Net: (Cov) is not closed. Rows 1, 2, 3, 4, 5, 6, 8 are open; 7 depends on 4 and 5. No existing theorem makes `dataOfAt` `some`.

### 11.3 (Rdr): agreement with the real reader
(a) With the auxiliary `readMachine` (`Tools/ShippingMachineCommand.lean:440`): `dataOfFrom` is built from the same pieces but replaces `unq` + the opaque `q.equal` by `readN` + `bitsBeq`; no theorem relates the two outputs, and `readMachine` is a `MetaM` command (not a function the kernel can unfold). 未供給 / この調査で経路未発見.
(b) With the compiler's reader (the one the machine route runs): its identity/location is not established by this Issue (§4 C-QWIT); no link from `dataOfAt` found.
(c) The values `tin`, `fl` versus those used by `machineShape?` (S-COV-FLOAT): both are `partial`; no producer found.

### 11.4 What is and is not supplied after this rev
Supplied (conditional, agent builds / clean-build pending where stated): §10 projections for the `d` of a successful `dataOfFrom`/`dataOfAt`.
Not supplied: (Cov), (Rdr), `s = sp` identification with the DG-COVER run, row 6a, C-CMP, C-QWIT, S-OK, S-COV-FLOAT, T-X, `dataOf` at `exprSize`. This is not an Issue/M5/FG completion.
