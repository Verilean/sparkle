# DG-READKINDS full-type freeze, rev2 (Issue sparkle-gen5-dg-readkinds)

rev2 answers the reviewer's changes_requested on rev1 (7bd14596): R1 (U4 full type), R2 (U5(a) provenance), R3 (partial-def
agreement wording). See §0. Sections not named in §0 are unchanged from rev1 except where noted inline (`rev2`).

Design sources: `par/gen5-t2:scripts/gen5/` `M5_INDEP_STUDIES.md` §B (reader inventory), `DGEN_FREEZE.md` (§2.4 R5 and its
unit table, row DG-READKINDS / DG-DATAOF / DG-COVER), `T2COVER_FREEZE.md` rev2 (c398021c). Line numbers below were
re-read on this branch (HEAD d0ddc50b); `[S]` = this tree.

**Status: design only. No Lean written, nothing built. Not submitted for implementation until the reviewer approves.**
New Lean goes in a new file `Tools/ShippingGen5ReadKinds.lean` and a new check `Tests/Gen5/ReadKindsCheck.lean`
(lakefile `lean_lib` additions only). No compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`
edit. No new TRUSTED boundary, law, FG/guarantee change. Everything that would need one is in §6, kept apart.

Wording rule used throughout: "not supplied / this survey found no source or route" is a statement about this
survey, not an impossibility claim. A "mutant" in §4 is a rejection by signature / defeq of a changed statement, not
a semantic counterexample.

---

## 0. Response to changes_requested on rev1 (7bd14596)

Reviewer verdict: reader core (U1-U3) may go ahead; fix U4's full type and U5's run provenance. FG is not reduced by this
revision; nothing in §1-§3 is dropped. Q1 (new file, recursion/eval helper), Q3 (quotation-only monotonicity), Q4 (U1-U4
intermediate; Issue-wide body quotation/normalization coverage stays OPEN) are taken as the reviewer answered; Q2 is
not adopted (see R2).

* **R1 (U4 ellipsis).** §2.4 now states `readTot_of_quote_body` with no `…`, plus two transport lemmas `kindsCfg_quote_args`
  (U4a) and `packed_wf_cfg` (U4b). The width function: `d.vwL = widV (kindsOf d)` is the premise `hw` that moves
  `d.packed.WF d.kb d.kv d.vw` to `WF` over `kindsCfg`'s `kb kv vw`. This `hw` is **U4's** statement; U3's `hw`
  (`machine_wf_of_readN`) transports the other way (WF from the reader's `cfg` back to `d`). They are two different
  propositions with the same hypothesis name; §2.4 says so and §4 compares both.
* **R2 (U5(a) provenance).** The rev1 sentence "the run executed `readMachine`, so `RootFacts` is supplied" is
  **withdrawn**. §2.5 now records what the survey read (`RunReadsAt` contains the compiler core's `machineShape?` /
  translator run, not `MachineCommand.readMachine`), the fully bound `RootFacts`, and which execution a producer must
  come from. **`RootFacts` is not supplied** by `RunReadsAt` on the present path. A value equation alone also does not
  give semantic preservation or quotation (§2.5).
* **R3 (partial agreement wording).** "Agreement with the `partial` defs is impossible / always TRUSTED" is replaced by
  "this survey found no route under the present boundary; not supplied; not claimed impossible" in §2.5(b), §3, §6 B2 and §8.

---

## 1. Reader kinds: compiler side, proved range, uncovered kinds

### 1.1 Compiler-side readers (what production runs)

| reader | file:line [S] | note |
|---|---|---|
| `unq` | `Tools/ShippingMachineCommand.lean:93` (`partial def`, to :247) | reads the 21 `Term` constructors (`Term`: `Tools/ShippingUnifiedSource.lean:39-75`); `partial` ⇒ no equation lemma |
| `splitLets` / `splitFields` / `unField` | `ShippingMachineCommand.lean:250` / :257 / :265 | total `def`s |
| `readMachine` | `ShippingMachineCommand.lean:440` | calls `unq c shape.body` (:515), then the opaque `q.equal shape.body` check (:533) |
| `packTupleInputs` | `Sparkle/Compiler/MachTupleIn.lean:79` (`partial def`) | called at `readMachine` :463 |
| `rootFloat` | `Sparkle/Compiler/MachRawSurface.lean:198` (`partial def`) | called at `readMachine` :467 |
| `zetaAll` | `Sparkle/Compiler/MachRawSurface.lean:219` (`partial def`) | not called inside `readMachine` :440-541 in this tree; listed by the M5 studies as part of the shape layer; its call sites were not re-surveyed here |
| `machDom?` | `Sparkle/Compiler/Elab.lean:4269` (`def`) | used at `readMachine` for `dom` |
| `machineShape?` | `Sparkle/Compiler/Elab.lean:5072` | calls the `partial` shape helpers (`machNorm` …) |
| local `loopLet` / `resDom` | `ShippingMachineCommand.lean` inside `readMachine` (`let rec`) | structural over `Expr` |

Of the 21 `Term` constructors, the production `unq` result must fit the total readers below.

### 1.2 Total readers (the proof-side model) and the proofs that exist

| reader | kinds | def file:line [S] | soundness (exists) | completeness on quotations |
|---|---|---|---|---|
| `readTerm` | 11 | `ShippingReaderTerm.lean:1061` | `readTerm_sound` (:1129 per M5 study) | `readTerm_quote` `ShippingReaderComplete.lean:548`, `readTerm_expr_quote'` `ShippingReaderKinds.lean:86` |
| `readTerm2` | 18 | `ShippingReaderNodes2.lean:604` | `readTerm2_reads` :607, `readTerm2_sound` :613, `readTerm2_expr_sound` :620 | `readTerm2_quote` `ShippingReaderComplete2.lean:484` (premise `core2 t`, `Complete cfg`, `t.WF`), `quote2_injective` :593, `readTerm2_extends_on_quotes` :605 |
| `readN cfg k` | 21 (3 lifts by level `k`) | `ShippingReaderApp.lean:336` | `readN_reads` :340, `readN_sound` :349, `readN_expr_sound` :356 | **none** (header `ShippingReaderApp.lean:45-52`) |

Facts used below (read from source, not proved here):
* `readN cfg 0 = readTerm2 cfg`; `readN cfg (k+1) = readWith (readInput cfg) (readNode3 (readN cfg k) cfg)` (:336-338).
* `readNode3 sub cfg c ls args = alt (readNode2 cfg c ls args) (readApNode sub cfg c ls args)` (:318-320). `readApNode`
  needs five arguments, the fourth an application `f a`; `sub` reads `a` (:283-287). The second operand is the
  ordinary argument reading of `readWith` at the same level.
* `core2` (`ShippingReaderComplete2.lean:423`) is `False` on `appCompare` / `appBool` / `appBool2`; so
  `readTerm2_quote` says nothing about a term containing a lift anywhere.
* `Complete cfg` (`ShippingReaderComplete.lean:540`): `domOk`, `boolOut`, `bitsOut`. `kindsCfg_complete'`
  (`ShippingReaderKinds.lean:79`) discharges it for the endpoint configuration, for every binder list.
* `machine_body_of_read` / `machine_wf_of_read` (`ShippingReaderMachine.lean:20-71` region) are stated for `readTerm`
  with `readTerm_kinds_sound`; no `readTerm2` / `readN` form exists.
* Build status of `ShippingReaderApp.lean`: lakefile `lean_lib «Tools.ShippingReaderApp»` (lakefile.lean:2205) and
  `Tests/AllTests.lean:278` imports `Tests.Compiler.ReaderAppTest`. The file header (:55) still says "UNVERIFIED …
  not built". **This survey did not settle whether it builds**; building it is step 0 of §5 (a build result will be
  recorded, not assumed).

### 1.3 Kind-by-kind table (21 constructors)

| kind | `unq` | total reader | sound | complete on quotations | READKINDS work |
|---|---|---|---|---|---|
| boolInput, bitsInput, boolLit, bitsLit, binary, compare, boolBinary, boolNot, boolEq, mux, concat (11 `core`) | yes | `readTerm` ⊂ `readTerm2` ⊂ `readN` | yes | yes (`readTerm_quote`, `readTerm2_quote`) | none beyond lifting to `readN` (U2) |
| bitsNum, setw, slice, zextMap, sliceF, concatLitHi, concatLitLo (7) | yes | `readTerm2` (Nodes2: `readBitsNum` :246, `readSetw` :278, `readSlice` :318, `readZext` :361, `readSliceF` :405, `readConcatHi` :452, `readConcatLo` :499) | yes | yes (`readTerm2_quote`) | none beyond lifting to `readN` (U2) |
| appCompare | yes (`unq`, :159-166 per study) | `readApCmp` `ShippingReaderApp.lean:221` via `readNode3` / `readN` | yes (`readApCmp_sound` :226) | **not covered** | U1, U2 |
| appBool | yes (:167-170) | `readApBool` :153 | yes (`readApBool_sound` :160) | **not covered** | U1, U2 |
| appBool2 | yes (:171-174) | `readApBool2` :187 | yes (`readApBool2_sound` :194) | **not covered** | U1, U2 |

Beyond `Term`: `rootFloat`, `packTupleInputs` (and `machDom?`, `loopLet`, `resDom`) are in `readMachine`, not in
`Term`; no total replacement and no proof about them is supplied by existing exports along the readN route
(M5 study §B.4). Existing `Tools/ShippingGen3ArgSupply3.lean:1103-1346` states facts **under the premise**
`rootFloat v = .letE …` (the partial function's value is a hypothesis, never unfolded); that pattern is the only
treatment found.

### 1.4 What is NOT covered (the work of this Issue)
1. Completeness of `readN` on the three lifts (and on any term mixing them with the 18 kinds), with a level bound.
2. `readN` forms of `machine_body_of_read` / `machine_wf_of_read`.
3. Body-is-quotation for a body produced by a successful run (production uses only the opaque `Expr.equal`).
4. A total replacement (or an avoidance) for `rootFloat` / `packTupleInputs` in `dataOf`.

---

## 2. Lemmas to add (complete types)

File `Tools/ShippingGen5ReadKinds.lean`, namespace `Tools.ShippingGen5ReadKinds`, opening
`Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingReaderTerm Tools.ShippingReaderInputs
Tools.ShippingReaderNodes2 Tools.ShippingReaderApp Tools.ShippingReaderComplete Tools.ShippingReaderComplete2
Tools.ShippingReaderKinds Tools.ShippingReaderMachine`. `autoImplicit false`. Imports only existing modules
(`Tools.ShippingReaderApp`, `Tools.ShippingReaderComplete2`, `Tools.ShippingReaderKinds`,
`Tools.ShippingReaderMachine`). Variable `{cfg : Cfg}` as in the cited files.

### 2.0 New definitions (all new, none edited)

```lean
/-- Nesting depth of applicative lifts through FIRST operands (what `readN` levels pay for). -/
def liftDepth : {s : SType} → Term s → Nat
  | _, .boolInput _ => 0   | _, .bitsInput _ _ => 0   | _, .boolLit _ => 0
  | _, .bitsLit _ _ => 0   | _, .bitsNum _ _ => 0
  | _, .binary _ a b => max (liftDepth a) (liftDepth b)
  | _, .compare _ a b => max (liftDepth a) (liftDepth b)
  | _, .boolBinary _ a b => max (liftDepth a) (liftDepth b)
  | _, .boolNot a => liftDepth a
  | _, .boolEq a b => max (liftDepth a) (liftDepth b)
  | _, .mux c a b => max (liftDepth c) (max (liftDepth a) (liftDepth b))
  | _, .setw _ a => liftDepth a
  | _, .slice _ _ _ a => liftDepth a
  | _, .concat a b => max (liftDepth a) (liftDepth b)
  | _, .concatLitHi _ _ b => liftDepth b
  | _, .concatLitLo a _ _ => liftDepth a
  | _, .zextMap _ _ a => liftDepth a
  | _, .sliceF _ _ _ a => liftDepth a
  | _, .appCompare _ a b => max (liftDepth a + 1) (liftDepth b)
  | _, .appBool _ a b => max (liftDepth a + 1) (liftDepth b)
  | _, .appBool2 _ a b => max (liftDepth a + 1) (liftDepth b)

/-- Structural size of an expression (own definition, so its equations are plain). -/
def exprSize : Lean.Expr → Nat
  | .app f a => exprSize f + exprSize a + 1
  | .lam _ t b _ => exprSize t + exprSize b + 1
  | .forallE _ t b _ => exprSize t + exprSize b + 1
  | .letE _ t v b _ => exprSize t + exprSize v + exprSize b + 1
  | .mdata _ e => exprSize e + 1
  | .proj _ _ e => exprSize e + 1
  | _ => 1

/-- The total reader with its level taken from the expression. -/
def readTot (cfg : Cfg) (e : Lean.Expr) : Option AnyTerm := readN cfg (exprSize e) e
```
(The constructor arities of `Term` are those of `ShippingUnifiedSource.lean:39-75`; the exact `max`
shapes are adjusted to the constructors when written. `liftDepth` is a measure, not a spec.)

### 2.1 U1 — completeness of `readN` (the main theorem)

```lean
theorem readN_quote {cfg : Cfg} (hc : Complete cfg) :
    ∀ {s : SType} (t : Term s) (k : Nat), liftDepth t ≤ k → t.WF cfg.kb cfg.kv cfg.vw →
      readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩
```
No `core2`/`core` premise: all 21 kinds. Proof route (not tested): induction on `t`, generalizing `k`.
* `k = 0` ⇒ `liftDepth t = 0` ⇒ `t` has no lift ⇒ `core2 t` (auxiliary `core2_of_liftDepth_zero`, below) ⇒ `readTerm2_quote`.
* `k+1`, non-lift node: the seven `_eval` lemmas of `ShippingReaderComplete2.lean:125-230` are reader-generic and
  used as they are; the other kinds go through U1a' (`readN_succ_app3..6` + `readNode3` = `alt (readNode2 …) …`).
* `k+1`, lift node: `readNode2 … = none` on a `Signal.ap` head (U1b), then `readApNode` with `sub := readN cfg k` on the
  first operand (`liftDepth a ≤ k`) and the level-`k+1` reading on the second.

Auxiliary statements (each a separate lemma, full types):

```lean
theorem core2_of_liftDepth_zero : ∀ {s : SType} (t : Term s), liftDepth t = 0 → core2 t
```
(`core2` excludes only the three lifts, whose `liftDepth` is ≥ 1; the other 18 kinds, including `bitsNum` etc., are in `core2`.)

U1a — node-level evaluation lemmas. The seven `_eval` lemmas of `ShippingReaderComplete2.lean` (`readBitsNum_eval` :125,
`readSetw_eval` :135, `readSlice_eval` :148, `readZext_eval` :163, `readSliceF_eval` :177, `readConcatHi_eval` :195,
`readConcatLo_eval` :213) are already reader-generic: their sub-readings are hypotheses `r4 = some ⟨.bits w, a⟩` on an
arbitrary `Option AnyTerm` (read at :135-147), so they are used **unchanged** for `readN`. No restatement.
The first eleven kinds (`boolInput` … `concat`) have no extracted `_eval` lemma: `readTerm2_quote` proves them inline
in its recursion (`ShippingReaderComplete2.lean:484-590`, using `readTerm2_app3..app6` :393-415 and the `read*_head`
lemmas :234-375, which are specific to `readTerm2`). For `readN` the same unfolding is needed with `readN (k+1)`:

```lean
/-- U1a': `readN (k+1)` unfolds as `readTerm2` does (the `readTerm2_app3..app6` family, :393-415), with `readNode3`. -/
theorem readN_succ_app3 {cfg : Cfg} {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} :
    readN cfg (k+1) (.app (.app (.app (.const c ls) x0) x1) x2) =
      readNode3 (readN cfg k) cfg c ls
        [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2)]
```
(and `readN_succ_app4`, `readN_succ_app5`, `readN_succ_app6` for 4, 5, 6 arguments; the exact right-hand side is
what `readTerm2_app3..6` say with `readNode2 cfg` replaced by `readNode3 (readN cfg k) cfg`, so each is the
`readWith_app3..6` lemma of `ShippingReaderTerm.lean:1139-1161` — whose form is read when written.) Together with
`readNode3 sub cfg c ls args = alt (readNode2 …) (readApNode …)` and `alt_some_left`, a non-lift node at level `k+1`
returns what `readNode2` returns on the same argument readings. This (not "restating the eval lemmas") is the real
extra work of step 2 of §5, and §7 Q1 is whether the eleven kinds' inline arms are extracted into lemmas or the recursion is redone for `readN`.

```lean
/-- U1b: heads. On an applicative-lift quotation the eighteen-kind node reader gives none. -/
theorem readNode2_ap_none {cfg : Cfg} (c : Lean.Name) (hc : c = ``Sparkle.Core.Signal.Signal.ap)
    (ls : List Lean.Level) (args : List Arg) : readNode2 cfg c ls args = none
```
(Expected by the header of `ShippingReaderApp.lean`: "the kinds' head constants are disjoint"; for five-argument
`Signal.ap` nodes. The statement may need the five-argument hypothesis `args.length = 5`; if some node reader
accepts `Signal.ap` on other shapes the lemma is restricted to the shape `quote` produces. **Not checked.**)

The induction hypothesis of U1 is what the `sub` argument of `readApNode` receives (no separate lemma).

The three lift constructors get one evaluation lemma each (U1d):
```lean
theorem readAp_appBool_eval {cfg} (hd : cfg.isDom cfg.dom = true) (op : SignalBoolBinKind)
    {a b : Term .bool} {ra rb : Option AnyTerm}
    (ha : ra = some ⟨.bool, a⟩) (hb : rb = some ⟨.bool, b⟩) :
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (.const ``Bool []) (.const ``Bool [])
      (mapHeadE cfg.dom (.const ``Bool []) (appBoolBodyE op)) ra rb = some ⟨.bool, .appBool op a b⟩
theorem readAp_appBool2_eval {cfg} (hd : cfg.isDom cfg.dom = true) (f : AppBool2)
    {a b : Term .bool} {ra rb : Option AnyTerm}
    (ha : ra = some ⟨.bool, a⟩) (hb : rb = some ⟨.bool, b⟩) :
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (.const ``Bool []) (.const ``Bool [])
      (mapHeadE cfg.dom (.const ``Bool []) (appBool2BodyE f)) ra rb = some ⟨.bool, .appBool2 f a b⟩
theorem readAp_appCompare_eval {cfg} (hd : cfg.isDom cfg.dom = true) (op : SignalCompareKind) {w : Nat}
    {a b : Term (.bits w)} {ra rb : Option AnyTerm}
    (ha : ra = some ⟨.bits w, a⟩) (hb : rb = some ⟨.bits w, b⟩) :
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (bitVecE w) (.const ``Bool [])
      (mapHeadE cfg.dom (bitVecE w) (appCompareBodyE op w)) ra rb = some ⟨.bool, .appCompare op a b⟩
```
(`readAp`'s arguments are `(cfg c ls x0 x1 x2 f ra rb)`, `ShippingReaderApp.lean:253`; the second `x1`/`x2` slots
follow `appE` (`ShippingUnifiedSource.lean:277`): dom, element type, `Bool`, then `.app (mapHead…) a`, `b`.)
Their proofs depend on three facts that are **each a separate small lemma**, none supplied today:
* `pickBy` finds the operator when its quoted head is in the list and distinct operators have distinct heads:
  `boolOp?_self`, `bool2Op?_self`, `cmpOp?_self` of the form
  `boolOp? dom (mapHeadE dom (.const ``Bool []) (appBoolBodyE op)) = some op` (and `bool2Op?`, `cmpOp? dom w` likewise).
  Needs the pairwise distinctness of the 3 / 3 / 5 head expressions by `eqE` (`decide` on closed `Expr` equality of
  `BitVec.ult` vs `BitVec.ule` … at symbolic `w` is by constructor/name discrimination, not by `decide`).
* `bitVecE? (bitVecE w) = some w` and `isConst ``Bool (.const ``Bool []) = true`.
* `lvl1 [.zero] = true`; `lastApp? (.app f a) = some (f, a)` (the latter is `rfl`).

Corollaries (full types):

```lean
/-- U1e: with the endpoint configuration, no condition on the binders. -/
theorem readN_expr_quote (dom : Lean.Expr) (ks : List MixedGateBinder) {s : SType} (t : Term s) (k : Nat)
    (hk : liftDepth t ≤ k)
    (hw : t.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0)) :
    readN (kindsCfg dom (isExpr dom) ks) k
      (quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) t) = some ⟨s, t⟩
/- proof: readN_quote (kindsCfg_complete' dom (isExpr dom) (isExpr_self dom) ks) …  where
   `isExpr dom dom = true` is the premise `hdom` of `kindsCfg_complete'`; see below. -/

/-- U1f: quote is injective on all 21 kinds. -/
theorem quote_injective {cfg : Cfg} (hc : Complete cfg) {s s' : SType} (t : Term s) (t' : Term s')
    (hw : t.WF cfg.kb cfg.kv cfg.vw) (hw' : t'.WF cfg.kb cfg.kv cfg.vw)
    (h : quote cfg.dom cfg.bools cfg.bits t = quote cfg.dom cfg.bools cfg.bits t') :
    (⟨s, t⟩ : AnyTerm) = ⟨s', t'⟩
```
(Proof: `readN_quote` at `k := max (liftDepth t) (liftDepth t')`, same shape as `quote2_injective` :593.)

The hypothesis `hdom : isDom dom = true` of `kindsCfg_complete'` is stated with `isDom := isExpr dom`; the corollary
needs `isExpr dom dom = true`. If that is not already an exported lemma it is U1g:
`theorem isExpr_self (dom : Lean.Expr) : isExpr dom dom = true`.
(`ShippingReaderInputs.lean:268`; `readTerm_expr_quote'` :86 passes the same premise, so a lemma may already exist
under another name: **to be located before writing**; if it exists U1g is dropped.)

### 2.2 U2 — level bound and monotonicity

```lean
theorem liftDepth_le_exprSize {cfg : Cfg} {s : SType} (t : Term s) :
    liftDepth t ≤ exprSize (quote cfg.dom cfg.bools cfg.bits t)

theorem readTot_quote {cfg : Cfg} (hc : Complete cfg) {s : SType} (t : Term s)
    (hw : t.WF cfg.kb cfg.kv cfg.vw) :
    readTot cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩
```
`readTot_quote` is `readN_quote hc t _ (liftDepth_le_exprSize t) hw`. `liftDepth_le_exprSize`: structural induction,
each `quote` constructor is at least one `app` node over the quoted children; `exprSize` of the lift head
`appE` strictly exceeds the first operand's size + 1 (`appE` has the `Signal.ap` application spine above `a`).
Proved with `quote`'s defining equations (`ShippingUnifiedSource.lean:370`); the `bitsNum`/`setw`/… arms use the
constructors' `*E` builders. **This lemma is the one whose bound is easiest to get wrong** (any constructor whose
quotation has no node above its child breaks the induction); it is the first item the check file tests with a
concrete instance (see §4 REACH note).

Monotonicity, stated in the form that the coverage goal needs:

```lean
/-- U2a: monotonicity ON QUOTATIONS (a corollary of U1 + soundness; no `goWith` monotonicity needed). -/
theorem readN_mono_on_quotes {cfg : Cfg} (hs : cfg.Sound) (hc : Complete cfg) {s : SType} (t : Term s)
    (hw : t.WF cfg.kb cfg.kv cfg.vw) {k : Nat} (r : AnyTerm)
    (hr : readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some r)
    {k' : Nat} (hk' : liftDepth t ≤ k') :
    readN cfg k' (quote cfg.dom cfg.bools cfg.bits t) = some r
```
Proof: `readN_sound` gives `quote r.2 = quote t`, `r.2.WF …`; `quote_injective` gives `r = ⟨s,t⟩`;
`readN_quote` gives the right-hand side. Note this proves the weaker, quotation-only statement. The header's
`readN cfg k e = some r → readN cfg (k+1) e = some r` for **arbitrary** `e` (`ShippingReaderApp.lean:48-51`) is
**not** adopted: it needs a monotonicity lemma for `goWith`, and DG-COVER only uses the quotation case. If the
reviewer wants the general form it is a separate unit (U2b, not planned).

### 2.3 U3 — `readN` forms of the machine body lemmas

```lean
theorem machine_body_of_readN (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)) :
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

theorem machine_wf_of_readN (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)) :
    d.packed.WF d.kb d.kv d.vw
```
Proof: copy of the two `readTerm` lemmas with `readN_reads` / `readN_sound` for `readTerm_kinds_sound`; the generic
`readTerm_kinds_sound` is replaced by `readN_sound (kindsCfg …) (kindsCfg_sound d.dom isDom hdom (kindsOf d))`
(`kindsCfg_sound` is used at `ShippingReaderApp.lean:360`, so `isDom` generic needs its generic form; whichever
exported form exists is used). The `readTot` form (`k := exprSize d.shape.body`) is the same statement with
`readTot` in place of `readN … k`.

### 2.4 U4 — the converse (a quotation is read; this is the part DG-COVER consumes) (rev2: full types)

Setting: `d : MachineData`, `ks := kindsOf d` (`ShippingReaderMachine.lean:38`), `cfg := kindsCfg d.dom isDom ks`
(`ShippingReaderInputs.lean:277`: `cfg.dom = d.dom`, `cfg.bools j = inputExpr ks.length ((posB 0 ks).getD j 0)`,
`cfg.bits j = inputExpr ks.length ((posV 0 ks).getD j 0)`, `cfg.kb = (posB 0 ks).length`, `cfg.kv = (posV 0 ks).length`,
`cfg.vw j = (widV ks).getD j 0`). `MachineData` projections: `d.kb = d.bposL.length`, `d.kv = d.vposL.length`,
`d.bpos j = d.bposL.getD j 0`, `d.vpos j = d.vposL.getD j 0`, `d.vw j = d.vwL.getD j 0` (`ShippingMachineAuto.lean:198-202`).

```lean
/-- U4a: the argument functions of `cfg` are the ones `machine_body_of_read` quotes with (a rewrite along `hb`, `hv`
    and `kindsOf_length`; stated so the body equation can be turned into a statement about `cfg`). -/
theorem kindsCfg_quote_args (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) :
    (kindsCfg d.dom isDom (kindsOf d)).bools = (fun j => inputExpr d.shape.binders.length (d.bpos j)) ∧
    (kindsCfg d.dom isDom (kindsOf d)).bits  = (fun j => inputExpr d.shape.binders.length (d.vpos j))

/-- U4b: the width / count transport (the widths function lives here: `hw`). -/
theorem packed_wf_cfg (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hwf : d.packed.WF d.kb d.kv d.vw) :
    d.packed.WF (kindsCfg d.dom isDom (kindsOf d)).kb (kindsCfg d.dom isDom (kindsOf d)).kv
      (kindsCfg d.dom isDom (kindsOf d)).vw

/-- U4: a body that IS the quotation of `d.packed` is read, at the level taken from the expression. -/
theorem readTot_of_quote_body (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : isDom d.dom = true)
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hwf : d.packed.WF d.kb d.kv d.vw) :
    readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)
```
Proof route (not tested): `Complete cfg` from `kindsCfg_complete' d.dom isDom hdom (kindsOf d)`; `hq` rewritten with U4a to
`d.shape.body = quote cfg.dom cfg.bools cfg.bits d.packed`; `hwf` to the `cfg` form with U4b; then `readTot_quote`.

* `hdom : isDom d.dom = true` (completeness: the test accepts the domain) is **a different premise** from U3's
  `hdom : ∀ x, isDom x = true → x = d.dom` (soundness: the test accepts nothing else). Both appear, each in its lemma;
  with `isDom := isExpr d.dom` both hold (`isExpr_self` for the first; the second is the existing soundness premise
  discharge in `ShippingReaderApp.lean:360`'s neighbourhood; located when written).
* **`hw` of U3 vs U4.** U3 `machine_wf_of_readN`: `hw : d.vwL = widV (kindsOf d)` takes `WF` over `cfg` (from the reader's
  soundness) to `d.packed.WF d.kb d.kv d.vw`. U4/U4b: the same list equation takes `d.packed.WF d.kb d.kv d.vw`
  (`hwf`) to `WF` over `cfg` (the premise of `readTot_quote`). Same equation, opposite directions, two lemmas: the
  width function `d.vw` is moved to `cfg.vw = fun j => (widV (kindsOf d)).getD j 0` only through this `hw`.
* `hq` is a premise. Nothing in §2 proves `hq` for a body produced by a run (§3).

### 2.5 U5 — `rootFloat` / `packTupleInputs` / `zetaAll` (rev2: provenance corrected)

No lemma planned that unfolds these `partial def`s (no equation lemma exists for a `partial def`; boundary O2,
`docs/parallel/R-reader-fuel.md:43-48, :552-555` per the M5 study — not re-read here).

**What this survey read about where the values come from (read-only; "no source found" ≠ "none exists").**
* `RunReadsAt` (`Tools/ShippingGen5RunReads.lean:42-73`) has: `run` (`synthesizeCombinationalCore X`), `chain`
  (`coreHead`, `getConstInfo`, two `getEnv`, `synthesizeMachineCertified … shape`, profile log, cache modify,
  `coreFinally`), `gates` and `shapeEq : machineShape? … = some shape`. It does **not** contain an execution of
  `Tools.ShippingMachineCommand.readMachine` (`MetaM Read`, `ShippingMachineCommand.lean:440`). The callers of
  `readMachine` found by grep are generator / test / sweep commands (e.g. `ShippingEntryOkCommand.lean:88`,
  `ShippingGateChildCommand.lean:193`, `ShippingMachineComposeRCommand.lean:58`), none in the compiler core or in
  `RunReadsAt`. So the rev1 sentence "the run already performed the production reads, `readMachine` computes
  `RootFacts`" described the generated-command side and is **not established** for a `RunReadsAt` run; withdrawn.
* The compiler core's `machineShape?` calls `packTupleInputs` (`Elab.lean:5078`) and `rootFloat` (`Elab.lean:5088`),
  but the latter inside `machLoopAsLet (rootFloat (zeroLit … (inlFoldNat (machNorm senv e))))`, i.e. on a different
  argument from `readMachine`'s `rootFloat entryBody` (`ShippingMachineCommand.lean:463-467`). `machineShape?_decomp`
  (`Tools/ShippingShapeDecomp.lean`, field `peel`) yields from `shapeEq` the `packTupleInputs`/`mixedGatePeel` half
  with its `(bs, e)` bound (build status of that file: not checked here); it does not yield `readMachine`'s `float`
  equation. This survey found no lemma relating the two compositions.
* A value equation (`entryBody = rootFloat entryBody₀`) is an equation of two `Expr` values. It does not say the
  floated body is semantically the original, nor that it is a quotation (that is §3): meaning preservation and
  quotation are **not supplied** by value equations.

**`RootFacts`, every variable bound (rev2).**
```lean
structure RootFacts (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder))
    (entryBody₀ entryBody : Lean.Expr) : Prop where
  pack  : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)
  float : entryBody = Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀
```
No claim relates `entryBody₀`, `entryBody` to `entryV` beyond these two equations; no `List …` placeholder remains.
The `bsIn` type is that of `ShapeDecomp.bs` (`List (Name × MixedGateBinder)`).

**Which producer would be needed.** For `RootFacts` at the `entryV`/`entryBody` that `readMachine` computes, the evidence
must come from an *execution of `readMachine`* (a `RunsTo (readMachine X) …` on a world that is tied to the same
`ci`/`envR` as the `RunReadsAt` run), or from a stated link between `readMachine`'s `entryBody` and the `entryBody`
that the compiler core used inside `machineShape?`. Neither is supplied on the present path. Routes that this
survey sees, none adopted and each outside this Issue's authority or still open:
* P1 add a `readMachine` run to the evidence (an edit or extension of `RunReadsAt`, a DG-RUNREADS-approved shared def);
* P2 `RootFacts` as a named premise of DG-COVER (conditional → recorded as intermediate);
* P3 derive the `peel` half from `shapeEq` through `machineShape?_decomp`, and state the `float` half on the
  compiler's own composition (a new fact about a `partial` composition, same position as R3 below).
Q2 stays **not adopted** until the reviewer decides on a producer. DG-READKINDS U1-U4 do not depend on U5.

**(b) total fuel versions** `rootFloatT (fuel : Nat)`, `packTupleInputsT (fuel : Nat)` defined in the new file, with
validated agreement on fixed instances only (`decide`/`rfl` on closed `Expr`s). **For agreement on all inputs this
survey found no route under the present boundary** (no equation lemma for the `partial` originals, no agreement lemma
exported); it is **not supplied**, and this document does not claim it impossible or that it would necessarily be a
new TRUSTED boundary — that classification is not decided here (see §6 B2). (b) as a checked artefact is as strong as the
instances tested.

---

## 3. Body-is-quotation (separate; the reason this Issue cannot be closed by U1-U4 alone)

Production: `readMachine` computes `q := quote … packed` and throws unless `q.equal shape.body`
(`ShippingMachineCommand.lean:529-534`). `Expr.equal` is `opaque` in core (`Tools/ShippingCacheSoundness.lean:26` and
`Tools/ShippingInlTypeFacts.lean:19` record the same: nothing reduces it). So for a body produced by an arbitrary
successful run the proof side has, from the existing exports, **no source of `body = quote … packed`**;
per declaration the endpoint gives `f.machine_body` by `Eq.refl` (`ShippingNoPortsCommand.lean:127`,
`ShippingSatCert2Command.lean:46-52`).

Consequences, stated without a conclusion about possibility:
* U4 (`readTot_of_quote_body`) is stated **with `hq` as a premise**. Nothing in §2 proves `hq` for an arbitrary run.
* DG-COVER, as written in DGEN_FREEZE row DG-COVER, "includes body-is-quotation (§2.4 R5)". With U1-U4 the remaining
  statement of that row is exactly: *for every body occurring in a successful machine-route run there exist `t`
  with `body = quote … t`.*
* **This survey found no supply and no route for that statement** inside the present boundary (no `Expr.equal` law,
  no run-linked `unq` equation since `unq` is `partial`). Possibilities to examine in the review, each of which would
  change something outside this Issue's authority: B1 a law linking `Expr.equal` to `=` (new TRUSTED/law), B3 making
  the evidence a premise of the coverage theorem (a conditional result, to be recorded as intermediate), B4 deriving
  it from a total replacement of `unq` plus an agreement lemma (needs agreement with a `partial` def; this survey found
  no route to that agreement under the present boundary — not supplied, not claimed impossible). They are in §6, not adopted.

---

## 4. Expected-type / closure / axiom audit plan

New file `Tests/Gen5/ReadKindsCheck.lean`, in the form of `RunReadsCheck.lean` / `T1NDCheck.lean` (imports
`Tools.ShippingGen5ReadKinds`, `Tests.Gen3.ExpectedType`; `set_option autoImplicit false`; header with
`-- Built in <job> (...)` comment filled in only after a build, as in the existing checks).

1. **TYPE.** Each lemma of §2 against an independently written `Exp…` statement (`def ExpReadNQuote : Prop := …`),
   compared with `isDefEq` on the fully bound, universe-instantiated type (`Tests.Gen3.ExpectedType` helpers as in
   `RunReadsCheck`). One `Exp` per: `readN_quote`, `readAp_appBool_eval`, `readAp_appBool2_eval`,
   `readAp_appCompare_eval`, `readN_expr_quote`, `quote_injective`, `readTot_quote`, `readN_mono_on_quotes`,
   `machine_body_of_readN`, `machine_wf_of_readN`, `kindsCfg_quote_args`, `packed_wf_cfg`, `readTot_of_quote_body`, and
   `RootFacts` (its fields against an independently written structure).
2. **MUTANT** (signature / defeq rejections, **not** semantic counterexamples), each a changed `Exp` that the same
   comparison must reject: `readN_quote` with `liftDepth t ≤ k` replaced by `True` (no level bound);
   with `liftDepth t < k`; `readN_quote` stated for `readTerm2` (level dropped); `quote_injective` without
   `hw'`; `readN_mono_on_quotes` with `readN cfg k` read at `k' < k`;
   `machine_body_of_readN` with `readTerm` in place of `readN`; `readTot_of_quote_body` without `hq`
   (i.e. claiming the coverage statement, which §3 says is unsupplied); `readTot_of_quote_body` / `packed_wf_cfg` without `hw`
   (width function not transported); `readTot_of_quote_body` with U3's `hdom` form in place of `isDom d.dom = true`;
   `RootFacts` with `float : entryBody = rootFloat entryV` (wrong argument).
3. **REACH** (full reachable closure over explicit bodies, `Rule`-based as in `T1NDCheck.lean` §5 `reach`/`badConst`/
   `badProj`):
   * must reach: `readN_reads` (via soundness for the U3 lemmas), `readTerm2_quote` (for `k = 0`) or the restated
     node-eval lemmas, `kindsCfg_complete'`.
   * must NOT reach (three-rule closure with controls as in `RunReadsCheck`): any `T1Hyp`/`T1HypND` field
     (projection, raw `.proj`, recursor), `Tools.ShippingGen2.T1Hyp.dec`, anything in `Laws`, any declaration whose
     body contains `Lean.Expr.equal` / `Lean.Expr.eqv` as a hypothesis-free use. Controls: a fixture reaching
     `T1Hyp.dec`; a fixture reaching `T1HypND.casesOn`; a fixture using `Expr.equal` (unit); an unrelated theorem
     (not flagged).
   * `readN_expr_quote`: positive reach on `kindsCfg_complete'` and `readN_quote`.
4. **AXIOMS.** `#print axioms` equivalent through `collectAxioms` on every lemma of §2: only `propext`,
   `Classical.choice`, `Quot.sound` (the three standard ones). No `sorryAx`, no `Lean.ofReduceBool`
   (native_decide), no other axiom.
5. **Concrete instances** (not a substitute for the theorems): at the three lifts and the nested forms of
   `ReaderAppTest.lean` (`t1`..`t4`, depth up to 2), `readTot cfg (quote … t) = some ⟨_, t⟩` by `rfl`/`decide` on the
   closed `Expr`, as positive controls of `liftDepth_le_exprSize`; one negative control that `readN cfg 0` returns
   `none` on `t1` (the kernel-checked version of the `ReaderAppTest` output).
6. Build discipline: one `kjob lake build` target at a time; the logs stay out of the source tree; the success SHA is
   written into the check file's header in a separate comment-only commit.

---

## 5. Implementation order (after approval)

| step | content | est. lines |
|---|---|---|
| 0 | `kjob lake build Tools.ShippingReaderApp` as-is; record result (the header says "UNVERIFIED, not built") | 0 |
| 1 | `liftDepth`, `exprSize`, `core2_of_liftDepth_zero`; `*Op?_self`, `bitVecE?` lemmas; `readAp_*_eval` (3) | 150-250 |
| 2 | `readNode2_ap_none`; `readN_succ_app3..6`; the eleven kinds' arms (extracted from `readTerm2_quote`, or the recursion redone; Q1) | 200-500 |
| 3 | `readN_quote`, `readN_expr_quote`, `quote_injective` | 150-300 |
| 4 | `liftDepth_le_exprSize`, `readTot_quote`, `readN_mono_on_quotes` | 80-150 |
| 5 | `machine_body_of_readN`, `machine_wf_of_readN`, `readTot_of_quote_body` | 60-120 |
| 6 | `ReadKindsCheck.lean`, `ReadKindsCheck` lakefile target | 250-400 |

Sum in the 500-1200 range of the DGEN unit row (an estimate, not a result).
Risks recorded: (R-a) `readNode2` might accept a `Signal.ap` shape and so make `readNode2_ap_none` false; then
U1 changes to `alt`-order reasoning (still within the new file). (R-b) the eleven first kinds' proofs are inline in
`readTerm2_quote`; if extracting them is heavy, the fallback is to prove U1 by re-doing that recursion for
`readN` with the node case split on the constructor (the same size as `readTerm2_quote`, ~110 lines).
(R-c) `ShippingReaderApp.lean` is documented as unbuilt; step 0 may find errors in that file. Fixing it
is within scope only if the fix is in `ShippingReaderApp.lean`'s own proofs (which is not a forbidden file); any
change to the *definitions* `readN`/`readNode3` would change what the soundness theorems cover and would be
brought back to the reviewer first.

---

## 6. Where a new TRUSTED / law / compiler change would be needed (not adopted, not requested)

| id | what | why it comes up | stated status |
|---|---|---|---|
| B1 | `Expr.equal a b = true → a = b` (or a law on the extern) | body-is-quotation from `q.equal shape.body` (§3) | new TRUSTED/law; **not proposed**. `Tools/ShippingCacheSoundness.lean:26-101` records that nothing reduces `Expr.equal` |
| B2 | agreement of total `rootFloatT`/`packTupleInputsT` (or a total `unqT`) with the `partial` originals | U5(b), §3 B4 | not supplied: this survey found no route to agreement with the `partial` defs under the present boundary (no equation lemma for a `partial def`). Whether a route needs a new TRUSTED boundary is **undecided here** (the O1/O2 choice of `docs/parallel/R-reader-fuel.md`, the DGEN D2 decision, **not re-opened**) |
| B3 | coverage theorem takes `hq` (body-is-quotation) as a premise | §3 | conditional result; if chosen, recorded as an intermediate result, not as completion of DG-COVER |
| B4 | compiler change: have `readMachine` return the evidence (a checked certificate `body = quote …` as a term) rather than an `Expr.equal` Boolean | removes the dependence on the extern | compiler edit (`Elab*.lean` / `ShippingMachineCommand.lean`), forbidden for this Issue |

None of B1-B4 is needed to implement §2 (U1-U4 are conditional only on the premise `hq` of U4, and that is stated
as a premise). Whether to choose one of them for DG-COVER is a user decision (new law / compiler change), to be
prepared as a separate decision document if the reviewer agrees that the DG-READKINDS acceptance depends on it.

---

## 7. Review questions

* **Q1 (U1a').** Extract the eleven kinds' inline arms of `readTerm2_quote` into reader-generic lemmas (default), or
  redo the `readTerm2_quote` recursion for `readN` in the new file (same size, no change to built files)?
* **Q2 (U5).** rev2: not adopted. Open: which producer for `RootFacts` (P1/P2/P3 in §2.5), or (b) fuel versions with instance validation only.
* **Q3 (U2a).** Is the quotation-only monotonicity enough, or is the general `readN k e = some r → readN (k+1) e = some r`
  required? (default: quotation-only; the general form is U2b, not planned.)
* **Q4 (acceptance).** The Issue goal reads "conditional results recorded as intermediate". With §3, U1-U4 are
  complete only up to `hq`. Is the acceptance "U1-U4 + checks, DG-COVER's body-is-quotation recorded as the §3 / B1-B4
  open item", or must B1-B4 be resolved first?

---

## 8. Not claimed
* Nothing in this document is built, elaborated or proved. Line counts are estimates.
* No claim that `ShippingReaderApp.lean` builds (step 0 decides).
* No claim that `readN` is complete on the lifts (U1 is a target), that `readNode2` is `none` on every `Signal.ap`
  node (U1b is a target), or that `liftDepth ≤ exprSize ∘ quote` (U2 is a target).
* No claim that a body produced by an arbitrary successful run is a quotation (§3); no claim that it is not.
* No claim that `RootFacts` is supplied by `RunReadsAt` (it is not on the present path, §2.5); no claim about agreement of any total version with the `partial` defs, either way.
* No claim about `rootFloat` / `packTupleInputs` / `zetaAll` beyond their file:line and their treatment in
  `ShippingGen3ArgSupply3.lean`.

---

## 9. Q2 read-only note (added with the implementation; does not change §2 and is not a freeze change)

Source read on this branch (no run, no build): `Tools/ShippingMachineCommand.lean:440-467` (`readMachine`) and
`Sparkle/Compiler/Elab.lean:5072-5095` (`machineShape?`).

* `readMachine` computes `mixedGatePeel (packTupleInputs entryV)` and then `rootFloat entryBody` on that peeled body,
  **without** `machNorm` / `inlFoldNat` / `zeroLit` in between.
* `machineShape?` computes `mixedGatePeel (packTupleInputs d.value)` (same `peel` half) and then
  `machLoopAsLet (rootFloat (zeroLit … (inlFoldNat (machNorm senv e))))`, i.e. `rootFloat` is applied to the **normalised**
  body, and `machLoopAsLet` follows. `shape.body` is read from that composition.
* So the two compositions share the `packTupleInputs`/`mixedGatePeel` half and differ in the argument of `rootFloat`
  (`entryBody` vs. `zeroLit … (inlFoldNat (machNorm senv e))`). This survey found no lemma relating them; the `float`
  half of `RootFacts` at `readMachine`'s `entryBody` is therefore **not supplied** by `machineShape?` either.
  This is a statement about this survey, not an impossibility claim. P1/P2/P3 stay not adopted; nothing in
  `Tools/ShippingGen5ReadKinds.lean` depends on this note.

---

## 10. Freeze → implementation differences (recorded with `Tests/Gen5/ReadKindsCheck.lean`)

Statement of scope: U1-U4 are intermediate results (approval 3f79600f). `hq` (body-is-quotation), RootFacts supply,
normalization/production coverage stay OPEN. The check below is signature/defeq comparison and a closure scan, not a semantic proof.

**Names / types.** All U1-U4 public theorems of §2 exist in `Tools/ShippingGen5ReadKinds.lean` under the §2 names with the
§2 types: `readN_quote`, `readAp_appBool_eval`, `readAp_appBool2_eval`, `readAp_appCompare_eval`, `readNode2_ap_none`,
`liftDepth_le_exprSize`, `readN_expr_quote`, `quote_injective`, `readTot_quote`, `readN_mono_on_quotes`,
`machine_body_of_readN`, `machine_wf_of_readN`, `kindsCfg_quote_args`, `packed_wf_cfg`, `readTot_of_quote_body`.
Auxiliary (not in §2 as separate lemmas): `core2_of_liftDepth_zero`, `boolOp?_self`, `bool2Op?_self`, `cmpOp?_self`,
`readN_succ_app3..6`, `rn3..rn6`, `rnAp`, `readNode2_app3..6`, `read*_head`. `liftDepth`, `exprSize`, `readTot` are definitions
(`readTot cfg e := readN cfg (exprSize e) e`). `RootFacts` is a type only (U5), not a producer.

**TYPE check.** Each Expected statement (`Exp…` in the check file) is written separately, using the implementation's binder
names and binder infos, because the shared comparison (`Tests.Gen3.ExpectedType.cmpTele`) requires equal names. Result:
all 15 comparisons accepted **syntactically** (no `GEN3 NOTE` / `GEN3 DEFEQ` lines were logged; `isDefEq` fallback never used).
`RootFacts` is compared by constructor telescope (names, order, binder info, types at reducible transparency, no extra field).

**MUTANTS (12 theorem-level + 1 structure).** Each keeps all binder names/infos and changes one point; all are rejected by
signature/defeq comparison (not semantic counterexamples; an elaboration failure would not count and none occurred):
`MutQuoteNoBound`, `MutQuoteStrict`, `MutQuoteTerm2` (readTerm2, level kept), `MutApNonePure` (head `Signal.pure`),
`MutInjNoWf`, `MutMonoLower` (`k' < k`), `MutBodyReadTerm` (readTerm for readN), `MutReadTotNoHq` (hq := True),
`MutReadTotNoHw` (hw := True), `MutPackedWfNoHw`, `MutReadTotSoundDom` (U3's hdom in U4), `MutWfNCompleteDom` (U4's hdom in U3),
and `MutRootFactsArg` (`rootFloat entryV` instead of `entryBody₀`; rejected at field `float`).
Differences from the §-plan: mutants of earlier plan with unnamed binders were redone with matching names so the rejection is
at the changed point.

**AXIOMS.** The 15 public theorems and 4 auxiliary table lemmas: only `propext`, `Classical.choice`, `Quot.sound` (subsets);
no `sorryAx`, no `native_decide`.

**CLOSURE.** The scan reads `thmInfo`/`defnInfo`/`opaqueInfo` values (and types), transitively, with raw `.proj` checks on
`T1Hyp`/`T1HypND`/`Laws` and a forbidden-constant list (`T1Hyp`/`T1HypND` fields/recursors, `Laws`, `Lean.Expr.equal`,
`Lean.Expr.eqv`). Constants without a value (inductives, constructors, recursors, axioms, quot) are **only counted** (the log
prints a count, not their names; the names are held in `noBodyNames` but not printed); opaque constants are listed (`String.Internal.append`, value read); unknown constants fail the check. Controls: three direct
fixtures, two via a helper in ANOTHER namespace (`ReadKindsFixtureOther.viaHelper`, `viaHelper2`) are detected; the unrelated
theorem and an other-namespace clean helper are not flagged. Positive reach: each root reaches its required lemmas
(8 REACH roots in the check: `readN_quote`, `readN_expr_quote`, `quote_injective`, `readTot_quote`, `readN_mono_on_quotes`, `machine_body_of_readN`, `machine_wf_of_readN`, `readTot_of_quote_body`; an earlier note that said 18 was wrong. E.g. `readN_quote` → `readTerm2_quote`, `readAp_*_eval`, `readNode2_ap_none`; the U3 lemmas → `readN_sound`, `kindsCfg_sound`;
`readTot_of_quote_body` → `kindsCfg_complete'`, `readTot_quote`, `packed_wf_cfg`, `kindsCfg_quote_args`).
Not covered: the detector reads Lean kernel terms only; it says nothing about `Classical` use being semantically irrelevant.

**Warning.** `boolOp?_self` (`:125`): unused simp arguments `Lean.mkApp6/5/3` removed; the proof is otherwise unchanged. The same linter
still warns at other lines (130, 135, 168, 565-627); left as they are.

**Build record (sync).** Clean issue-linked build `rkav-4d5b7874` (tree 4d5b7874) exit 0, 751 jobs. The R1/R2 audit-fix commits (single-constant forbid controls `RK CONTROL-SINGLE` for `badDec`→`T1Hyp.dec`, `badNDCases`→`T1HypND.casesOn`, `badEqual`→`Lean.Expr.equal`, each with raw-proj off and a one-element forbid set) were built in the pod (`kjob lake build Tests.Gen5.ReadKindsCheck` exit 0, 751 jobs, tree 40aa86f0); their clean build is the coder's. Signature/defeq rejections remain non-semantic.
