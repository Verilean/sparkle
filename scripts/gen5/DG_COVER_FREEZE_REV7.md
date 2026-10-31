# DG-COVER freeze rev7 — unit U-E3: R-trace / R-in / R-nl / R-dom over the T3 phase witness (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — docs only. No Lean file was edited or elaborated for this document; the Lean text below is an unelaborated proposal written against definitions read in this tree.**
Base `9b9cdd55` (kjob/g5cv-r11, U-E2 T1-T6 scoped approved), branch `kjob/g5cv-r12`. Continues `DG_COVER_FREEZE_REV5.md` §1 rows 1-4 and `DG_COVER_FREEZE_REV6.md` §5 (phase trace).
No guarantee, law, TRUSTED boundary, FG scope or shared definition is changed or proposed to be changed; `GenWF` is not strengthened; no decision is requested.

Wording rule (as rev0–rev6): "not found" = *this investigation found no supplier or route*, never "impossible / not derivable". A mutant is a rejection of a changed statement by
signature / defeq, not a semantic counterexample. A conditional wrapper is **not** a supply. Conditional results are INTERMEDIATE.
Rule of use: every later connection is made on the **T3 witness** (`machineShapeF_state_side`: `p en st0 env st1 st v` with the six run equations) together with **T4**. T5/T6 conclude only
`∃ st, st.LenOk ∧ ShapeAgree d st`, which forgets the phase trace; nothing below uses them, and no `st` is identified with any other existential witness.

## 0. What was searched, and what the survey found

Read: `Tools/ShippingGen5Cover3.lean` (`InRange`, `RangeInv`, `FullInv`, `FStep`, `FReach`, `fullInv_reach`, `LetQuoteEq`, `LetsNoLoose`), `Tools/ShippingLetsReaderInv.lean` (`Pre`, `Post`, `Good`, `readF_good`),
`Tools/ShippingLetsReaderInvMain.lean` (`machConvF_post`, `machChainF_post`, the five range premises), `Tools/ShippingReaderFuelDefs.lean` (every state write of the seven `readF` bodies),
`Tools/ShippingReaderFuelShape.lean` (`shapeStart`, `shapeRootLet`, `shapeBody`, `shapeW`, `wtab`), `Tools/ShippingReaderLenOk.lean` (`reserved`).

Findings (S1-S5). Each is "what this investigation found", not a proof that nothing else exists.

* **S1. The existing post-condition of the fuel reader is `Adv`, not a trace.** `Good`/`Post` (`ShippingLetsReaderInv.lean:139-177`) give, for each successful `readF` call, `RdOk st' ∧ st.lets.size ≤ st'.lets.size` (+ `LetOk` of the returned expression).
  No lemma relates a `readF` call to `FStep`/`FReach`. `FReach` is an abstract closure (header of Cover3 says so); R-trace is not a corollary of `readF_good`.
* **S2. `FStep` does not cover every state write of the fuel reader.** `FStep` has constructors for `lets`, `insts`(+`instOrigins`), `kinds`/`inits`/`names` and `ws` only. `readF` also writes `dom` (`ShippingReaderFuelDefs.lean:318, 420, 450, 585`),
  `nested`/`inInner` (`:408`), `loops` (`:586`), `runs` (`reserved`, `ShippingReaderLenOk.lean:176`), often in the same record update as a covered field (e.g. `:317-318` pushes `kinds/inits/names` **and** sets `dom`).
  So the sentence "every reader step is an `FStep`" is **not available as typed**: those updates are not `FStep` results. The fields `dom/nested/loops/inInner/runs` are not read by `CallOrderInv`, `RangeInv`, `OrigAligned`, `EntryKinds`
  (they read `lets, insts, instOrigins, kinds, inits(size via LenOk elsewhere), ws`; `callOrderInv_congr`/`rangeInv_mono_aux` show the congruence). This investigation found no route to R-trace that avoids extending the step relation;
  the extension below (`FReachC`, a `ctrl` step on the non-read fields) is new content in a new file, with `Cover3` untouched.
* **S3. `nDecl` is not a quantity of the fuel run.** `_machIn i` is created only by `convBvar` (`ShippingReaderFuelDefs.lean:255`: `machIn (j - d - env.length)` for a **loose bvar** of the input expression). Hence R-in
  ("every `_machIn i` mentioned by a pushed let has `i < nDecl`") needs: (a) a loose-bvar bound `< d + env.length + nDecl` on the expressions handed to the reader; (b) the same for placeholders already present in `env` values;
  (c) that `rootFloat`/`liftLooseBVars`/`instantiate1`/`bundleIota` and `senv.instS` types keep these bounds. (a) and (b) are input conditions; (c) are the **extern/partial** facts that `machConvF_post` already carries only for `LetOk`
  (`RootFloatRange`, `LiftRange`, `Inst1Range`, `BundleIotaRange`, `SigTyRange` — NOT PROVED). Their placeholder-range/loose-bvar versions do not exist at all. And `nDecl` must be identified with `kDOf d = d.nIn - d.shape.insts.length` (row 6b side).
* **S4. `machReserve` is not a `readF` call but is in-tree and pure.** `shapeStart` runs `machReserve` (state `reserved st dom' body kinds inits` = slot-append + `dom`/`runs` writes). Its trace is closable from in-tree parts
  (`machReserve_eq_spec`, `reserved`) with no range premise on expressions (`kinds`, `inits` lists only), **but the `wConv` of `dom` in `shapeStart` and everything inside `shapeRootLet`/`shapeBody` are `readF` calls** (S1-S3).
* **S5. R-nl (`LetsNoLoose`) and R-dom.** Loose bvars of a stored let value: `machClose_bvar` bounds only the root bvar; `Expr.hasLooseBVars`/`liftLooseBVars` are `extern`; no lemma found (rev5 row 3 unchanged).
  R-dom: `RdOk` third clause gives only the `_machLet` clause of `PhInRange` for `st.dom`; the `_machIn/_machInst/_machSlot` clauses and "equals the R5-R6 composition" have no supplier found (rev5 row 4 unchanged).

## 1. Row status after this survey

| row | status | named premise(s) that remain (all UNPROVED, none an axiom here) | supplier Issue |
|---|---|---|---|
| 1 R-trace | **未供給 / この調査で経路未発見** for `readF` calls. Closable in-tree: the **step relation extension** and the `machReserve` step (U-E3a). | `TraceGood` (below): a per-call joint invariant (new induction over the seven `readF` bodies, mirror of `readF_good`) | none assigned. No existing Issue found whose scope is the reader's range/trace invariant (`dg-readkinds` = top-level `Read` record; `dg-dataof` = `d`; `dg-sem` = `genSem`). Proposal: manager to open an Issue "reader trace invariant TraceGood" (this Issue changes no other Issue) |
| 2 R-in | **未供給 / 経路未発見** | `ShapeInputs nDecl …` (loose-bvar / placeholder input bounds, S3 a,b); `RootFloatPh, LiftPh, Inst1Ph, BundleIotaPh, SigTyPh` (S3 c) | same proposal; `SigTyPh` is an environment condition (`structEnv`) |
| 3 R-nl | **未供給 / 経路未発見** | loose-bvar fact of stored lets; `liftLooseBVars` extern | same proposal |
| 4 R-dom | **未供給 / 経路未発見** (only the `_machLet` clause) | other three `PhInRange` clauses of `st.dom` | same proposal |

Production connection stays through `ShapeFuelBridge` (`hbr`, assumed once, inline as in T6); nothing below mentions production.

## 2. Types (new file `Tools/ShippingGen5Cover6.lean`; unelaborated proposal)

Imports `Tools.ShippingGen5Cover3`, `Tools.ShippingGen5Cover5`, `Tools.ShippingReaderLenOkReserve` (for `machReserve_eq_spec`; whichever are not transitive). `namespace Tools.ShippingGen5Cover6`; `set_option autoImplicit false`;
opens as Cover5 plus `Tools.ShippingGen5Cover5`. New `def`/`inductive` are in this file only; no `axiom`, no shared-definition edit, no `sorry`.

### 2.1 U-E3a — step relation matching the fuel reader's writes (implement first)

```lean
/-- The fields read by `FullInv` are unchanged; every other field of `MachRead` (dom, nested, loops, inInner, runs, …) is free. -/
def CtrlEq (st st' : MachRead) : Prop :=
  st'.lets = st.lets ∧ st'.insts = st.insts ∧ st'.instOrigins = st.instOrigins ∧
  st'.kinds = st.kinds ∧ st'.inits = st.inits ∧ st'.names = st.names ∧ st'.ws = st.ws

inductive FReachC (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : FReachC nDecl st st
  | tail {a b c : MachRead} : FReachC nDecl a b → FStep nDecl b c → FReachC nDecl a c
  | ctrl {a b c : MachRead} : FReachC nDecl a b → CtrlEq b c → FReachC nDecl a c

theorem reachC_of_reach {nDecl : Nat} {a b : MachRead} (h : FReach nDecl a b) : FReachC nDecl a b
theorem reachC_trans {nDecl : Nat} {a b c : MachRead} (h1 : FReachC nDecl a b) (h2 : FReachC nDecl b c) : FReachC nDecl a c
theorem fullInv_reachC {nDecl : Nat} {st0 st : MachRead} (h : FullInv nDecl st0) (hr : FReachC nDecl st0 st) : FullInv nDecl st
theorem reachC_sizes_mono {nDecl : Nat} {a b : MachRead} (hr : FReachC nDecl a b) :
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size
/-- the empty state satisfies `FullInv` (start of the T3 witness's phase 0 for `shapeStart`'s `none` arm). -/
theorem fullInv_empty {nDecl : Nat} : FullInv nDecl ({} : MachRead)
/-- `machReserve` is a slot append plus writes to fields outside `CtrlEq`'s list: premise-free. -/
theorem reserved_reachC {nDecl : Nat} {st : MachRead} {dom' body : Lean.Expr} {kinds : List MixedGateBinder} {inits : List Nat} :
    FReachC nDecl st (reserved st dom' body kinds inits)
```
`reserved_reachC` needs `kinds.length = inits.length`-free form? `FStep.slots` has no length premise (`ks is ns` arbitrary), and the `names` list is `machSlotNames … .toArray`, so no premise. (`names` is within `CtrlEq`'s equal list, but `slots` step changes it; the order is `slots` then `ctrl` on `dom/runs`.)
If `fullInv_empty` already exists under another name in the tree it is not duplicated; the Check reports which.

What U-E3a does **not** do: it does not connect any `readF` call to `FReachC` (S1/S3), supplies no range, and is not an R-trace supply. It makes the closure *able to hold* the real writes (S2) and closes `machReserve` (S4).

### 2.2 U-E3b — the connecting theorem (full type; **not implemented in this unit**, premises named)

Reader-call helpers (new `def`s, pure projections): `Call.st : Call → MachRead` (the input state field of each constructor) and `Call.outSt : (c : Call) → c.Res → MachRead` (the output state of the result).

```lean
/-- Joint trace invariant of a call table: for every call meeting the range input conditions, a successful answer is a closure-reach from the input state, with the range clauses.  UNSUPPLIED. -/
def TracePre  (nDecl : Nat) : Call → Prop      -- Pre c ∧ loose-bvar bound (d + env.length + nDecl) on the input exprs ∧ placeholder-range of env values ∧ placeholder-freeness of input exprs ∧ FullInv nDecl c.st
def TracePost (nDecl : Nat) : (c : Call) → c.Res → Prop   -- Post c v ∧ FReachC nDecl c.st (c.outSt v)
def TraceGood (nDecl : Nat) (h : Hs) : Prop := ∀ c, TracePre nDecl c → ∀ v, h c = some (some v) → TracePost nDecl c v

/-- U-E3b: R-trace over the T3 witness. Premises (all named, none supplied): `TraceGood` for the table `readF senv n`,
the root input condition `ShapeInputs`, and the ph-range versions of the five pure premises. -/
theorem machineShapeF_reach {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hTG : TraceGood nDecl (readF senv n))
    (hIn : ShapeInputs nDecl sm ps ci senv) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      <the thirteen clauses of machineShapeF_state_side, same text> ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧ FullInv nDecl st
```
The conclusion is exactly the thirteen T3 clauses ∧ `FReachC nDecl {} st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧ FullInv nDecl st` (`FullInv` from `fullInv_reachC` + `fullInv_empty`).
The root-value range `hv` of `resultRange_final` (row 8) is `InRange nDecl st1 st1.lets.size v`: it would be a further clause of `TracePost` for `chain`/`conv` (the returned expression); it is **not** part of this type until `TracePost` is fixed with its supplier.
`ShapeInputs nDecl sm ps ci senv` and `TracePre/TracePost` are given only as the comments above in this revision: their precise bodies are fixed **only after U-E3a is built**, in a rev8 addendum together with the supplier decision. U-E3b is therefore *not* proposed for Lean in this unit.

Identification of `nDecl`: a later combination takes `hnD : nDecl = kDOf d` as an explicit premise on the **same** `d` and the **same** T3 witness `sp` (row 6b side: `d.nIn = nDecl + sp.insts.length`; projection lemmas not found). It is never obtained by a conjunction of separate existentials.

## 3. Choice of the first unit, and why

**U-E3a (§2.1).** Reasons: (1) everything it needs is in this tree (`FStep`, `FullInv` congruence lemmas, `reserved`, `machReserve_eq_spec`), no import of an unmerged branch, no premise; (2) S2 shows R-trace cannot even be *stated* as "each step is an `FStep`" without it,
so it is the precondition of any `TraceGood` statement, and fixing it first avoids freezing a `TracePost` that the fuel reader's real writes cannot satisfy; (3) it pins the shape of the premise that U-E3b leaves open, without claiming a supply.
Not chosen: U-E3b (needs the five ph-range premises and a new seven-way mutual induction; supplier Issue not assigned, so its body would be a conditional wrapper on its own conclusion), R-nl/R-dom (no route found, S5).

## 4. Checks planned (`Tests/Gen5/Cover6Check.lean`, form of `Cover5Check.lean`; real counts with category and rule: one compared declaration = 1)

* **TYPE**: the six theorems and the `CtrlEq`/`FReachC` signatures of §2.1 against `Exp…` statements written from §2.1 **independently of the Tools file** (own spelling), by `checkExpected` with positive controls. `def`/`inductive` are compared by a constructor-list/type check, counted separately from theorems.
* **MUTANT** (signature/defeq rejection, **not** semantic counterexamples; well-typed single changes only): `reserved_reachC` with `FReach` for `FReachC` (the weaker closure: type differs); `fullInv_reachC` without `h`; `reachC_sizes_mono` with `<` for `≤` on `kinds`; `reachC_trans` with `a c` swapped for `c a`;
  `CtrlEq` with one conjunct dropped (the `ws` one: statement-level, compared by the same comparer on `def` bodies); a conclusion-conjunct-drop mutant of `reachC_sizes_mono`.
* **AXIOMS**: `collectAxioms` per theorem, standard only. **CLOSURE**: value-closure walk as in Cover5Check with 3 negative / 2 clean controls and the unknown-name controls (unknown names `throwError`); intended `sorry` negatives built in memory inside `withoutModifyingEnv` (warning count N observed in the Pod, stated in the header).
  Source: no `sorry`, axiom, `native_decide`.
* Build: `kjob lake build Tools.ShippingGen5Cover6`, then `Tests.Gen5.Cover6Check`, one at a time, logs outside the tree; success SHA recorded by a comment-only commit; two `lean_lib` additions to `lakefile.lean`. The Lean commit is left `doing` with "clean build は coder".

## 5. Not claimed

* R-trace for `readF` calls, R-in, R-nl, R-dom: **未供給 / この調査で経路未発見**. U-E3a is a step-relation extension and the `machReserve` step; it is not a supply of any of rows 1-4.
* `TraceGood`, `ShapeInputs`, the five ph-range premises, `hnD : nDecl = kDOf d`: unsupplied named premises; no supplier Issue exists yet (proposal in §1, to be made by the manager; this Issue changes no other Issue).
* Row 6b, `ShapeFuelBridge` (`hbr`), `LetQuoteEq`, `LetsNoLoose`, `FullInv` for a real run, `d.ok` for a run, real reader coverage, B3: unchanged from rev5/rev6. Issue/FG not complete.
* No new law, TRUSTED boundary, FG/guarantee change, compiler or shared-definition change; `GenWF` not strengthened.
