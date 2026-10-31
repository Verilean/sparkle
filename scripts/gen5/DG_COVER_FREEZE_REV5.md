# DG-COVER freeze rev5 — supply-connection survey of the open rows of rev4 §4, and the first unit U-E1 (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — docs only. No Lean file was edited or elaborated for this document; the Lean text of §3 is an unelaborated proposal, written against definitions read in this tree.**
Base `72752f4c` (kjob/g5cv-r7, Cover3 U-D1/U-D2/U-D3 scoped approved as a *conditional intermediate result*), branch `kjob/g5cv-r8`. This is the "next unit" freeze of the
supply connection (rev4 §4 and `DG_COVER_IMPL_REV4.md` "Still open"). Nothing here completes the Issue, M5 or FG. No guarantee, law, TRUSTED boundary, FG scope or
shared definition is changed or proposed to be changed; `GenWF` is not strengthened; no decision is requested.

Wording rule (as rev0–rev4): "not found" = *this investigation found no supplier or route*, never "impossible / not derivable". A mutant is a rejection of a changed
statement by signature / defeq, not a semantic counterexample. A conditional wrapper is **not** counted as a supply. Conditional results are INTERMEDIATE.

## 0. What was searched (and where the owners' parts live)

Searched: this tree (`Tools/ShippingReaderFuel*.lean`, `ShippingLetsReaderInv*.lean`, `ShippingMachineAuto.lean`, `ShippingGen5Cover*.lean`) and, read-only via `git show`,
the owner branches `kjob/g5rk-r8` (DG-READKINDS, `bb783eda`), `kjob/g5do-r4` (DG-DATAOF, `8b57cc6e`), `kjob/g5sm-p4r` (DG-SEM), `kjob/g5ac-r3` (DG-ACC), `kjob/g2st-r3`
(SRC-ARGW, `ShapeFuelBridge`). **Important for use:** `Tools/ShippingGen5ReadKinds*.lean`, `Tools/ShippingGen5DataOf*.lean` and `Tools/ShippingGen5Acc.lean` do **not** exist in this
branch's tree (base `72752f4c`); a Lean unit of this Issue cannot `import` them without a merge (forbidden) or a copy (a duplicate implementation, forbidden by the task).
So, in this branch, "supplied by Issue X" means: X has the theorem on its own branch (status in the table), and the row stays open here until X is integrated. Rows whose
supplier is X are **not re-implemented** here. The statuses (review / scoped approved) are those recorded in each Issue's history at the time of writing.

In-tree facts used below (read): `machineShapeF_steps / _lenOk / _decomp` and `shapePost_decomp / shapePost_insts' / shapePost_instOrigins` (`Tools/ShippingReaderFuelShapeR5.lean`),
`machConvF_post / machChainF_post …` and `RdOk`, `LetOk` (`Tools/ShippingLetsReaderInvMain.lean`, `…InvBase.lean`), `MachineData.ok` (`Tools/ShippingMachineAuto.lean:217`).

## 1. Row table (name, complete type, supplier, status)

Legend: **closed here** = every premise is a theorem/definition of this tree or of the Cover3 base; **owner X** = the theorem is on X's branch (not importable here, see §0);
**未供給 / この調査で経路未発見** = no supplier and no route found.

| # | row (rev4 §4 name) | exact name and complete type | supplier | status |
|---|---|---|---|---|
| 1 | **R-trace** (`FReach` ← real reader steps) | would be: `∀ n senv … (h : machineShapeF n sm ps ci senv ai = some (some sp)), ∃ st, FReach nDecl {} st ∧ shapePost … st v = some sp` (shape of the statement not frozen: no supplier) | pieces: `machineShapeF_steps` (in-tree: the phases and states `st0 st1 st` of a fuel-model run); `machConvF_post` & co. (in-tree) give `RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true` only, **conditional on** `RootFloatRange, LiftRange, Inst1Range, SigTyRange senv, BundleIotaRange` (NOT PROVED); twin → real `TwinCoverAt` (OPEN) / `ShapeFuelBridge` | **未供給 / この調査で経路未発見.** What is missing is an invariant for *every* `readF` call that each state change is an `FStep` with its premises (the `InRange` of §2 of rev4, the `a < st.lets.size` of `inst/group`, `rs.length = os.length`); `readF_good` proves only the `LetOk` clause. The twin facts are about the fuel model; the production reader is opaque (`partial def`) |
| 2 | **R-in** (input clause of `InRange` for each pushed let, loose-bvar bound of the entry body) | `∀ i, MentionsPh "_machIn" i v → i < nDecl` for every `v` pushed by `FStep.letv` | none (`LetOk` speaks of `_machLet` only; `PhInRange` has four clauses) | **未供給 / この調査で経路未発見** |
| 3 | **R-nl** `LetsNoLoose st` | `∀ j nm kd v, st.lets[j]? = some (nm,kd,v) → ∀ b, ¬ LooseOcc 0 v b` | none (no lemma about loose bvars of stored let values; `Expr.hasLooseBVars`/`liftLooseBVars` are `extern`, cf. `LiftRange` premise) | **未供給 / この調査で経路未発見** (open in `ShippingLetsReaderInvMain.lean` header) |
| 4 | **R-dom** (`st.dom` in range, equals the R5-R6 composition) | `∀ d, st.dom = some d → PhInRange nDecl st.insts.size st.kinds.size st.lets.size d` | partial: `RdOk` 3rd clause gives `LetOk st.lets.size d = true` (the `_machLet` clause only); the other three clauses and "equals the composition" | **未供給 / この調査で経路未発見** (only the let clause exists, conditional on `PureFacts`) |
| 5 | **B3** memory arg sorts | agreement of an existing let's kind with the kind passed to the memory call | none; SRC-ARGW `MemSrcKinds`/`ReadTyped` unsupplied | **未供給 / この調査で経路未発見** (owner SRC-ARGW, not re-implemented) |
| 6a | **ShapeAgree**, state-side half (`insts`, `origins`, and the sizes `slots`/`lets` of the final state vs the `MachineShape`) | in-tree: `shapePost_insts' : shapePost ai p m st v = some sp → sp.insts = st.insts.toList`, `shapePost_instOrigins : … → sp.instOrigins = st.instOrigins.toList` (`ShippingReaderFuelShapeR5.lean:343,363`); `layout.lets := st.lets.size`, `layout.slots := machSlotFields (… st.kinds …)` are read off `shapePost` (`ShippingReaderFuelShape.lean:153-202`) but have **no named lemma** (`shapePost_decomp` gives `layout.lets = letB.length` with `letB` existential) | fuel-model only (a theorem about `machineShapeF`, not about production `machineShape?`; link = `ShapeFuelBridge`) | **closes with in-tree parts** for the sizes (new small lemma `shapePost_layout_sizes`), but is a statement about the twin; candidate **U-E2** (next unit) |
| 6b | **ShapeAgree**, `d`-side half (`d.shape = sp`, `d.ss.length`, `d.ls.length`, `d.nIn`) | `dataOfFrom_sound`/`dataOfAt_sound : … → d.shape = s ∧ d.ok = true ∧ d.shape.body = quote … ∧ d.initOk (initsOf d) = true` (DG-DATAOF); `d.nIn = (peel).length + shape.insts.length` is inside `dataOfFront` (no projection lemma), `d.ss`/`d.ls` lengths are inside `dataOfTail`/`typedFields` (no projection lemma) | **owner DG-DATAOF** (`kjob/g5do-r4`, review; `dataOf` conditional on `lvl`, helpers as arguments) | `d.shape = s`: supplied there (conditional); `ss/ls` lengths and `nIn`: **この調査で経路未発見** (projection lemmas absent) |
| 7 | **LetQuoteEq** (Q-wit / Q-cmp / Q-snd) | `def LetQuoteEq (d) (st) : Prop` (Cover3) | owner DG-DATAOF D9 / DG-READKINDS U4 / SRC-ARGW / DG-SEM: `dataOfFrom_sound` gives the *whole-body* form `d.shape.body = quote … d.packed`; `readTot_of_quote_body` (READKINDS U4, approved, conditional on `hq`, `hb`, `hv`, `hw`, `hwf`) reads a body that IS the quotation; `genSem_local` (a field of the `K` structure of DG-ACC, `kjob/g5ac-r3`) is a semantic locality fact | **未供給 / この調査で経路未発見** for the per-let projection (relating the reader's stored let value, after `machClose`, to `quote … (d.ls[j]).2`); not re-implemented |
| 8 | `resultRange_final`'s `hv` | `InRange nDecl st1 st1.lets.size v` for the root value `v` returned by `shapeBody` | none: the twin gives `LetOk st'.lets.size r = true` for `r` (`machConvF_post`), the `_machLet` clause only | **未供給 / この調査で経路未発見** |
| 9 | **hb / hv (O10/O11)** | `hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length`, `hv : ∀ j, d.vpos j < …` | **`MachineData.ok`** row 16/17 (`Tools/ShippingMachineAuto.lean:236-240`: `∀ j, j < d.kb → d.K (d.bpos j) = some .bool ∧ d.bpos j < d.nIn + d.ss.length + d.ls.length`, and the `kv` one) — in this tree; `d.ok = true` is delivered by `dataOfFrom_sound` (owner DG-DATAOF, review) | **closes with in-tree parts, relative to `d.ok = true`**, with a `total = 0` case (§3). **Chosen: U-E1** |

Other items of the task text and who owns them (no overlap, nothing re-implemented):
- `RootFactsAt` (U5, `4ac00d24` approved), `readMachine_root` (U6, `36318286` approved as conditional intermediate), `readMachine_fields` / `ReadFields` (U7, type freeze `f02837ed` approved,
  implementation `bb783eda` in review) — DG-READKINDS. They describe the top-level `Read` record that `readMachine` returns (entry body, `nDecl`, `nIn = nDecl + insts.length`,
  binder count, `bposL/vposL/vwL`, `machDom?`). They are **not** statements about the per-step `MachRead` evolution, so they do not supply R-trace/R-in/R-nl/R-dom. The only row they
  touch is the `d`-side of ShapeAgree (`r.nIn = r.nDecl + r.shape.insts.length`, `r.shape.binders.length = r.nIn + slots + lets`) for the `Read` produced by the *real* reader; the `d` of
  `dataOf` is built from a `MachineShape`, not from `Read`, so the identification `r` ↔ `d` is also not supplied (DG-DATAOF/DG-RUNREADS).
- `genSem_local` — a field of `K` in DG-ACC (`Tools/ShippingGen5Acc.lean` on `kjob/g5ac-r3`), about `genSem` under `ordCallees`; not a supplier of any row of this table.
- `ShapeFuelBridge` — one shared Prop, statement `∀ E senv sp, machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)` (`SRC_ARGW_SUPPLY_FREEZE.md` §2); it is the O1/O2 boundary of this Issue (D2(b)), **assumed once, not proved here**. Every twin-side row above (1, 6a, 8, and the `PureFacts` premises) reaches production only through it.
- `dataOf_sound` (DG-DATAOF) — as in 6b.

## 2. Choice of the first unit

**U-E1 = row 9 (`hb`/`hv` from `MachineData.ok`) and the `rowC` corollary without `hb`/`hv`.** Reasons:
1. Every ingredient is in this tree (`MachineData.ok`, `MachineData.bpos/vpos/kb/kv`) or in the Cover3 base; no import from an unmerged branch, so the unit can be built and checked here.
2. It removes two premises of the approved `rowC_of_reader` by *derivation*, not by renaming: the premise that remains for them is `d.ok = true`, which is `dataOf`'s own guard (`checked`) and is delivered by DG-DATAOF's `dataOfFrom_sound` — the owner's row, not re-implemented.
3. The other closable row (6a, state-side sizes of the twin) is stated about the fuel model and needs `ShapeFuelBridge` (boundary) to say anything about production, and its `d`-side counterpart (6b) is owned by DG-DATAOF with projection lemmas missing there; it is the better *second* unit (U-E2), after DG-DATAOF integration decides how `d.ss/d.ls/d.nIn` are exposed.
4. Rows 1-5, 7, 8 have no route found in this investigation; they are listed as open, not claimed.

What U-E1 does **not** do: it does not make `FReach` a trace of the real reader, supplies none of rows 1-8, and does not claim `d.ok = true` for any run.

## 3. U-E1 — full types (new files; unelaborated proposal)

New files: `Tools/ShippingGen5Cover4.lean` (imports `Tools.ShippingGen5Cover3`, `Tools.ShippingMachineAuto`; `namespace Tools.ShippingGen5Cover4`; `set_option autoImplicit false`),
`Tests/Gen5/Cover4Check.lean`; `lakefile.lean`: two `lean_lib` additions. Opens as in Cover3: `Lean Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Cover3 Tools.ShippingGen5Sem`.
No edit of the compiler, `ShippingGen2Defs`, `T1Hyp`, `T1HypND`, `Elab*.lean`, Cover/Cover2/Cover3, `ShippingMachineAuto`.

```lean
/-- O10: every Bool-binder position of `d` is below the total binder count of `rowC_of_reader`'s `hb`; `hpos` covers `j ≥ d.kb` where `bpos j` is the default `0`. -/
theorem bpos_lt_of_ok {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length) :
    ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length

/-- O11, for the BitVec positions. -/
theorem vpos_lt_of_ok {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length) :
    ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length

/-- `rowC_of_reader` with `hb`/`hv` discharged from `d.ok`: when the total is `0`, `ShapeAgree.nIn` gives `d.shape.insts.length = 0`, so the statement is vacuous. -/
theorem rowC_of_reader_ok {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hq : LetQuoteEq d st) (hnl : LetsNoLoose st) (hok : d.ok = true) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true
```
Proof plan. `unfold MachineData.ok at hok; simp only [Bool.and_eq_true] at hok`; row 16 is `hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1` (15 `.2` then `.1`) and row 17 `…2.1` (positions counted in the `&&` chain of `ok`; the
check compares against an independently spelled statement, so a miscount fails the build, not silently). `bpos_lt_of_ok`: `by_cases hj : j < d.kb`; then row 16 (`of_decide_eq_true`) gives the bound;
else `d.bpos j = d.bposL.getD j 0 = 0` (`List.getD_eq_default`, `kb = bposL.length`) and `hpos`. Same for `vpos`/`kv`/`vposL`. `rowC_of_reader_ok`: `by_cases h0 : d.nIn + d.ss.length + d.ls.length = 0`;
in the `0` case `k < d.shape.insts.length ≤ d.nIn ≤ 0` (`hag.nIn`) is absurd; otherwise `rowC_of_reader hag hi hq hnl (bpos_lt_of_ok hok h) (vpos_lt_of_ok hok h)`.

## 4. Checks planned for `Tests/Gen5/Cover4Check.lean` (form of `Cover3Check.lean`; the numbers will be reported as real counts with category and aggregation rule: one compared declaration = 1)

- **TYPE**: the three theorems against `Exp…` statements written from §3 **independently of the Tools file** (own spelling of `bpos`-bound, `ok`-row text not shared), by the same reducible comparer `checkExpected` (`Tests.Gen3.ExpectedType`) with positive control(s).
- **MUTANT** (signature/defeq rejection, **not** semantic counterexamples), each well-typed and rejected by the same comparer: `bpos_lt_of_ok` with `≤` for `<`; `bpos_lt_of_ok` without `hpos`; `rowC_of_reader_ok` without `hok`.
- **AXIOMS**: `collectAxioms` per theorem, standard axioms only. **CLOSURE**: value-closure walk over `getUsedConstants` as in Cover3Check, unknown names `throwError`, same 3 negative / 2 clean controls and the unknown-name controls (the intended `sorry` negatives are built in memory inside `withoutModifyingEnv`; the build prints N "declaration uses `sorry`" warnings, N = the count observed in the Pod, stated in the header). Source contains no `sorry`, axiom or `native_decide`.
- **Row-position check**: a reducible `rfl`/`decide`-style comparison that the two `MachineData.ok` rows used are the `kb`/`kv` rows of the unfolded `ok` (so a change of `ok` breaks the build).
- Build: `kjob lake build Tools.ShippingGen5Cover4`, then `Tests.Gen5.Cover4Check`, one at a time in the Pod, logs outside the tree; success SHA recorded by a comment-only commit. The Lean commit is left at `doing` with "clean build は coder".

## 5. Not claimed

- Rows 1-5, 7, 8 are open (未供給 / この調査で経路未発見); `FReach` is a closure of abstract steps, not a trace of the real reader; `FullInv` says nothing until R-trace is supplied.
- `d.ok = true` is a premise of U-E1 (delivered by DG-DATAOF's conditional `dataOfFrom_sound`); no successful run, `dataOf` success, `GenWF` on real data, corpus, M5 or FG statement is made.
- Twin-side statements (rows 1, 6a, 8) are about the fuel model; production only through `ShapeFuelBridge`, which is assumed once and not proved.
- No new law, TRUSTED boundary, FG/guarantee change, compiler change or shared-definition change; `GenWF` is not strengthened.
