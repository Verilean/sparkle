# DG-COVER / DG-WFCOVER / DG-MEASURE — row-by-row supply survey and full-type freeze, rev0 (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — design/survey only. No Lean file, lakefile or shared definition was edited, nothing was elaborated or built by this
document. Every Lean text below is an unelaborated proposal.** Nothing here is a completion of the Issue, of M5 or of FG.

Base: `kjob/g5cv-309a33a9` = `309a33a9` (`kjob/g5sm-u3`: par/gen3-combined 9d26005c line + DG-SEM U3, `Tools/ShippingGen5SemGen.lean`).
`[B]` = this tree (line numbers re-read here). `[D]` = `DGEN_FREEZE.md` (`par/gen5-t2` c398021c; §4 rows DG-COVER/DG-WFCOVER/DG-MEASURE, §5 D2/D3),
`[T]` = `T2COVER_FREEZE.md` (same ref), `[DO]` = `kjob/g5do-r2:scripts/gen5/DG_DATAOF_FREEZE.md` rev1 (8d20ae99), `[RK]` =
`kjob/g5rk-impl:scripts/gen5/DG_READKINDS_FREEZE.md` rev2 (3f79600f; impl 8781ec44), `[AW]` = `scripts/gen3/SRC_ARGW_SUPPLY_FREEZE.md` [B] (rev3),
`[SM]` = `scripts/gen5/DG_SEM_FREEZE_REV3.md` [B].

**Wording rule (kept throughout).** "Not found" means *this survey found no supplier or route*; it is not a claim that none exists or that the row is
false. A "mutant" in §9 is a rejection of a changed statement by signature / defeq, not a semantic counterexample. Conditional results are
INTERMEDIATE and are never written as completion. The corpus census (DG-MEASURE) is evidence only and discharges no row.

---

## 0. What is asked, and what the run gives

**Target (coverage).** For every successful machine-route run (the run object is `RunReadsAt`, `Tools/ShippingGen5RunReads.lean:42-73` [B], produced by
`runReads_of_run` :181 from the run, `MachineDefines` and `MachineClosesAtA`), `dataOf` on the run's entry constant and shape returns `some d`, and
`GenWF d = true`.

**What a `RunReadsAt` run contains (the only facts a coverage proof may start from).**
- `shapeEq : machineShape? false [] E (structEnv envR') = some shape` with `E := entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)`;
- `gates`: both certified gates return `none` at `E`;
- `chain`: the machine synthesis `synthesizeMachineCertified … shape` returned `some (raw, D)` (Elab.lean:5252 [B]): the transition went through
  `synthesizeMixedCertified` without refusal, `closeLets` returned `some`, and `closeInstsM`/`closeInstsGM` returned `some` when `shape.insts ≠ []`;
- it does **not** contain an execution of `readMachine` (`Tools/ShippingMachineCommand.lean:440` [B]); the callers of `readMachine` are generator/test commands
  ([RK] §2.5). So `dataOf` (the pure part of `readMachine`, [DO] §1) is *not* run by production: every `dataOf` success condition must be derived from
  `shapeEq` (+ `chain`), or recorded as unsupplied.
- `envR` and `envR'` are two `getEnv` results; `envR = envR'` is not claimed (header of RunReads.lean). `entryConst` uses `structEnv envR`, `machineShape?` uses
  `structEnv envR'`. `readMachine` uses ONE `senv` for both (:443). **Design point P-ENV:** this document states `dataOf` at `senv := structEnv envR'` (the one
  `shapeEq` is stated at). If DATAOF fixes a single-`senv` signature (`dataOf E senv shape`, [DO] §2.2), the identification of `structEnv envR` with
  `structEnv envR'` on the names used is DG-ENV's (`SigEq`, [AW] §6 Q3); it is not supplied here.

**The reader branches a `shapeEq` run went through** (all [B]):
| id | branch | file:line |
|---|---|---|
| E0 | `entryConst`: original ci, or `inlinedConst inl ci` when a gate/shape accepts the unfolding | Elab.lean:5272-5282 |
| M0 | `machineShape?` `.defnInfo d` guard, `symbolicMode`/`parameters` | Elab.lean:5072-5077 |
| M1 | peel `mixedGatePeel (packTupleInputs d.value) = some (bs, e)` | Elab.lean:5078; `mixedGatePeel` :2345 |
| M2 | outputs `machTupleKinds?`/`machOuts?`; `outs ≠ []`, names `outNameOk`, `Nodup` | Elab.lean:5079-5086 |
| M3 | normalise `e := machLoopAsLet (rootFloat (zeroLit … (inlFoldNat (machNorm senv e))))`, then `machRoot` | Elab.lean:5088-5091 |
| M4 | enclosing run: `machReserve` (slot kinds, reset values `machInits`, names) | Elab.lean:5107-5117; machReserve :3703; machInit? :3453 |
| M5 | root `let`s, `machConv`/`machBindLet*` into `st.lets` | Elab.lean:5118-5134; machBindLet :3619, Named :3640, Alias :3654 |
| M6 | chain/body `machChain`/`machConv` (calls: `machInstance` :4049, `machInstanceS` :4087, memory arm :3954, `machLetIndex` :3743) | Elab.lean:5135-5147 |
| M7 | acceptance rejects: `n = 0 …`, `!allowInsts`, loops | Elab.lean:5150-5159 |
| M8 | domain `st.dom <|> machTypeDom? d.type`, `machDom?` | Elab.lean:5162-5163; machDom? :4269 |
| M9 | fields: `machField dom' kind (machClose kI n k 0 …)` for lets, outputs, slots; `machPack`; `machCanonAp` | Elab.lean:5164-5180; machClose :4255, machField :4298, machPack :4304 |
| M10 | acceptance `unifiedGateRoot (binders.map (·.2)).toArray body` | Elab.lean:5185; unifiedGateRoot :2619 |
| M11 | result record: `binders = bs ++ instBinders ++ names.zip kinds ++ lets`, `layout`, `insts`, `instFields`, `instOrigins` | Elab.lean:5186-5196 |

`readMachine` steps that `dataOf` replays ([B] `ShippingMachineCommand.lean`): R1 :454 `entry.value?`; R2 :456 peel; R3 :459 `rootFloat entryBody`; R4 :465 binder
count; R5 :466 `machRoot senv.proj entryBody []`; R6 :467-503 `srcDom`/`depth`/`machDom?`; R7 :505-514 outputs and kinds; R8 :515 `unq c shape.body` (in `dataOf`:
`readN … (lvl body) body`); R9 :516 result sort bits; R10 :517 `splitLets`; R11 :519 `splitFields`; R12 :525-527 `typed`/`unField` ×3; R13 :529-533 repack and
`q.equal` (in `dataOf`: `bitsBeq`); R14 (no counterpart, `dataOf` guard) `d.ok`.

**Important structural fact (R3 vs M3).** `readMachine` computes `machRoot` on `rootFloat entryBody` of the **un-normalised** peeled body (:459, :466), whereas
`machineShape?` computes it on the **normalised** `machLoopAsLet (rootFloat (zeroLit (inlFoldNat (machNorm senv e))))` (Elab.lean:5088-5091). The domain `dom`
(R6) therefore comes from a different composition than the shape's `st.dom`/`dom'` (M8). This survey found no lemma relating the two compositions ([RK] §2.5:
`RootFacts`; [DO] S-COV-FLOAT). Rows D4/D6 below depend on it.

---

## 1. Row table 1 — success conditions of `dataOf` (DG-COVER proper)

Status codes: **S** supplied by an existing named lemma (build status per §10: header claims are quoted, not re-verified here); **P** a pure lemma writable now
without any dependency (full type in §4); **W(x)** exact proposition waiting on dependency `x` (§5); **U** no supplier or route found by this survey (§6).

| id | success condition (`dataOf` = pure `readMachine`) | reader branch | existing supplier / status |
|---|---|---|---|
| D0 | `E` is `.defnInfo d` (so `E.value?` is `some`, R1) | M0, R1 | from `shapeEq`: `ShapeDecomp.peel` is stated for `.defnInfo d` (`machineShape?_decomp`, ShapeDecomp.lean:71); `reader_defn` (ReaderOutsInv.lean:80) gives `ci = .defnInfo _`. **S** (headers: ShapeDecomp "UNVERIFIED written, not built"; ReaderOutsInv "WRITTEN, NOT BUILT"; see §10) |
| D1 | `mixedGatePeel (packTupleInputs entryV) = some (bsIn, body₀)` (R2) | M1 | `ShapeDecomp.peel` (:61) **S**, same expression |
| D2 | `rootFloat body₀` evaluated as a value (R3) | M3 vs R3 | total-as-value: no obligation beyond D4's relation; opaque `partial` constant; (T-K) only ([DO] §2.4a). No claim of termination of the compiled code |
| D3 | `binders.length == nIn + nSlots + nLets` (R4), `nIn = nDecl + insts.length` | M11 | `ShapeDecomp.binders/slots/lets` (:61-66) + `ShapeDecomp.nDecl` (:150) need R5: `(names.zip kinds).length = sp.layout.slots.length`. `r5_of_lengths` (:143) needs `names.length = kinds.length ∧ inits.length = kinds.length` of the reader state: **W(SRC-ARGW: ShapeFuelBridge)** via `machineShapeF_lenOk` (ShapeR5:416) / `LenOk` (ReaderLenOk.lean:75). Pure part **P** (§4 U-C4) |
| D4 | `machRoot senv.proj entryBody []` ⇒ `(srcDom, depth)`, `srcDom'` not a root-let bvar, `machDom? (kI+nSlots+nLets) srcDom' = some (dom, _)` (R5-R6) | M3, M8 | **U**: relation between R3's composition and M3's (`rootFloat` of the un-normalised vs normalised body). Candidate routes seen but not adopted: [RK] §2.5 P1 (add a `readMachine` run to `RunReadsAt`), P2 (premise), P3 (derive from `machineShape?_decomp.peel` + new fact on a `partial` composition) |
| D5 | outputs: `machTupleKinds? entry.type` / `machOuts? senv entry.type = some (ctor?, outKinds)` (R7) | M2 | `ShapeDecomp.outsEq : declOuts? senv d.type = some (ctor?, outs)` (:62) **S**; `declOuts?` ↔ `machTupleKinds?/machOuts?` unfolding is a small pure lemma **P-candidate** (not typed here: `declOuts?` is in `ShapeDecomp`'s import closure; typed after reading `declOuts?`) |
| D6 | **body is read**: `readN (kindsCfg dom (isExpr dom) kinds) (lvl body) body = some ⟨.bits W, whole⟩` (R8-R9) | M9, M10 | **U** (S-COV-Q): needs "`shape.body` is the quotation of a `Term`"; READKINDS U4 `readTot_of_quote_body` (`Tools/ShippingGen5ReadKinds.lean`, [RK] §2.4) takes it as the premise `hq`. Gate acceptance does not give it (`ShippingReaderTerm.lean:43-47`: recognisers do not pin domain/levels/type arguments, "accepted ⟹ a quotation" is FALSE as stated). The fuel twin has no invariant "every `machConvF` output is in quotation form" (`ShippingLetsReaderInvMain.lean` OPEN: "the Expr → typed `letFields` / `quote` link"). See §7 C1 |
| D7 | `splitLets nLets ⟨W, whole⟩ = some (letFs, core)` (R10) | M9 (`machPack` of `letFields ++ …` nests concats) | follows from D6's `whole` equalling the packed term of M9; `splitLets_some` is [DO] §5b U-E (design only). **W(DATAOF U-E, READKINDS U4)** |
| D8 | `splitFields (nOuts + nSlots) core = some fs` (R11) | M9 | same as D7. **W(DATAOF U-E, READKINDS U4)** |
| D9 | `typed`: each `unField kind f = some t` for lets/outs/nexts, with `kinds`/`fs` lengths equal (R12) | M9 (`machField` makes `.bool` ↦ `mux b 1 0`, `.bits n` ↦ itself) | `unField` shape: [DO] U-E `unField_bool/_bits`. Length equality: `letFs.length = nLets` (from D7) and `(kinds.drop (nIn+nSlots)).length = nLets` (from D3). **W(DATAOF U-E)**; sort-of-field-matches-kind needs D6 |
| D10 | repack equality `bitsBeq ⟨W,whole⟩ ⟨_,packed⟩ = true` (R13) | M9 | the three failure modes ([DO] §1 table) are excluded by M9's *construction* (`machField`/`machPack`/`machCanonAp`) only given D6 + D7-D9. **W(D6, DATAOF `bitsBeq_eq`/U-E)** |
| D11 | `d.ok = true` (R14, `MachineData.ok`, ShippingMachineAuto.lean:216-243 [B]) | M2/M4/M9/M11 | conjunct-wise in §2 (rows O1-O20) |

DG-COVER's own final statement over D0-D11 is `dataOf_some_of_rows` (§3). The "includes body-is-quotation" requirement of [D] §4 is D6.

---

## 2. Row table 2 — the conjuncts of `MachineData.ok` (row D11; [DO] S-OK)

`ok` (:216-243 [B]) is not run by production; the kernel runs it per declaration (`machine_ok` by `Eq.refl`). Rows below are what a run-level supplier must give.
`d` is the data `dataOf` returns; `d.shape = shape`, `d.nIn = nDecl + insts.length`, `d.ss` = sorts of the typed `nexts`, `d.ls` = typed lets.

| id | conjunct | reader branch | existing supplier / status |
|---|---|---|---|
| O1 | `nIn + ss.length ≤ binders.length` | M11, R4 | from D3 and `ss.length = nSlots` (D9 length). **P+W(D3)** |
| O2 | `layout.lets = letBs.length` | M11 (`lets := k`, `binders … ++ lets`) | `ShapeDecomp.lets` (:66) + count check. **S+P** |
| O3 | every binder `.bits n` has `0 < n` | M1 (`mixedGatePeel` → `mixedGateBinderKind?`), M11 instBinders, M4 slots, M5 lets | decl binders: kinds from `mixedGateBinderKind?` (the `machineShape?` docstring, Elab.lean:5050-5054, says "a Bool or a positive-width BitVec") — lemma `mixedGateBinderKind?_pos` not found. Slot/let/call kinds likewise. **U** (small pure facts about total `def`s; the reader-state parts need the fuel twin) |
| O4 | slot binders `≠ .domain` | M4 `machSlotKind?` | **U** (`machSlotKind?` not read in this survey for a `≠ .domain` lemma) |
| O5 | let binders `≠ .domain` | M5 `machBindLet`: `some .domain ⇒ (v', lets)` (no push) :3621; `machLetIndex` pushes with caller's `kind` | `machBindLet`/`Named`/`Alias` never push `.domain` (by cases, :3619-3670, **pure**), `machLetIndex` pushes `k` the caller passes: callers pass `kind` from signature `kinds` with the `.domain` arm excluded (:4062-4068, :4107-4112, mem arm :3954). Fuel-side invariant "no pushed let is `.domain`" **W(ShapeFuelBridge)**; not found as an existing lemma |
| O6 | `zipAllB` slots vs slot binders: `f.width = machWidth b.2`, `b.2 ≠ .domain`, `f.init < 2^f.width` | M11 `slots := machSlotFields (…zip inits)` | width: `ShapeDecomp.slots` (:64) gives the shape of `machSlotFields`; lengths need R5 (D3). `init < 2^width`: literal branch of `machInit?` is guarded by `v < 2^w` (`bitVecLitValue?`, Elab.lean:1350-1361) **S (by reading)**; the `natOf` branch (Elab.lean:3465-3468) and the Bool branch: **U** (soundness of `natOf` as an evaluator not found) |
| O7 | `∀ o ∈ outs, 0 < o.width ∧ outNameOk o.name` | M2, M11 `outs := machOutFields …` | name half: `outNames_of_reader` (ReaderOutNames.lean:156) **S**; width half `0 < o.width` (hypothesis `hpos` of `outsOk_of_core`, :206): **U** (needs positivity of `machWidth` of `machOuts?` kinds = O3's kind fact) |
| O8 | `outs.map name` Nodup | M2 | `outNames_of_reader` (:156) **S** |
| O9 | `packed.WF kb kv vw` | M9/M10 | **W(D6; READKINDS U3 `machine_wf_of_readN`)**: `readN_sound` gives term `WF` over `cfg`; `hw : d.vwL = widV (kindsOf d)` transport |
| O10 | `∀ j < kb, binders[bpos j] = .bool` | quote numbering | `posB 0 ks` facts (`ShippingReaderInputs`), [DO] U-D `bposL_eq`. **W(DATAOF U-D)** |
| O11 | `∀ j < kv, binders[vpos j] = .bits (vw j)` | quote numbering | same, `vposL_eq`/`vwL_eq`. **W(DATAOF U-D)** |
| O12 | `∀ f ∈ slots, f.lo + f.width ≤ core.1` | M9 widths | `machSlotFields` + `machPack` width sum = `core.1` — **U** (width of `machPack` result vs `(kinds.map machWidth).sum`; a pure lemma about total `def`s, **P-candidate**, not typed here) |
| O13 | `∀ o ∈ outs, o.lo + o.width ≤ core.1` | M9, M11 `machOutFields` | same family as O12; `machOutFields_ty` (ReaderOutsInv.lean:59). **U/P-candidate** |
| O14 | `LetsScoped bpos vpos (nIn+ss.length) letBs letFields` | M5/M9 let order | each let's value mentions only earlier lets / inputs. Fuel-side range facts exist for expressions returned by the twin (`machConvF_post`, `LetOk`, ReaderInvMain.lean), **not** as "let `j`'s stored value is `LetOk j`"; and conditional on `PureFacts` premises (`RootFloatRange`, `LiftRange`, … NOT PROVED). **U** |
| O15 | `slotsFitB fields outs.length slots` | M9/M11 | **U** |
| O16 | `∀ j<kb, K(bpos j) = bool ∧ bpos j < nIn+ss.length+ls.length` | numbering + typed lets | **W(O10, D3)** |
| O17 | `∀ j<kv, K(vpos j) = bits (vw j) ∧ vpos j < …` | same | **W(O11, D3)** |
| O18 | `∀ i<ss.length, K(nIn+i) = ss[i]?` | M4/M9 | `ss` = sorts of the typed nexts; ties slot binder kinds to `unField` kinds. **W(D9)** |
| O19 | `LetsTyped bpos vpos kb kv vw K (nIn+ss.length) ls` | M5/M9 typing of lets | **U** (same family as O14, plus typing) |
| O20 | `∀ g ∈ nexts.fields, g.2.WF kb kv vw`, `outsFitB …`, `!fields.isEmpty` | M9 | WF: **W(D6, U3)**; `outsFitB`, `!fields.isEmpty`: **U** (`fields.isEmpty` false since `outs ≠ []`, M2 + `outNames_of_reader` gives `outs ≠ []`: **S+P**) |

Rows O3, O4, O12-O15, O19, O20 (partly), D4, D6 are the **U** rows of this table. They are not claimed false or impossible.

---

## 3. Final theorem types (conditional; INTERMEDIATE until every premise is supplied)

New file `Tools/ShippingGen5Cover.lean`, `namespace Tools.ShippingGen5Cover`, `set_option autoImplicit false`. Opens
`Lean Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Sem Tools.ShippingGen5RunReads`. The names `dataOf`, `ShapeFuelBridge`,
`exprSize` are **imported**, never defined here: `dataOf` from DG-DATAOF's `Tools/ShippingGen5DataOf.lean` (`Tools.ShippingGen5DataOf.dataOf`),
`ShapeFuelBridge` from SRC-ARGW (§5 W-OSH). `GenWF`/`GenIn` are DG-SEM's and are not changed.

```lean
/-- The entry constant the run's `shapeEq` is stated at (RunReads.lean:70-72). -/
def runEntry (ci : ConstantInfo) (envR : Environment) : ConstantInfo :=
  entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

/-- The coverage proposition at one run's data (P-ENV: `senv := structEnv envR'`). -/
def CoverAt (E : ConstantInfo) (senv : StructEnv) (shape : MachineShape) : Prop :=
  ∃ d, Tools.ShippingGen5DataOf.dataOf E senv shape = some d ∧ GenWF d = true

/-- The premises of the conditional theorem: exactly the rows of §1/§2/§7 that are not supplied. One field per row id. -/
structure CoverRows (E : ConstantInfo) (senv : StructEnv) (shape : MachineShape) : Prop where
  d4  : <§7 C2>    -- domain composition (R5-R6 vs M3/M8)
  d6  : <§7 C1>    -- body is a quotation (S-COV-Q)
  o3  : <§7 C3>    -- positive widths
  o4  : <§7 C3>    -- slot kinds
  o6  : <§7 C3>    -- reset values below 2^width (natOf / Bool branches)
  o12 : <§7 C4>    -- layout/width sums
  o14 : <§7 C5>    -- let order / scoping
  o15 : <§7 C4>
  o19 : <§7 C5>
  wb1 : <§5 W-B1> -- RowB: result kinds are not .domain
  wa3 : <§5 W-A3> -- RowA: argument indices in range
  wm  : <§5 W-MEM> -- RowA4/RowB memory rows
  wc  : <§5 W-C>   -- RowC call order

/-- THE FINAL SHAPE. Conditional: `OSH` is SRC-ARGW's boundary, `rows` are the unsupplied rows. -/
theorem cover_of_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design} {b : Bool} {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape}
    {w5 w6 : Void IO.RealWorld}
    (rr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6)
    (OSH : Tools.ShippingGen3ArgSupply.ShapeFuelBridge)          -- one shared boundary; owner SRC-ARGW, see §5 W-OSH
    (rows : CoverRows (runEntry ci envR) (structEnv envR') shape) :
    CoverAt (runEntry ci envR) (structEnv envR') shape
```
Premise sources: `rr` (the run); `OSH` is used by every row marked W(ShapeFuelBridge) (D3, O5, O1, wb1, wa3, wm, wc); the DATAOF/READKINDS-dependent rows
(D7-D10, O9-O11, O16-O18) are discharged inside the proof from `dataOf`'s own lemmas once those land, and are NOT premises of the final shape; the fields of
`CoverRows` are exactly the **U** rows of §1/§2 and the W-rows of §5 that have no supplier. When a row becomes supplied its field is deleted, not weakened. The
unconditional theorem (no `rows`) is the target and is **not claimed**. `cover_of_run` with `rows` is recorded INTERMEDIATE.

Two component theorems (the proof structure; the second is writable now from §4 alone):
```lean
theorem dataOf_some_of_rows … : <D0-D11 premises> → ∃ d, dataOf E senv shape = some d        -- waits on DG-DATAOF's def (W)
theorem genWF_of_rows (d : MachineData) (h : GenWFRows d) : GenWF d = true                    -- P, §4 U-C5
```

---

## 4. Pure lemmas writable now (no dependency): full types

All in `Tools/ShippingGen5Cover.lean`. They use only `Tools/ShippingGen5SemGen.lean` [B] definitions (`RowA/RowB/RowC/GenWF`, `kDOf`, `callArgs`, `callKind`,
`letSort`, `originOf`, `posOk`, `cleanLets`) and `Tools.ShippingMachineRef.reads` ([B] Tools/ShippingMachineRef.lean:31), `machClose`/`machIn`/`machSlot`/`machLet`/
`machInstOut` (Elab.lean:4255, 3500-3506) and `inputExpr` (`Tools/ShippingMixedSourceBridge.lean:63`).

**U-C1 — rows as ∀-statements (unfolding lemmas).**
```lean
theorem rowA_iff (d : MachineData) : RowA d = true ↔
    (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
     ∀ k, k < d.shape.insts.length →
       (∀ l ∈ callArgs d k, l < d.ls.length) ∧
       ∀ cb aw dw, originOf d k = .mem cb aw dw → (callArgs d k).length = 4)
theorem rowB_iff (d : MachineData) : RowB d = true ↔
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain ∧
      ∀ cb aw dw, originOf d k = .mem cb aw dw →
        ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = .bits dw ∧
          letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
          letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw)
theorem rowC_iff (d : MachineData) : RowC d = true ↔
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true
theorem genWF_iff (d : MachineData) : GenWF d = true ↔ RowA d = true ∧ RowB d = true ∧ RowC d = true
```
**U-C5 — `GenWFRows` (a Prop-structure; `GenWF` is not changed, `genWF_iff_rows` is an iff so nothing is strengthened).**
```lean
structure GenWFRows (d : MachineData) : Prop where
  a1  : d.shape.insts.length ≤ d.nIn
  a2  : d.shape.instOrigins.length = d.shape.insts.length
  a3  : ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length
  a4  : ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw → (callArgs d k).length = 4
  b1  : ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain
  b23 : ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw →
          ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = .bits dw ∧
            letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
            letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw)
  c   : ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true
theorem genWF_of_rows {d : MachineData} (h : GenWFRows d) : GenWF d = true
theorem genWFRows_of_genWF {d : MachineData} (h : GenWF d = true) : GenWFRows d
```
**U-C2 — `cleanLets` facts.**
```lean
theorem cleanLets_length (d : MachineData) (k : Nat) : (cleanLets d k).length = d.ls.length
theorem reads_mono {okB okV okB' okV' : Nat → Bool}
    (hb : ∀ j, okB j = true → okB' j = true) (hv : ∀ j, okV j = true → okV' j = true) :
    ∀ {s : SType} (t : Term s), Tools.ShippingMachineRef.reads okB okV t = true →
      Tools.ShippingMachineRef.reads okB' okV' t = true
theorem posOk_mono (d : MachineData) {k k' : Nat} (hk : k ≤ k') {clean clean' : List Bool}
    (hc : ∀ i, clean.getD i false = true → clean'.getD i false = true) (p : Nat) :
    posOk d k clean p = true → posOk d k' clean' p = true
/-- An argument `let` that is clean for call `k` is clean for every later call `k'` (the entries of one structure call share their argument lets). -/
theorem cleanLets_mono (d : MachineData) {k k' : Nat} (hk : k ≤ k') (l : Nat) :
    (cleanLets d k)[l]? = some true → (cleanLets d k')[l]? = some true
```
**U-C3 — placeholder ↔ binder position (what `machClose` does; the link between a placeholder's index and the `kD + k`/slot/let positions `posOk` talks about).**
```lean
theorem machClose_machIn (nDecl kI n k i : Nat) (hi : i < nDecl) :
    machClose kI n k 0 (machIn i) = inputExpr (nDecl + kI + n + k) (nDecl - 1 - i)
theorem machClose_machInstOut (nDecl kI n k j : Nat) (hj : j < kI) :
    machClose kI n k 0 (machInstOut j) = inputExpr (nDecl + kI + n + k) (nDecl + j)
theorem machClose_machSlot (nDecl kI n k i : Nat) (hi : i < n) :
    machClose kI n k 0 (machSlot i) = inputExpr (nDecl + kI + n + k) (nDecl + kI + i)
theorem machClose_machLet (nDecl kI n k j : Nat) (hj : j < k) :
    machClose kI n k 0 (machLet j) = inputExpr (nDecl + kI + n + k) (nDecl + kI + n + j)
```
**U-C4 — `nIn`, `kD` and the call binder.**
```lean
theorem kDOf_add_len (d : MachineData) (h : d.shape.insts.length ≤ d.nIn) :
    kDOf d + d.shape.insts.length = d.nIn
/-- `callKind` is the stored result kind of entry `k`, from the binder fact `ShapeDecomp.callBinder_bs` (ShapeDecomp.lean:162) at `bs.length = kDOf d`. -/
theorem callKind_eq_inst (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length)
    (hn : d.nIn = kDOf d + d.shape.insts.length)
    (hb : (d.shape.binders.map (·.2))[kDOf d + k]? = (d.shape.insts.map (·.2.2))[k]?) :
    callKind d k = (d.shape.insts[k]'hk).2.2
```
Consumers: U-C1/C5 are the target forms every WFCOVER row is stated in; `cleanLets_mono` serves the group entries (`machInstanceS`, Elab.lean:4087, writes entries `k0 … k0+f-1` with the same
`js`, :4123); U-C3 gives the position meaning of RowC's `p < kDOf d + k`/slot/let ranges; `callKind_eq_inst` makes RowB's `callKind ≠ .domain` a statement about the stored `insts` result kinds (§5 W-B1).
These lemmas supply no row of §1/§2 by themselves.

---

## 5. WFCOVER rows (`GenWF`) against the reader branches

`callArgs d k = (insts.map (·.2.1))[k]?` is the argument-let index list stored by `machInstance`/`machInstanceS` (`js`, Elab.lean:4062-4073 resp. :4096-4112); `d.ls` is
the typed `st.lets` (R12); `callKind d k` is the stored result kind via the binder `nDecl + k` (M11).

| id | GenWF term | reader branch | existing supplier | status |
|---|---|---|---|---|
| A1 | `insts.length ≤ d.nIn` | R4 (`nIn := nDecl + insts.length`, :464) | arithmetic (U-C4 `kDOf_add_len`) | **P** given `dataOf`'s `nIn` definition |
| A2 | `instOrigins.length = insts.length` | M11 `instOrigins := st.instOrigins.toList` | `machineShapeF_origins_aligned` (ShippingReaderFuelShapeR5.lean:429, header "BUILT … ig4") at fuel; `InstProv.origins` (Prov.lean) | **W-A2(ShapeFuelBridge)**: premise `machineShapeF n false [] E senv true = some (some shape)` |
| A3 | every `l ∈ callArgs d k` has `l < d.ls.length` | `machInstance` :4062-4073 / `machInstanceS` :4096-4112 (`machLetIndex` returns `j` with `j < lets.size` of the NEW table) | fuel range lemmas for `machLetIndex`/`machBindLet*`: `LetsReaderInvBase` ("the returned placeholder is `v'` or `machLet j` with `j` below the NEW size", header, BUILT lc3a3). **No lemma "every stored `insts` argument index is `< lets.size`"** found; `InstArgKinds` ([AW] §3.1) implies it for non-memory entries only, and only given [AW]'s own unsupplied suppliers | **W-A3**: `∀ e ∈ shape.insts, ∀ a ∈ e.2.1, a < shape.layout.lets` (fuel invariant, copy of the `InstProv`/`LenOk` induction), + `d.ls.length = shape.layout.lets` (from D3/D9 lengths) |
| A4 | memory entry: `callArgs` has length 4 | memory arm Elab.lean:3954-3963: `machInstance … [.domain, .bits aw, .bits dw, .bool, .bits aw] … (dom :: ops)`; `memCall?` returns 4 operands (MachMemory.lean:21-35), the `.domain` kind adds no `js` | `ArgKindsAtG` is **vacuous** at `.mem` (`SigKindsAt … .mem = False`, ArgWidthSrc.lean:134-138; [AW] §1.1 says memory entries are not targets) | **W-MEM**: `∀ k, originOf = .mem cb aw dw → (insts[k]).2.1.length = 4` (fuel invariant) |
| B1 | `callKind d k ≠ .domain` | `machInstance` :4056-4059 (`| _ => none` for a `.domain` result), `machInstanceS` :4106-4107 (`fields.any domain ⇒ none`), memory result `.bits dw` | `OrdOrigin`/`StructOriginI`/`MemOriginI` (FuelProv.lean:85-125): `StructOriginI` has the `fields.any … = false`; `OrdOrigin` does **not** record `r ≠ .domain`; `MemOriginI` gives `r = .bits dw` | **W-B1(ShapeFuelBridge)**: `∀ e ∈ shape.insts, e.2.2 ≠ .domain` (needs a small strengthening of `InstProv` on the twin, not an existing lemma) + U-C4 `callKind_eq_inst` + `ShapeDecomp.callBinder_bs` |
| B2 | memory: `callKind d k = .bits dw` | same | `MemOriginI.r = .bits dw` (FuelProv.lean:118) + U-C4 | **W-MEM**, (ShapeFuelBridge) |
| B3 | memory: `letSort l0/l1/l2/l3 = bits aw / bits dw / bool / bits aw` | `machLetIndex nm kind v' lets` (:3743): for a `_machLet j` argument it returns `j` and keeps that let's own kind; otherwise it matches an existing let **by value only** (`l.2.2 == v'`), else pushes with the passed `kind` | the passed kinds are the hard-coded memory kinds. Agreement of an existing let's kind with the passed kind is a typing argument (the same `Expr` has one Lean type): that is [AW]'s `MemSrcKinds`/`ReadTyped` (`TY`, HK/SK/`EqvSound` premises), **not supplied** ([AW] §7) | **U/W(SRC-ARGW TY)**. Also the width `aw` is read by `natOf` (:3954) while the let's kind is read by `mixedGateBinderKind?` from the Lean type: agreement not supplied |
| C | call order through lets: every arg `l` of call `k` satisfies `(cleanLets d k)[l]? = some true` | args of entry `k` are converted (`machConv … arg`) BEFORE the entry is pushed (:4062-4068, :4096-4103), so they mention `_machInst j` only for `j < st.insts.size` at that time `≤ k`; dedup returns an earlier entry; a structure call writes entries `k0…k0+f-1` after its args; let values mention earlier lets (range `LetOk`) | existing: fuel range facts of **returned expressions** (`machConvF_post`, ReaderInvMain.lean). **Not found**: (i) "each stored let `j`'s value mentions only `_machLet i` with `i < j`", (ii) "each stored arg let of entry `k` mentions only `_machInst j`, `j < k`", (iii) the transport from Expr placeholders to `Term` input positions (`reads` on `d.ls`/`quote`) | **W-C** exact propositions below; transport (iii) **W(READKINDS U4 + quote)** |

**W-C, the Expr-level propositions (fuel twin, state invariants; ShapeFuelBridge for the production link).** With `st` the final reader state of the run and
`InstIn j e := e mentions machInstOut j`:
```lean
def LetValuesEarlier (st : MachRead) : Prop :=
  ∀ j nm kd v, st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsLet i v → i < j
def ArgsEarlier (st : MachRead) : Prop :=
  ∀ k c js r, st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ nm kd v, st.lets[a]? = some (nm, kd, v) →
    (∀ i, MentionsInst i v → i < k) ∧ (∀ i, MentionsLet i v → ∃ nm' kd' v', st.lets[i]? = some (nm', kd', v'))
```
(`MentionsLet i`/`MentionsInst i`: occurrence of `machLet i` / `machInstOut i`, to be defined with the `LetOk` predicate of ReaderInvBase.lean.) These are the exact
propositions DG-WFCOVER row C needs on the Expr side; the transport to RowC's `Term`-level `cleanLets` is the further proposition
`reads_of_quote` (the occurring bvars of `quote dom bools bits t` bound the positions `reads` asks for), whose full type is not frozen here (it needs the
`quote` equations, `ShippingUnifiedSource.lean:370`, and the injectivity of `bools`/`bits` numbering; it is stated in a freeze addendum if the reviewer wants that unit).

**RowC risk (DGEN R1).** A real successful source on which `cleanLets` fails would be the D3 stop of [D] §5. This survey did not find such a source and did not
search the corpus for one (that is DG-MEASURE, evidence only).

---

## 6. Rows for which this survey found no supplier or route (listed, not decided)

D4 (R3-vs-M3 domain composition), D6 (body is a quotation), O3, O4, O6 (`natOf`/Bool branches), O7 (width half), O12, O13, O14, O15, O19, O20 (`outsFitB`), A3's fuel invariant, A4/B2 memory
invariants, B1's `r ≠ .domain` strengthening, B3, C (Expr-level invariants and the Expr→Term transport). For each, §5/§2/§7 give the exact proposition. "Found no
supplier" does not mean the proposition is false or unprovable. In particular: D6 and D4 are open mathematical questions here; no source is exhibited on which they fail.

## 7. Candidate decision rows (kept apart; NOT decided here)

These are rows where, *if* the survey's "not found" persists after the reviewer's pass, a route would need a new law, a compiler change or a scope change. This
document does not choose among them; a decision document (plain-language explanation, impact, options with cost, recommendation, reversibility, consequence of not
deciding) is written and the Issue set to `decision` **only after the reviewer agrees these rows are genuinely stuck**; until then they are work items.

- **C1 — body is a quotation (D6).** Shape of the problem: production accepts a body by the syntactic `unifiedGateRoot`, which does not pin domain, universe levels
  or type arguments, while `readN`/`quote` do (ReaderTerm.lean:43-47). A body produced by a run is built by `machConv`, which also passes unknown applications through
  (Elab.lean:3957-3975). The routes seen (none adopted): (a) the production check [D] §5 D2(a) (compiler change: `dataOf`/`GenWF` as a guard, creates fallback successes, output-policy
  measurements needed); (b) `Expr.equal a b = true → a = b` (new law, READKINDS B1); (c) a fuel-twin invariant that every `machConvF` output is a quotation form,
  proved by induction with the gate (not attempted; pass-through arms make it unclear whether it is true); (d) keep `hq` as a recorded premise (conditional result,
  intermediate). Reversibility and costs belong to the decision document.
- **C2 — domain composition (D4).** [RK] §2.5's P1 (extend `RunReadsAt` with a `readMachine` run: a shared-definition change), P2 (premise), P3 (new fact on a `partial` composition).
- **C3 — reset values (O6, `natOf` branch).** The `BitVec.toNat` branch of `machInit?` (Elab.lean:3465-3468) is accepted without the `< 2^w` guard that the literal branch has. If a
  source reaches it with a value ≥ `2^w`, `d.ok` fails and so would coverage (a D3 stop). This survey did not find such a source and did not test one.
- **C4/C5** (O12-O15, O19): pure facts about `machPack`/`machField`/`machOutFields` (C4: total `def`s; likely provable) and let scoping/typing (C5: fuel-twin invariants). No law or compiler change is
  seen for C4; C5 depends on the conditional `PureFacts` premises of `ShippingLetsReaderInvMain.lean` (`RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange`, `BundleIotaRange`: NOT PROVED).

No guarantee is narrowed, no FG scope is cut, no new TRUSTED boundary is added by this document.

---

## 8. ShapeFuelBridge — one boundary, owned by SRC-ARGW

`[AW]` §2 states `ShapeFuelBridge` as the exact proposition
`∀ E senv sp, machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)` (O1/O2). **In this tree and in every branch searched
(`git grep "def ShapeFuelBridge"` over the g5*/g3*/par/* refs) it is stated only in documents and comments (`Tools/ShippingGen3ArgSupply.lean:21,139`); no Lean `def` was found.**
This document therefore does not define it. The per-row fuel lemmas of §5 (A2, A3, A4, B1, B2, C) are stated with the fuel premise
`machineShapeF n false [] E senv true = some (some sp)` directly, so they are independent of the bridge; only the assembly `cover_of_run` takes `OSH` (from SRC-ARGW's file once it
exists). If SRC-ARGW's Lean definition is not available when phase 2 starts, `cover_of_run`/`CoverRows` are left as text in this document and only §4 and the fuel-premise lemmas are built.

## 9. MEASURE (evidence only; not a completion condition)

`DG-MEASURE`: a corpus census per declaration of (i) `dataOf` success = `readMachine` data, (ii) `GenWF`, in the style of `scripts/shipping-coverage/endpoints.sh`
([T] §4). It needs DG-DATAOF's `dataOf` to run and a kjob run with output outside the source tree. **Not started; no number exists.** Interpretation fixed in advance:
a clean count is never all-success coverage (it covers neither sources outside the corpus nor fallback successes, DG-FALLBACK); a failing declaration is reported
with its row id (D3 stop), never used to narrow FG. It is not a premise or a supplier of any row above.

## 10. Phase 2 (after approval): files, checks, build

- `Tools/ShippingGen5Cover.lean` — §4 lemmas (U-C1…U-C5) and, only if their dependencies exist at that time, the fuel-premise lemmas of §5; `lakefile.lean`: `lean_lib «Tools.ShippingGen5Cover»`,
  `lean_lib «Tests.Gen5.CoverCheck»` (additions only). No edit of the compiler, `ShippingGen2Defs`, `T1Hyp`, `T1HypND`, `Elab*.lean`, `ShippingGen5SemGen.lean`.
- `Tests/Gen5/CoverCheck.lean` in the form of `Tests/Gen5/SemGenCheck.lean` [B]: **TYPE** — each theorem against an independently written `Expected…` statement
  (`checkExpected`, `isDefEq` on fully bound types); **MUTANT** — one-place changes (e.g. drop `a4`; `b1` with `.domain` replaced by `.bool`; `cleanLets_mono` with `k' ≤ k`; `machClose_machInstOut` at `nDecl + j + 1`), well-typed, rejected by `checkMutant`
  (signature/defeq rejection, **not** semantic counterexamples); **AXIOMS** — `collectAxioms`, standard only; **CLOSURE** — separate walk rejecting `sorryAx` and native-reduction axioms.
- Build: `kjob lake build <target>` one at a time in the Pod, logs outside the tree; success SHA recorded by a comment-only commit; the commit with Lean is left at `doing` ("clean build is the coder's").
- **Import build status.** Several files this survey cites carry headers "WRITTEN, NOT BUILT" / "UNVERIFIED" (ShapeDecomp, ReaderOutNames, ReaderOutsInv, ReaderLenOk, ReaderApp). Phase 2 imports only
  `Tools.ShippingGen5SemGen`, `Tools.ShippingMachineRef`, `Sparkle.Compiler.Elab`, `Tools.ShippingMixedSourceBridge` (the §4 lemmas need nothing else). The first action of phase 2 is one build of every file §5/§2 would import
  and a report of its actual result; a failing import is reported, not hidden, and the dependent row stays unsupplied.

## 11. Not claimed

- Nothing here is built, elaborated or proved. The Lean texts are proposals; no size estimate is a result. No `sorry`/axiom/`native_decide` exists because no Lean exists.
- No claim that `dataOf` succeeds or fails on any successful run; no claim that `GenWF` holds or fails on any run; no source was exhibited for either. No corpus count exists.
- No claim that rows listed in §6 are false, unprovable or impossible.
- No claim about fallback successes (DG-FALLBACK), `ClosingRun`, `GeneratedAt`, DG-ENV, DG-ACC. `cover_of_run` with `rows` is an INTERMEDIATE shape, not M5 or FG completion.
- `ShapeFuelBridge`, `ReadTyped`/`TY`, `EqvSound`, `SrcKindingLaws` are not supplied by this document. This document defines none of `GenWF`, `GenIn`, `dataOf`, `ShapeFuelBridge`.
