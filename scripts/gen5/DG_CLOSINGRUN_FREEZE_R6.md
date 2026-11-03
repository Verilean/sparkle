# DG-CLOSINGRUN freeze r6 — supplier survey for the OPEN rows (docs only)

Base: `kjob/g5cr-r5` f2e763d0 (scoped approved; clean build cr5v-f2e763d0). Audit improvement at 9370bda2
(`ClosingRun2Check` closure walker counts an unresolved name as a FAILURE, one negative control; headers synced).
This document is a survey of which existing theorems could supply the rows that `ClosingRun0` / `closingRun0_of_run`
(Tools/ShippingGen5ClosingRun2.lean) still take as premises. A wrapper or a conditional restatement is NOT counted as a
supply. Nothing here claims T1, FG, M5 or Issue completion. Statements like "no path found" mean only that this survey did
not find a supplier or route in the tree at f2e763d0; they do not say the row is impossible or underivable.
No Lean change follows from this freeze (see §4).

## 1. Premises of `closingRun0_of_run` (frozen r4/r5 type, unchanged)

`hord`, `hT : T1HypND L P Reach DataOk`, `hs : Start L mctx cctx w`, `hd0 : dv w = 0`, `hIH : IHAt L P Reach 1`,
`hKI : ChildKeepsInv L P Reach 1`, `hrun`, `Gen`, `hGen`. Not in the structure at all: depth-0 `stop`, non-vacuity.

## 2. Supplier table (real names, full types in the cited files)

| Row | Existing candidate (file) | What it needs | Status of the row |
|---|---|---|---|
| `hord` (the `∀ q, DataOk q → q.d.shape.instFields = [] → ∀ k < insts.length, (instOrigins.getD k .ord).child? = none`) | `Tools.ShippingGen2DataBridge.hord_of_row {p} (h : OneOutNoMemRow p = true) (hf) (hk)` (ShippingGen2DataBridge.lean:57); `noMemRowS` is `!instFields.isEmpty \|\| instTagged.all (child?.isNone)` | `hrow : ∀ q, DataOk q → OneOutNoMemRow q = true` | `hord` follows from `hrow` pointwise (proved, used inside `closingRun_of_run`). `hrow` itself: **未供給 / この調査で経路未発見** (`DataOk` is an abstract Prop parameter; the only mentions of `OneOutNoMemRow` are as a premise in `servedShips0_proved`, `postFacts_proved`, `t1_of_step_rows`, `closingRun_of_run`). Rewriting `closingRun0_of_run` over `hrow` would be a wrapper, not a supply. |
| `hGen` (`RunReadsAt … → Gen ci envR envR'`) | `Gen` is a PARAMETER everywhere; `GeneratedAt` is defined only in `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` §(line 221) as a design text, NOT in the tree. In-tree: `Tools/ShippingGen5Env*.lean` (`ReadsAt`, `readsAt_self`, `ci_of_readsAt`, `envR_of_readsAt`, `machineDefines_of_readsAll`) | DG-COVER + DG-WFCOVER + `genP_generated` (C6) + DG-ENV, per DGEN_FREEZE §604 | **未供給 / この調査で経路未発見** for `Gen := GeneratedAt …`; the DG-ENV `ReadsAt` lemmas are one ingredient only. `gen_of_closingShared` gives the converse direction (Gen is extracted from the block), not a supply. |
| `hIH`, `hKI` at depth 1 | `Tools.ShippingGen2.ih_allPF L P Reach DataOk hT hStep hKC hSS hPF hLim 1 (Nat.le_refl 1) : IHAt … 1 ∧ ChildKeepsInv … 1` (ShippingGen2T1.lean:198). Parts: `hKC := keepChild_proved` (proved, KeepChild.lean:360), `hLim := limitStmt_proved` (proved, T1.lean), `hSS := servedShips0_proved … hrow` (proved, CONDITIONAL on `hrow`, Served.lean:638), `hPF := postFacts_proved … hrows hrow` (proved, CONDITIONAL on `hrows : DataRows` and `hrow`, PostFactsProof.lean:230) | `hT : T1Hyp` (WITH `dec`), `hStep : StepStmt L P DataOk`, `hrow`, `hrows` | Not closed. (a) `StepStmt` (Defs.lean:310): **この調査で供給元・経路が見つからなかった** (only `stepStmt_of_old` in PostFacts.lean:117, a conversion from `StepStmtOld`, no proof of either). (b) `ih_allPF` takes `T1Hyp`, `ClosingRun`/`closingRun0_of_run` take `T1HypND`; `T1Hyp.toND` goes only from `T1Hyp` to `T1HypND`; a route from `T1HypND` to `T1Hyp.dec` (G-CALLDEC) was not found in this survey. (c) `hrow`, `hrows` as above. |
| non-vacuity | none in the tree for `ClosingRun`, `ClosingRun0`, `ClosingShared` or `T1HypND` | a concrete `Laws`, `Pkgs`, `Reach`, `DataOk`, an actual run and all the rows above | **未供給 / この調査で経路未発見.** `closingRun_nonempty_of_premises` (r5) is conditional sufficiency over `ClosingPremises` (packaging); `not_closingShared_false` only shows `Gen := False` is excluded. Neither is a witness. |
| depth-0 `stop` (`InvAt 0 w'`) | `stop_of_run` (ClosingRun.lean:271) needs `1 ≤ dv w`; it goes through `core_tripleAInv` (KeepChild.lean:133) whose hypothesis `hD : 1 ≤ D` excludes the depth-0 cache clear | a depth-0 core run that ends with `CacheShips (cv w')` after the clear | **この調査で経路未発見.** `JQC 0 w` is in `Start` (the `hs.2` used for `hw`); no theorem giving `CacheShips` for the final cache of an outermost core run was found. `stop_of_run` is unchanged and not used at depth 0. `ClosingRun0` has no `stop` field by design (r4). |
| connection `Start → InvAt 1 w5` | supplied (r5): `invAt_w5_of_runReadsAt_JQC` from `coreHead_invAt0`, `triple_runs`, `keepsA_framed` | `hw : JQC L.O (dv w) w`, `hc : dv w = 0 ∨ CacheShips …` | proved; not an OPEN row. |

## 3. What the survey does and does not change

* `hord` is reduced to `hrow` (already known); `hrow` stays unsupplied.
* `hIH`/`hKI` have a named in-tree producer shape (`ih_allPF` at `D = 1`), but its premises `StepStmt`, `hrow`, `hrows` and
  `T1Hyp.dec` are unsupplied, so the pair stays an input. A packaging lemma `ihPair1_of_rows` (just `ih_allPF … 1 le_rfl`
  with `keepChild_proved`, `limitStmt_proved`) would add a name but no supply; not proposed as progress.
* `hGen`, non-vacuity, depth-0 `stop`: no supplier found.
* T1/FG are not claimed. No new TRUSTED boundary, law, or FG/guarantee change; `GenWF` is not strengthened.

## 4. Implementation decision

No row closes from existing parts alone, so there is no Lean implementation after this freeze (the instruction allowed
one only when a row closes). Unsupplied after this survey: `hrow`/`hrows`, `StepStmt`, `T1Hyp.dec` from `T1HypND`,
`hGen`/`GeneratedAt`, non-vacuity, depth-0 `stop`, T1/FG. Next candidates (each needs its own freeze): DG-COVER/DG-WFCOVER
for `hGen`; a depth-0 end-cache statement for `stop`; the `StepStmt` producer (M2-b).
