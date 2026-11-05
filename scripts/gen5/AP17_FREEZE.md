# AP17 freeze: FG premise-ledger row A.P-17 (`T1Hyp.dec`) derived inside the depth induction

Issue sparkle-ledger-ap17 (parent sparkle-ledger-shorten). Base: par/gpfix 7a3779e6 + merge of kjob/flow1-b e6d8e55b (72e03a47).
New files: `Tools/ShippingGen5AP17.lean`, `Tests/Gen5/AP17Check.lean` (+ lakefile entries). No existing file/definition/statement edited
except the lakefile. No new law/TRUSTED, no sorry/axiom/native_decide. Axioms of every new theorem: propext, Classical.choice, Quot.sound.

## 0. Merge record (kjob/flow1-b -> this worktree)

Only conflict: `lakefile.lean`, three regions (EnvFrame block; Cover/SemGen block; GDCover block). Resolution: keep both sides' `lean_lib`
entries (markers removed). One duplicate entry after the union (`Tests.Gen5.ClosingRun2Check`, present on both sides) was removed once.
No other conflicts (the flow1-b files are all new: `Tools/ShippingGen5T2TieCR{,2}.lean`, `Flow1Reads`, `Flow1Tie`, their Checks).

## 1. Subtraction table

| 消える ID | 入る束縛変数 (existing rows only) |
|---|---|
| A.P-17 `T1Hyp.dec` (PA non-leaf) | `H : T1HypND` (pkg/defines/closes/closed fields = the T1Hyp fields minus dec); `hrows` (T1L-05; gives `callsOk`, `ss.length = slots.length` = A.P-19/A.P-09 data rows); `hStep` (T1L-03); `hMEM` = A.P-16 `hG_MEMCALLS`; `hARGS` = A.P-19/A.P-09 `callArgsOkAt` + args length; `hOW` = A.P-25/D.T-3 `OneOutWidth`; `hkidW` = D.T-4. Package assignment (`hDG_PKGASSIGN`) from `H.closed` + `H.pkg` (`calleePkg_of_t1ND`). DG-SEM from `hDT1_of_genGP` (inside `hT2Tie_of_genGP`). `hDG_CLOSINGRUN` from the run (below), no binder. |

The table is `P := genGP lvl hs genData₀ env` (the inputs `lvl initsOf hs genData₀ env` are the existing GPFIX inputs, as in `hT2Tie_of_genGP`).

`HMemRow / HArgsRow / HOWRow / HKidWRow` (Tools/ShippingGen5AP17.lean) are the existing per-package premises of `stepDec_of_ties` /
`hT2Tie_of_genGP` quantified once over the packages `q` with `Reach q.decl ∧ P q.decl = some q` (the old `T1Hyp.dec` was quantified over the same
reached packages). They are the same statements, not new facts. REVIEWER POINT: whether the universal-over-reached form counts as the existing
row (I read it so; `hOW`/`hkidW` are row-by-row the binders of `hT2Tie_of_genGP`).

## 2. Statements (Tools/ShippingGen5AP17.lean, namespace Tools.ShippingGen2; `GP := genGP lvl hs genData₀ env`)

* `ServedShips0StmtND`, `PostFactsStmtND`: `ServedShips0Stmt` / `PostFactsStmt` with `T1HypND` in place of `T1Hyp` in the premise. Proofs
  `servedShips0_runND`, `postFacts_of_runND` are copies of `servedShips0_run` / `postFacts_of_run` (they only used pkg/defines/closes/closed).
  (They had to be copied: the originals take a `T1Hyp`, which contains `dec`, inside the induction.)
* `decAt_ND L H hrows hMEM hARGS hOW hkidW hA hR hPq hDq hjqc hcc hIH hKI hcore :
   ∀ k hk, MemDec q k _ ∨ ∃ q', GP _ = some q' ∧ CallDec q q' k`
  = `stepDec_of_ties` with `hT2_TIE := hT2Tie_of_genGP …`, whose `hDG_CLOSINGRUN` is `servedCall_of_closingShared_one` (instFields = [])
  / `servedCall_of_closingShared_group` (≠ []) applied to `ClosingShared := closingShared_of_runR … hIH hKI hcore`.
  This is the child-result -> FieldRowAt/dsn-module link of the plan: it already existed in flow1-b (`T2TieCR`, `T2TieCR2`); no new proof
  of the link was needed. No circularity: `closingShared_of_runR` needs only `IHAt/ChildKeepsInv (dv u + 1)`, i.e. the induction hypothesis
  one level deeper, not `dec` at this level.
* `ihAt_stepPF_ND L H hStep hrows hMEM hARGS hOW hkidW D hIH hKI : IHAt L GP Reach D`.
* `ih_allPF_ND L H hStep hrows hMEM hARGS hOW hkidW : ∀ D, 1 ≤ D → IHAt L GP Reach D ∧ ChildKeepsInv L GP Reach D`
  (replaces `ihKI_of_rows`; the proved statements `keepChild_proved`, `limitStmt_proved`, `servedShips0_runND`, `postFacts_of_runND` inside).
* `t1_of_stepPF_ND L H hStep hrows hMEM hARGS hOW hkidW : ∀ c mctx cctx w w1 raw b Dg, Reach c → Start L mctx cctx w → RunsTo … →
  (b = … ∨ b = …) → ∃ q n, GP c = some q ∧ TopShips q n c b raw Dg` (= `T1Stmt` after its `T1Hyp →`, with `H` as binder).
* `closingRun0_of_runT1_ND`, `closingRun_of_runT1_ND`: `closingRun{0,}_of_runT1` (ClosingRun4) with `hT : T1Hyp` replaced by `H : T1HypND`
  and the rows above added.

## 3. Check (Tests/Gen5/AP17Check.lean, built OK, exit 0)

One telescope walk per pair (old with `P := genGP …`): `ihKI_of_rows ~ ih_allPF_ND`, `closingRun0_of_runT1 ~ …_ND`, `closingRun_of_runT1 ~ …_ND`
(binder types `==`, `hT : T1Hyp L P Reach DataOk` replaced by `H : T1HypND` with the same four arguments, conclusions `==`; the only extra
binders are `lvl initsOf hs genData₀ env hMEM hARGS hOW hkidW`), `t1_of_step_rows_run ~ t1_of_stepPF_ND` (old conclusion `T1Stmt` unfolded, its
`T1Hyp →` dropped; extras additionally `H`). CONST: no type of the six new theorems mentions `T1Hyp` (control: old `closingRun_of_runT1` has exactly `hT`).
VALUE: `T1Hyp.dec` is not reachable through `Tools.*` values from the four new final theorems (control: it is reachable from old
`closingRun_of_runT1`). Negative control: a wrong pairing (`ihKI_of_rows` vs `closingRun0_of_runT1_ND`) is rejected.

## 4. Failed attempts / notes

* A static `hDG_CLOSINGRUN` built by `closingRun_of_runT1 hT` is circular (as the survey says); not used. The per-level route above avoids it.
* First draft build errors only of the name/open kind (`mergeChecked`, `tys`, `RealChildA`, `RunReadsAt`, a `GP` local notation clashing with `end GP`),
  all fixed; no mathematical obstruction met.

## 5. Remaining / not claimed

CONDITIONAL on `H`, `hrows`, `hStep`, `hMEM`, `hARGS`, `hOW`, `hkidW` (and the existing GPFIX inputs). Not the FG chain's final theorem itself: the
downstream consumers that still take `hT : T1Hyp` (e.g. `Tools/ShippingGen5AuditE3B3{,Run}.lean`, `Tools/ShippingGen5T2OutTy.lean`) are not
re-threaded here; they would take `H : T1HypND` through `T1Hyp.toND`-free versions as a follow-up if the FG chain uses them. Ledger count
change claimed: FG -1 (A.P-17) pending reviewer's reading of §1.
