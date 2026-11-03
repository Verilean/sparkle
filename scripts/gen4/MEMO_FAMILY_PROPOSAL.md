# MEMO_FAMILY_PROPOSAL: A_M2 row-by-row check for memo content, and a complete type for one shared memo law family (option B + D)

Status: study / proposal. **Document only.** No Lean file of the tree is edited; nothing is proved about the translator; the family below is
**not used as a premise anywhere** (its statement was only elaborated). Base 4a54e1f0 (par/memo-family; `PARAM_MEMO_STUDY.md` approved as a study, memo laws NOT approved).
Ledger: FG 91 / T1 57 (this unit: FG -0 +0 / T1 -0 +0).
Vocabulary: **read** = my reading of a file, not checked by Lean; **counted** = printed by a command in this unit; **elaborated** = built by `kjob lake build` (scratch, exit 0);
"this study did not find X" means a supply path / row was not found by this reading; it is not a claim that X is impossible. Mutants: none were made in this unit (so no signature/defeq rejection is reported; a future freeze Check would report those as signature/defeq rejections, not semantic counterexamples).
Sources read: `par/fg-ledger-sync:scripts/gen2/premise_ledger/{A_M2,B_M4,C_M5dg,D_M5t2}.md` and `scripts/gen2/PREMISE_LEDGER.md` (FG index), `par/t1-ledger-sync:scripts/gen3/PREMISE_LEDGER.md` (T1), `Tools/ShippingMemoLaws.lean`, `Tools/ShippingMemoInv.lean`, `Tools/ShippingLegacySemMemoWalk.lean`, `Tools/ShippingChildInvA.lean`, `par/gen3-induct:Tools/ShippingGen2T1.lean` header, `Sparkle/Compiler/Elab.lean` (writers of the tracked cells).

## 0. Result in short

1. **A_M2 P-01 … P-28, read block by block (§1.1): no block states a law about the memo cell `sparkleSubModuleCache`.** Four blocks mention it or its neighbours and are
   classified separately: P-01 (the `Laws` boundary: the memo occurs only as a member of the *framed* class, indirectly), P-22 and P-24 (they point to `CacheShips`, whose doc says the memo is NOT covered, G-MEMO), P-03 (`JQC`/`CacheInvA` is about the *child* cache). The words "memory/MemDec/MemOrigin" in P-13, P-14, P-16, P-26 are about hardware memory instances, not the memo (a name collision to keep in mind).
2. **Other ledgers (§1.2):** B_M4 has the memo only in F-9 (a list of items "no theorem found": T-LEG, T-MEMO, K4, "memo law"; F-9 is not a counted block) and in no P-row. C_M5dg: EN-4 `CellPrem` quantifies over `SideRef` (which contains the memo as one of 24 refs) but states only ReadWorld/SetFrame of the cell, no value law. D_M5t2: none. T1: **T1L-25 only** (G-MEMO, "obligation, unassigned"; M3's header says it is "only a DISPATCH exclusion", no memo law used), plus T1L-01 (`Laws`), T1L-22 (`RefLaws`↔`Laws` bridge) as neighbours.
   The ledger row the reviewer called "B.F-8 の memo 腕" **was not found**: B.F-8's text is the `ChildRunN` clean-up input and does not mention the memo. The memo item in the fallback chain is F-9 plus the existing Lean `outer_miss` (premise `RefLawsM`). Reviewer: please say if another row was meant.
3. **The shared family (§2): 7 fields, 10 leaf statements** (`frame`, `frameCacheSet`, `frameDepthSet`, `memoGet`, `memoSet`, `memoModify`, `tele` = 4 telescope statements), over the `O` of a `Laws`, in the restricted style of `RefLawsAOps` (admissible context, quiet world). Elaborated, exit 0, standard axioms only.
   **Correction to PARAM_MEMO_STUDY §2:** C-M1 over `FramedA` is not enough; the walk also performs the writes of the two tracked cells that are outside `FramedA` (`sparkleChildCache.set/modify`, `sparkleSynthDepth.set/modify`), so two more frame statements (`frameCacheSet`, `frameDepthSet`) are needed; and the separate `distinct` field of `RefLawsM` is folded into `frame` by quantifying over `FramedNM` (the framed class without the memo's own constructors), because a hypothesis `¬ MemoOpA p` on a *term* cannot be discharged for a non-memo ref without a distinctness fact (a `cases` on it failed in scratch).
4. **Counts (§3):** the family is 1 row (as one structure), 3 rows (C-M1/C-M2/C-M3 grouping) or 10 rows (per leaf statement), depending on the counting rule; if it is added as a third field of `Laws` it adds 0 rows but **changes** the existing TRUSTED row A.P-01 = T1L-01 (and a shared definition, which this unit may not edit). The only rows that can go down are the conditional B.P-8 −1 / B.P-1 −1 (all of F-θ, F-top, F-post, shape, assembly, F-kids first). Net: −1 (1 row), +1 (3 rows), +8 (10 rows); T1: 0 now (T1L-25 can go only if M3 changes its dispatch exclusion into the K-branch proof). Nothing moves today.
5. §4 is the plain-language material for the user decision. **Nothing is decided here.**

## 1. Ledger check by ID

### 1.1 A_M2 (28 blocks, `A_M2.md` lines 947-1503; "含む" = states a law/premise about the memo)

Columns: block / one-line content / memo? / evidence (line of `A_M2.md`).

| ID | content | memo? | evidence |
|---|---|---|---|
| P-01 `Laws` (G5) | `L.O : RefLawsAOps`, `L.T : RefLawsATele` | **間接**: `sparkleSubModuleCache` occurs in `Laws`' constant closure only as the ctor `SideRef.subModule` of the framed class (leaves `cv/sv/dv`); no value function or law for `mv` (read: PARAM_MEMO_STUDY §1; `Tools/ShippingChildInv.lean:75`) | 947-955 |
| P-02 `AdmCtx` | `canUnfold?` callback inert | 含まない | 957-965 |
| P-03 `JQC` | `JQ ∧ CacheInvA O (cv w)` | 含まない (child cache only) | 967-975 |
| P-04 core run `RunsTo` | input | 含まない | 977-985 |
| P-05 `hpost` | b / raw post-processing | 含まない | 987-995 |
| P-06 `MachineDefines` | shape reflection | 含まない | 997-1005 |
| P-07 `MachineTaken`/`MachineClosesAtA` | route evidence | 含まない | 1007-1015 |
| P-08 package existence / G3-GEN | `P c = some q` | 含まない | 1017-1025 |
| P-09 `DataOkB` rows | decidable rows | 含まない | 1027-1046 |
| P-10 `MemParentDataOk` | "Mem" = hardware memory | 含まない (name collision) | 1048-1069 |
| P-11 `LeafDataOk` | rows | 含まない | 1071-1093 |
| P-12 `ExtInS` | input extension identity | 含まない | 1095-1114 |
| P-13 `MemOrigin` | memory instance origin | 含まない (hardware memory) | 1116-1135 |
| P-14 case premises | insts/instFields/slots | 含まない | 1137-1172 |
| P-15 `hrst` | rst not an input | 含まない | 1174-1183 |
| P-16 `MemDec` (G-MEMCALLS) | memory-call decomposition | 含まない (hardware memory) | 1185-1193 |
| P-17 `CallDec` (G-CALLDEC) | ordinary call decomposition | 含まない | 1195-1204 |
| P-18 `HPointAt`/`HPointG`/`CallFactF` | per-call generator residue | 含まない | 1206-1283 |
| P-19 `callArgsOkAt`/arity | port data | 含まない | 1285-1322 |
| P-20 4 row premises | `hLeafRow`.. | 含まない | 1324-1344 |
| P-21 `hseq` | clk input | 含まない | 1346-1354 |
| P-22 G-SERVED trace | `ServedP (ShipsRes L P)`; "T1 台帳を参照" | 含まない; **points to** `CacheShips` (inside `ShipsRes`'s `InvAt`) whose doc (`GEN2_DEFS` 140, A_M2 line 624) says the memo is NOT covered (gap G-MEMO) | 1356-1364, 624 |
| P-23 G-LIFT | `LiftShips` | 含まない | 1366-1384 |
| P-24 `ChildKeepsInv` (G-KEEP-CHILD) | "T1 台帳を参照" | 含まない (child cache) | 1386-1391 |
| P-25 `OneOutWidth` | widths | 含まない | 1393-1424 |
| P-26 `hnomem`/`hord` (P-MEM) | "mem" = memory instances | 含まない (hardware memory) | 1426-1443 |
| P-27 `TopShips` premises / `PTopPrem` | c1..c6 | 含まない | 1445-1474 |
| P-28 `PbhRunEx` | run existence | 含まない | 1476-1503 |

Not in the P-blocks but in A_M2: §1.x history lines 51, 57, 63 ("MemDec", "G-MEMCALLS": hardware memory), line 843 (`T1Stmt` doc: "G-REACH, G-SERVED, G-CACHE and G-MEMO are lemmas of its proof", i.e. G-MEMO is *expected to become a lemma*, no premise). Count: of 28 blocks, **1 indirect (P-01), 2 pointers (P-22, P-24 → G-MEMO via `CacheShips`), 25 none**. (Counting method: I read each block's heading, Lean names, type text, "効く binder" and classification lines; I did not re-derive the `Laws` closure — that count is PARAM_MEMO_STUDY's.)

### 1.2 B_M4, C_M5dg, D_M5t2, T1 (memo-related rows by ID)

| ledger / ID | content | memo law? |
|---|---|---|
| B_M4 F-9 (not a counted block) | "instance あり body、非 fragment の `mergeChecked`、T-LEG、**T-MEMO、K4**、depth0 T-FIN …、**memo law**。各 theorem はこの調査では見つからなかった" (B_M4 line 161) | names the memo law as *unsupplied*; no type |
| B_M4 F-1 `ChildKeepsInv` (D+1) | IH of the fallback chain | no |
| B_M4 F-8 `ChildRunN` input | core-module run end for clean-up | no memo text (the "memo arm" is not here) |
| B_M4 P-7 `RefLaws` (I3c) | old 26-field `RefLaws`; B.P-7 | no memo field (`RefLawsM` = P-7's `RefLaws` + 6 memo fields not in any row) |
| B_M4 P-1 / P-8 | `AllPos θ` / `LegalBinding D θ` | no (the conditional −1 / −1 targets) |
| B_M4 G-1..G-10, P-2..P-6 | gate / param-model rows | no |
| C_M5dg EN-4 `CellPrem` | `CellOK` for the 3 tracked cells, `∀ r, SideRef r → CellOK cref r`, fresh refs, `mref`, `cref` | **間接**: the memo is one of the `SideRef` cells, but only `ReadWorld`/`≠ cref`/`SetFrame` w.r.t. `cref` (no `mv` value law, no frame of `mv`) |
| C_M5dg EN-1..EN-3, EN-5..EN-8, RR, CR, RK, DO, SM, AC, CV, RT, DG | env / reads / data rows | no (`grep -i memo` on C and D prints no line; the `cache` lines are `cv`/`CacheInvA`/`CacheShips`) |
| D_M5t2 all (P1-P3, T-1..T-12, D-1..D-9, E-1..E-13) | `hG_MEMCALLS` (T-11) is `MemDec` = hardware memory; E-10 `Laws` 14 fields | no |
| T1 **T1L-25** | "G: `sparkleSubModuleCache` memo (G-MEMO), not covered by `CacheShips`", owner unassigned, "obligation" | **this is the only memo row**; names no law; T1 §"G-MEMO": "NOT resolved: recorded as a dispatch exclusion under `T1Hyp.defines`/`closes`; row 25 stays" |
| T1 T1L-01 / T1L-22 | `Laws`; `RefLaws`↔`Laws`/`JQC` bridge | neighbours (where a memo family would attach / bridge) |
| T1 T1L-26, T1L-18, T1L-04, T1L-41 | `MemDec`, case X, `hrow`, `i₀` | hardware memory, not the memo |

Existing Lean related to the memo, not in a ledger row: `Tools/ShippingMemoLaws.lean` (`RefLawsM`, 6 own fields; file header: "This file EXTENDS the trust base"), `Tools/ShippingMemoInv.lean` (`MemoInv`, `ArmObligations`, `MemoSound`: statements only), `Tools/ShippingLegacySemMemoWalk.lean` (`outer_miss`, premise `RefLawsM`, **unrestricted** in context and world — the `Laws` family is restricted to `AdmCtx` and quiet worlds, so `outer_miss` is not directly applicable to it; it would need a restated proof — a Lean unit, not done here).

## 2. The shared family (complete Lean type)

Scratch `Tests/Gen4/MemoFamilyScratch.lean` (6 builds while fixing; final: `kjob lake build Tests.Gen4.MemoFamilyScratch`, 702 jobs, **exit 0**, no sorry; `#print axioms` of `MemoFamily`, `MemoTele`, `memo_miss_of_child_miss`, `reset_then_side_set`, `memoKeys_keeps_step` = propext, Classical.choice, Quot.sound). File and lakefile entry removed; the text below is the elaborated text (the two long inductives are described, not pasted: they are mechanical copies).

```lean
def mv (w : Void IO.RealWorld) : Std.HashMap Name Res := readOf Sparkle.Compiler.Elab.sparkleSubModuleCache w   -- a definition, not a premise

/-- SideRef (Tools/ShippingChildInv.lean:60) without its `subModule` constructor: 23 constructors (counted), the same list. -/
inductive SideRefNM : {σ : Type} → IO.Ref σ → Prop   -- | wireWidth : SideRefNM sparkleWireWidthCache  … (23)

/-- FramedA (Tools/ShippingChildInvA.lean:139-203, 40 constructors counted) with `SideRef r` replaced by `SideRefNM r` in its 7 side-ref constructors; the other 33 are verbatim.
    So it is the framed class WITHOUT the memo's own get/set/modify. -/
inductive FramedNM (Fresh : (σ : Type) → IO.Ref σ → Prop) : {α : Type} → MetaM α → Prop   -- 40 constructors

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

structure MemoTele (O : RefLawsAOps MkRefd mref cref) : Prop where     -- C-M3
  telescope lamTelescope localDecl letDecl : <the four statements of RefLawsATele (Tools/ShippingChildInvA.lean:296-334) with `mv w' = mv w →` added to the step condition
    `∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') → I w → I w'`>

structure MemoFamily (O : RefLawsAOps MkRefd mref cref) : Prop where
  -- C-M1: framed operations on any ref other than the memo leave the memo
  --       (this is also the non-aliasing assumption for the 23 side refs and for the run-made refs)
  frame : ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ {α} (p : MetaM α), FramedNM MkRefd p → ∀ w, O.quiet w →
    mv (endW mctx mref cctx cref p w) = mv w
  -- C-M1': the writes of the two tracked cells that are outside FramedA (Elab.lean:5541, 8932, 5561, 5577)
  frameCacheSet : ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  frameDepthSet : ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  -- C-M2: the memo's own operations
  memoGet : ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ m w w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' → O.quiet w → mv w' = mv w
  memoSet : ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = v
  memoModify : ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ f w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = f (mv w)
  -- C-M3
  tele : MemoTele O
```
Notes. (i) `modify` of the two tracked cells (`modify` at 8932, 5577) is not a separate statement: by the generic split `modify = get; set` (`modify_split`, read, built elsewhere) it reduces to `frameCacheSet`/`frameDepthSet`; not re-proved here. (ii) The value returned by a memo `get` is `readOf` of the cell (`runsTo_get_readOf`, a theorem, no law), which is why there is no `mval` field. (iii) `memoModify` is kept to mirror `RefLawsM`; it is derivable from `memoGet`+`memoSet` by the same split, so a minimal family drops it (9 leaf statements). (iv) `frame` is true only if the cells really are distinct; that is the old `RefLawsM.distinct` assumption ("two `initialize … ← IO.mkRef` allocate two cells") — still not provable in Lean.

Elaborated consumer facts (statements about the family, *assuming* a `MemoFamily` hypothesis; not used as premises of any tree theorem):
* `reset_then_side_set` (proved): after a successful `memo.set {}` and a successful `set` of a `SideRefNM` ref, `mv = {}` (uses `memoSet`, `frame` at `FramedNM.sideSet`).
* `memo_miss_of_child_miss` (proved, from K only), `memoKeys_keeps_step` (proved): K = `MemoKeysInChild w := ∀ n, ((mv w).get? n).isSome → ((cv w).get? n).isSome`; K survives a step that leaves `cv` and `mv`. This is exactly the shape the new `tele` step condition (`cv` and `mv` unchanged) supplies.
* Not done: a lemma turning a `FramedA MkRefd p` into `FramedNM MkRefd p ∨ MemoAccess p` (my `cases` attempt timed out / left side goals; it needs a per-constructor argument, with `MkRefd` an existential — read, not proved).

### 2.1 Who uses what

| consumer | fields used | status of the consumer |
|---|---|---|
| (a) parametric K (`memo keys ⊆ child-cache keys`, PARAM_MEMO_STUDY §3) | all: `frame` at the framed constructors of the translator walk, `frameCacheSet` (insert at 8932, reset at 5541), `frameDepthSet` (5561/5577), `memoSet`/`memoModify` at the 5 writer sites (5297, 5304, 5323, 5388, reset 5540), `memoGet` at the read (5335), `tele` at the 4 combinators | K and its walk are not proved (statement and obligations (a)-(d) of PARAM_MEMO_STUDY §3) |
| (b) fallback memo hit (T-MEMO / `outer_miss` in the F-9 sense) | `memoSet` (reset), `frame` (8 side sets, `getConstInfo`, `getEnv`), `frameCacheSet`, `frameDepthSet`, `memoGet`; **no `tele`** | `outer_miss` exists only under `RefLawsM` (unrestricted); a restatement under `AdmCtx`/quiet is a Lean unit not started |
| (c) M3 G-MEMO (T1L-25) | today **none**: M3 records G-MEMO as a dispatch exclusion under `T1Hyp.defines/closes`, "no cache invariant about the memo map is stated or used" (`Tools/ShippingGen2T1.lean` header @par/gen3-induct). It would use the family only if M3 replaced the exclusion by the K-branch of GENERAL_SPEC §4.3 ("its own invariant, or a proof that machine-route parents never read it") | undecided by M3; sharing is an option, not a present need |

## 3. Counting

Rows are counted against the R0 ledgers (FG 91 / T1 57). One family must not be counted +1 in both ledgers.

| counting rule | rows added | note |
|---|---|---|
| R-1: `MemoFamily` as one structure, one TRUSTED row | +1 | simplest; same granularity as `Laws` (A.P-01 / T1L-01 is one row of two structures) |
| R-3: by the C-M1 / C-M2 / C-M3 grouping (frame + the 2 tracked-cell frames; get/set/modify; tele) | +3 | matches PARAM_MEMO_STUDY's candidates |
| R-10: per leaf statement | +10 (+9 without `memoModify`) | most conservative |
| R-0: add as a third field of `Laws` (`Laws.M`) | 0 new, but **changes** A.P-01 = T1L-01 | needs a change in `Tools/ShippingGen2Defs.lean` (shared definition, not allowed in this unit) and in the FG statement's `∀ L : Laws`; user decision |

Rows that can go away (conditional; **only if all of F-θ, F-top, F-post, shape, assembly and F-kids are proved**; B.P-8/B.P-1 are not reduced by any one of them): B.P-8 −1, B.P-1 −1 (unchanged from the approved estimate).
T1 side: T1L-25 −1 only if M3 turns its dispatch exclusion into the K-branch proof using this family (not planned today).

| rule | gross | conditional −  | FG net if all conditions met | T1 |
|---|---|---|---|---|
| R-1 | +1 | −2 | −1 | 0 now (T1L-25 stays); −1 only if M3 adopts the family, and then the family's +1 is booked in one ledger only |
| R-3 | +3 | −2 | +1 | same |
| R-10 | +10 | −2 | +8 | same |
| R-0 | 0 (+ change of A.P-01) | −2 | −2 | same |

Today (conditions not met): the family adds its rows and removes none. **Ledger line (accepted values only): 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）.** This document accepts and changes nothing.

## 4. Material for the user decision (plain language; no decision is taken here)

**What the memo is.** While the Sparkle compiler turns one Lean definition into hardware, it keeps a small notebook in memory (`sparkleSubModuleCache`, a table "declaration name → the module already produced") so that a declaration reached again by one particular translation route (the "legacy" route) is not translated twice. It is cleared at the start of each top-level compilation and written at the end of four of the routes. Separately, there is a second notebook for child modules (`sparkleChildCache`), which the existing proofs already track.

**Why Lean cannot prove facts about it by itself.** Both notebooks are global mutable cells created by `initialize … ← IO.mkRef`. In Lean's logic such a cell is an opaque constant: the logic does not say that two such cells are different cells, nor what a "set" or "get" does to the machine state of a run. The existing proofs therefore take a few such facts as *assumed laws about the runtime* (the TRUSTED `Laws`: "setting the child cache changes only the child cache" and so on). They cannot be proved inside Lean; they can only be assumed and checked against the real runtime by testing/reading.

**Why the parametric (symbolic-width) route needs it.** The proof that a successful parametric compilation ships a correct design walks through the whole translator. At one place the legacy route could return a stored result from the memo instead of translating; the proof must either say what a stored result looks like (hard) or show that this never happens for a child (the "K" invariant: every name in the memo is already in the child cache, and the child cache is looked at first). To state and carry K through the translator's steps one has to know that those steps do not touch the memo: that is the family's content. So avoiding a *content* invariant does not avoid *new runtime laws*.

**The laws, one sentence each** (names of §2):
1. `frame`: every ordinary step the translator performs on any cell other than the memo (reading/writing the 23 bookkeeping cells, the cells it creates for itself, reading the environment) leaves the memo's table unchanged. *(This also assumes those cells are not the memo.)*
2. `frameCacheSet` / `frameDepthSet`: writing the child cache or the recursion-depth counter leaves the memo's table unchanged.
3. `memoGet`: reading the memo leaves it unchanged.
4. `memoSet` / `memoModify`: after the memo is set to `v` its table is `v`; after it is modified by `f` it is `f` of the old table.
5. `tele` (4 statements): the translator's four "open a binder, run a continuation, close" helpers (`forallTelescope`, `lambdaTelescope`, `withLocalDecl`, `withLetDecl`) keep any invariant that depends on the memo as well, provided the continuation does.

**What is affected.** Without a decision, the parametric chain's F-kids invariant stays a statement; B.P-8 and B.P-1 cannot be reduced (their conditional −1/−1 require it); the symbolic-entry part of the final general guarantee stays open. M3 is not blocked (it uses no memo law today), and the fallback memo-hit item (F-9) stays "no theorem found".

**Options** (impact / cost; none decided):
* **A. No memo laws; keep F-kids as a statement.** User-visible: nothing changes. Cost: 0. Effect: the parametric guarantee cannot reach "no premise beyond the TRUSTED set"; ledger does not move. Reversible.
* **B. Add the family as a separate TRUSTED structure next to `Laws` (rule R-1/R-3), used by parametric K only.** Cost: a freeze (reviewer + user), Lean for the family file (small), then the F-kids walk (estimate 3500-5000 lines, PARAM_INV_ESTIMATE, estimate). Effect: trust base grows by 7 fields; no data-loss risk; reversible before proofs depend on it, expensive after.
* **C. B + share with the fallback memo-hit (b) and optionally M3 (c) (option D).** Cost: B plus a restated `outer_miss` under the family; sharing with M3 only if M3 changes its approach. Effect: one family instead of up to three bespoke assumptions.
* **D. Add the family as a third field of `Laws`.** Changes an existing TRUSTED statement and a shared definition (the FG statement quantifies over `Laws`); affects every M3/M4/M5 consumer's type. Highest coordination cost; not recommended without a separate decision.
* **E. Production guard** (the compiler refuses a memo hit below the top; removes the need for K). A production-code change, outside this unit's permission; not evaluated further.

**Recommendation (reviewer's lean, restated, not a decision):** C with the family as a separate structure (rule R-1), minimal form (drop `memoModify`), because it keeps the memo's *content* out of the trust base and shares one family. **Reversibility:** nothing exists yet beyond this document; after a freeze approval and proofs that use the family, removing it means redoing those proofs. **If no decision is taken:** option A in effect — F-kids stays a statement, no memo-dependent ledger movement.

## 5. Limits, and what was not done

* Not proved: K, its obligations (a)-(d), `framedA_cases`, any use of the family in a tree theorem; the statements of the family were elaborated, and a few consumer lemmas were proved from the family hypothesis. No claim that the laws are true of the runtime or consistent with `Laws`/`RefLaws` (joint satisfiability of `Laws` is OPEN in the ledger, D.E-10).
* The ID check of C_M5dg / D_M5t2 used the block headings, the `grep -i memo|subModuleCache` lines and the blocks with cache/env words; I did not re-read every line of the 55 + 37 blocks (§1.2 says so per row). A_M2 was read block by block; B_M4 in full; T1 by the memo/cache/Laws rows and the §"G-MEMO" lines.
* "B.F-8 memo arm" was not found (§0.2). The comparison with `Laws` closure counts relies on PARAM_MEMO_STUDY §1.
* The document is a proposal for a freeze, not a freeze: the family needs a freeze review and user decision before any Lean implementation.

`台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）`
`条件付き台帳: B.P-8 -1 / B.P-1 -1（全項目揃った場合のみ。memo 法則家族の追加は 1 行（R-1）〜3 行（R-3）〜10 行（R-10）で数え方が未確定。`Laws` の第 3 field にする案は 0 行追加だが A.P-01=T1L-01 の変更）`
