# G-SERVED / G-START freeze: `ServedShips0Stmt` producer (FOR REVIEW — design only, nothing built or proved)

- **Issue:** `sparkle-gen3-served` (depends on `sparkle-gen3-post` doing, `sparkle-gen3-keepchild` done).
- **Base:** `par/gen3-induct` b4ee77eb. Reference only: `par/gen2-spec` 649a6bf5 (labelled `[g2s]`). All other
  file:line refs are at b4ee77eb. Research by grep/read. No lake/lean run, no `.lean` edit, no commit.
- **Rule kept:** no new semantic premise, no FG narrowing, no edit of Defs/T1/KeepChild/compiler. The one extra
  premise proposed (§2, D1) is a decided per-declaration Bool data row. It is EXPLICIT and needs a decision.

## 1. The target and the chain

### 1.1 Frozen statement (Tools/ShippingGen2T1.lean:112-125, unchanged)
`ServedShips0Stmt L P Reach DataOk := T1Hyp L P Reach DataOk → ∀ p mctx cctx w w' raw D, Reach p.decl →
P p.decl = some p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → (dv w = 0 ∨ CacheShips L P Reach (cv w)) →
IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
RunsTo (synthesizeCombinationalCore p.decl [] false) … w (raw, D) w' →
MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc`.

**It must conclude:** the parent trace, with the SAME `ids`/`cache` witness. Every served non-memory instance of
call `k` must be origin-built (`child? = some md ∧ mc = md.1`) or a `ShipsRes` result `(mc, Dc)` whose modules
are in `D` (`ServedGP`/`Served1P`/`ServedP`, Defs:216-244). `ShipsRes` has 3 conjuncts: `RealChildA ∧ ∃ q n,
ChildShips ∧ InstClosed` (Defs:135-136). At `[g2s]` Defs:134-136 it has only 2. The `ServedP` text is identical
in both (diffed). Consumers:
- `ihAt_stepPF`, with `Or.inr hu.2` (T1:185);
- `t1_of_stepPF`, with `Or.inl hdv` (T1:241);
- `servedShipsStmt_of_0` (T1:134-139).

### 1.2 The existing served-real chain (JQC / `RealChildA` boundary)
| # | lemma | type summary | file:line |
|---|---|---|---|
| a | `core_reads_invA` | core run, `JQ D` + (`D=0 ∨ CacheInvA`) ⇒ body run from `JQC (D+1) w3`; D=0 by `tripleC_clear` | ChildRunA:89-149; CacheA:218 |
| b | `machine_run_of_coreA` | ⇒ `synthesizeMachineCertified` run from `JQC (D+1) w9`, `∀ res, r = some res → res = (m,d)` | ChildRunA:225-245 |
| c | `MachineRunJQC`, `machineRunJQC_of_closesA` | route evidence; `MachineClosesAtA` ⇒ `r ≠ none` | ServedRealA:90, :97-111 |
| d | `synthesizeChild_realC` | `JQC D` run of `synthesizeChild n` ⇒ `RealChildA ∧ JQC D w'` (needs `BodyStepC`) | DepthC:275 |
| e | `closeInstsM_realC` / `_runC` | one-output closing: ALL `shape.insts` synthesised ⇒ pure `closeInsts` of `RealChildA` children | DepthC:283; CallsCloseA:64 |
| f | `closeInstsGM_realC` / `_runC` | general closing: origin dispatch ⇒ `closeInstsG`, `MemChildren`, `ChildrenRealA` | RunAKids:59; CallsCloseA:89 |
| g | `ChildrenRealA` | `length = insts.length ∧ ∀ k, ∃ y, children[k]? = some y ∧ (child? = some y ∨ RealChildA)` | RunAKids:51 |
| h | `synthesizeMachineCertified_runsA` | harness keeps `JQC n` (`mixed_keepsAP`+`htr`); `closeLets`; `CloseCalls … ∧ ChildrenRealA` | RunAKids:109-151 |
| i | `…_machine_soundRA_ranA` | `ran` ⇒ `MachinePreservesX (ServedRealA …)` via `synthesizeMachineCertified_soundX` + `closeInsts(G)_serves`/`_acyclic`/`_names` | ServedRealA:116-191; MachineEntry:1044 |
| j | `machine_trace_lets_of_streamBRA_ranA` | data + `ran` ⇒ `MachineTraceLBX (ServedRealA …)`; `ran` used ONLY in `hpres` (:94-96) | ServedRealATrace:36 |
| k | `machine_traceL_of_data_causalRA_ranA` | GenFacts form; passes `ran` to (j) only (:87-88) | ParentSeqComposedA:23 |
| l | `machine_traceL_of_loop_causalRA_ranA` | loop form; passes `ran` to (j) only (:98-99) | Gen2Loop:37 |
| m | `genTrace` / `genTraceL` / `Pkg.trace` | per-package wrappers at `MachineRunJQC (D₀+1)` | QuadComposed:156; Gen2Loop:213; Gen2Pkg:103-112 |

These already exist at `InvAt` (G-KEEP-CHILD, built at g3kc-9b79bf3a, re-verified at g3pf-28476add):
- `stableA_invAt` (Connect:41), `servedP_mono` (:64), `machineTraceLBX_mono` (:47);
- `translate_keepsInv_of_tele` (Keep:39, gives `RecA`, which unfolds to `KeepsCP` at `hA`, TranslateA:488);
- `tripleInv_depthSet` (KeepChild:71), `tripleInv_cacheGet` (:239);
- `cacheShips_insert` (:255), `invAt_insert_runs` (:271);
- `synthesizeChild_tripleInv` (:292), `synthesizeChild_shipsRes` (:331, returning-run form).

### 1.3 Correspondence table (JQC→InvAt, RealChildA→ChildrenShipsI)
New files (compiler-files-small rule): **F1** `Tools/ShippingGen2ServedRun.lean` (run level; shared with
G-POST P1/P2) and **F2** `Tools/ShippingGen2Served.lean` (trace copies + producer). Namespace `Tools.ShippingGen2`.
| source | new name / file | kind |
|---|---|---|
| (a) at D=0: `tripleC_clear` (CacheA:218) | `cacheShips_empty`, `tripleInv_clear` (cv = {} by `O.cacheSet` hk.1, CacheA:223-225) / F1 | mechanical |
| (a) `core_reads_invA` | `core_reads_invAt0` / F1: premise `JQC D w ∧ (D = 0 ∨ CacheShips (cv w))` (G-START), concl. `InvAt (D+1) w3`; `stableA_JQC`→`stableA_invAt` after the clear/inherit split | mechanical (2 branches) |
| (b) `machine_run_of_coreA` | `machineRunInv_of_core0` / F1 (= GPOST P1 with the G-START disjunct; P1's `InvAt` form is a corollary by `Or.inr hw.2`) | mechanical |
| (c) `MachineRunJQC` | `MachineRunInv L … n c shape M D` := the same `∃ tenv b w9 w10, RunsTo … (some (M,D)) w10 ∧ InvAt L P Reach n w9` / F1; `machineRunInv_of_closes0` (closes via `.1 : JQC`) | mechanical |
| (d) `synthesizeChild_realC` | **`synthesizeChild_ships`** / F1: from `InvAt D w`, `IHAt D`, `ChildKeepsInv D`: `RealChildA ∧ (Reach n → ShipsRes) ∧ InvAt D w'`. The value comes from `synthesizeChild_shipsRes` plus the `RealChildA` of the hit (`hw.1.2`) or of the miss (`RealChildA.of_jqc`, CacheA:160, as at KeepChild:320). The end world comes from `ChildKeepsInv D` (Keeps → endW). No `BodyStepC` | needs new argument (`ChildKeepsInv` for the end world) |
| `cacheInvA_insert`, `jqc_insert_runs` | reused inside `cacheShips_insert`/`invAt_insert_runs` (existing) | reuse |
| (g) `ChildrenRealA` | **`ChildrenShipsI L P Reach shape children`** / F1, the GPOST P2 text verbatim (GPOST_FREEZE:97) | mechanical (def) |
| (e) `closeInstsM_runC` | **`closeInstsM_ships`** / F1: `mapM_hoare` with `InvAt D` and (d); right disjunct for every entry | mechanical |
| (f) `closeInstsGM_runC` | **`closeInstsGM_ships`** / F1: the same; the `child? = some` arm unchanged | mechanical |
| (h) `synthesizeMachineCertified_runsA` | `synthesizeMachineCertified_runsS` / F1 (= GPOST P2 `…_runsInv`; ONE lemma, two names to unify, D3). Harness: `mixed_keepsAP` (FrontCP:84) with `htr := translate_keepsInv_of_tele (D+1) hKI tenv mctx cctx hA` | mechanical |
| (i) `…_soundRA_ranA` | **`soundX_ships_ran`** / F2: `MachineRunInv` + `IHAt n` + `ChildKeepsInv n` + `hreach` + `hord1` ⇒ `MachinePreservesX (ServedP (ShipsRes L P) …)`. Proof text :140-191 with `hrc` replaced by `(hS (hreach k hk hnone))` | needs new argument (`hreach`, `hord1`, §2) |
| (j) `…_streamBRA_ranA` | `machine_trace_lets_of_streamBRX` / F2: X-generic, `ran`/`hB`/`htr` replaced by `hX : SoundXAt X declName d.shape m design` (the `∀ bsIn slotBs letBs, hbs → … → outsNodup → MachinePreservesX X …` of ServedRealA:119-131) | mechanical (X-generic) |
| (k), (l) | `machine_traceL_of_data_causalX`, `machine_traceL_of_loop_causalX` / F2 (pass `hX`) | mechanical |
| (m) | `Pkg.traceX` / F2 (cases `gen`/`loop`, as Gen2Pkg:108-112) | mechanical |
| producer | **`servedShips0_proved (hrow : ∀ q, DataOk q → OneOutNoMemRow q = true) : ServedShips0Stmt L P Reach DataOk`** / F2 | new assembly (§1.4) |
| T1 corollary | `t1_of_stepPF_served` / F2: `t1_of_stepPF_kc` with `hSS` discharged; conditional on `StepStmt`, `PostFactsStmt`, `hrow` | mechanical |

No row is STOP. The only route question is G-ONEOUT-REACH (§2). `servedP_mono` and `servedRealA_of_servedP`
(Connect:64/:79) keep the old `ServedRealA` derivable (control C3).

### 1.4 Producer assembly (sketch)
1. Run (b′) at `JQC (dv w) w` and the disjunct, which gives `w9`, `InvAt (dv w + 1) w9` and the run.
2. `hT.closes` (Defs:205-207) at `.1` gives `r = some (raw, D)`, which gives `MachineRunInv`.
3. Apply (i) with `n := dv w + 1`. Use `hIH`/`hKI` directly (same depth: the children run at `dv w9 = dv w + 1`).
   - The shape is pinned by `hT.defines` (`MachineDefines … q.d.shape`), as in RunA:240-243.
   - `hreach k hk hnone := hT.closed p.decl hR p hP k hk hnone` (Defs:211-213).
   - `hord1` comes from `hrow` (§2).
4. `Pkg.traceX`.
5. The body's own (legacy-translator) child calls need no `ShipsRes`: they keep `InvAt` through
   `ChildKeepsInv` alone. So G-REACH (actual body calls vs `T1Hyp.closed`) does not enter this producer.

## 2. G-ONEOUT-REACH

**What it is.** `closeInstsM` (Elab:5206-5218) computes `shape.insts.mapM fun (c, _, _) => synth c` (:5211)
whatever the entry's origin. It is selected when `instFields.isEmpty` (:5261-5262). `closeInstsGM` dispatches on
`o.child?` (:5235-5238). For one-output parents, `Served1P` (Defs:231-240) needs either `child? = some md ∧
mc = md.1` or `ShipsRes`. `ShipsRes` comes only from `Reach (insts[k]).1` (`IHAt`/`CacheShips` are
`Reach`-guarded, Defs:141-143, 158-162). `T1Hyp.closed` gives `Reach` only when `child? = none` (Defs:211-213).
A memory-origin entry with `instFields = []` therefore has neither disjunct. The fact needed:
`hord1 : q.d.shape.instFields = [] → ∀ k < insts.length, (instOrigins.getD k .ord).child? = none`.

**Where assumed or missing:**
- (e)/`closeInstsM_ships` is fine: it gives the right disjunct `RealChildA ∧ (Reach → ShipsRes)`.
- The gap is in (i)'s one-output case (ServedRealA:151-166, `case o`): from `hor` it needs `Reach`.
- `T1Hyp.dec` (Defs:208-210) does NOT supply it. `CallDec`'s first conjunct is `child? = none`
  (Defs:95-96), but `MemDec` holds vacuously for empty `ι` (S4_CONSUMER_FREEZE `[g2s]`:620).
- The same fact is G-POST U1 (GPOST_FREEZE:157-165; GPOST_STAGE1_RESULT:29) and M2 S4-MEM
  (S4_CONSUMER_FREEZE `[g2s]`:602-607).

**Candidate routes:**
| route | what | pros | cons |
|---|---|---|---|
| R-ROW (recommended) | explicit premise `hrow : ∀ q, DataOk q → OneOutNoMemRow q = true`; `hord_of_row` (`[g2s]` Tools/ShippingGen2DataBridge.lean:37, :43-60, built g2db-5d6ca626) gives `hord1` in range | decided Bool row on the shape; existing proof (needs only `notag_at`, ChildInv:544); the SAME row closes GPOST U1 and S4-MEM; follows the S1 precedent (`DataRows` explicit, GPOST_FREEZE:192-198); `DataOkB`/`T1Hyp` unchanged | unsupplied premise; coverage over successful compilations UNMEASURED (G-DATA); the file is not in gen3-induct (it imports `[g2s]` `ShippingGen2FitChain`), so the 4 decls must be copied (D2) |
| R-READ | `MachineDefines ⇒ hord1` by a reader invariant | no extra premise | reader `machInstance` is `partial` (Elab:4049); fuel candidate `machineShapeF` not switched; `.mem` arm lacks `instStruct` (S4_PMEM_FREEZE `[g2s]`:41-60, O1/O2 unsupplied): STOP today |
| R-RUN | derive from the run (`instStmt` clk refusal) | none | needs an environment premise ("no declaration carries a placeholder name, or its compile has clk"), which is a NEW SEMANTIC premise (S4_PMEM_FREEZE `[g2s]`:23-39): rejected |
| R-WIDEN | `T1Hyp.closed` without `child? = none` for one-output parents | no row | edits frozen `T1Hyp`. `Reach` of a memory placeholder then needs `pkg`/`defines` for it, a vacuity risk: rejected |
| R-COMP | make `closeInstsM` origin-aware | removes the gap structurally | compiler change: output policy (golden + function check + measurement); touches `closeInsts`'s pure spec and `MachineClosesAtA`. Out of scope; user decision |

**Recommendation: R-ROW.** It is an explicit, unsupplied Bool data premise, not FG narrowing. Coverage is a
separate obligation, measured later by a census of `OneOutNoMemRow` over the corpus. Use ONE row for served,
post U1 and S4-MEM.

**Status of R-ROW (coder note, binding on this freeze).** A producer taking `hrow` proves a CONDITIONAL
`hrow → ServedShips0Stmt`, and C2 below is a T1 statement with one more premise than `T1Stmt`. Both are INTERMEDIATE
results: they are not `ServedShips0Stmt` / `T1Stmt` and cannot complete G-SERVED, M3 or FG while `hrow` is unsupplied.
Making the row part of `DataOkB`/`T1Hyp` is the shared strengthening listed in S4_WID_SUPPLY `[g2s]` §4.1 (revision
table) and is NOT approved; this freeze does not apply it. The general supply of `hrow` (for every successful
compilation) is the open G-DATA coverage obligation (P-MEM-1/2), tracked under `sparkle-gen3-data-supply`.

## 3. Interface to G-POST
- **Consumed from `PostFactsStmt`:** nothing directly. `InstClosed` of served children arrives inside `ShipsRes`
  through `IHAt (dv w + 1)` and `CacheShips`. Those are premises of `ServedShips0Stmt`, and `ihAt_stepPF`
  establishes them using `hPF` (T1:183-185). No-top-name is not used: `ServedP` is about `raw`/`D` of the core
  run, not the full entry.
- **Shared with post:** P1 (= `machineRunInv_of_core0`) and P2 (= `synthesizeMachineCertified_runsS`,
  `ChildrenShipsI`, `closeInsts(G)M_ships`, `synthesizeChild_ships`) live in F1, and post imports F1. P7
  (`closeInsts(G)_kids_inst`, b4ee77eb) is not used by served. U1 is resolved by the same `hrow`.
- **Provable now, unconditionally on post:** all of F1, and F2's `servedShips0_proved` under `hrow`. Only
  `t1_of_stepPF_served` remains conditional on `PostFactsStmt` (and `StepStmt`).
- **Acceptance** of `sparkle-gen3-served` still waits for `sparkle-gen3-post` done (manager dependency). F1 must
  then be RE-ELABORATED at the combined SHA; evidence from another SHA is not reused.

## 4. Staging, controls, audit, size, build
**Stages:**
- S0: this freeze reviewed; D1-D3 decided.
- S1: F1, coordinated with the post coder (a single owner of F1).
- S2: F2.
- S3: controls/audit file `Tests/Gen3/ServedCheck.lean` + lakefile entries + result doc
  `scripts/gen2/SERVED_RESULT.md`.

**Controls (Tests/Gen3/ServedCheck.lean):**
- C1 expected types: `example : ServedShips0Stmt L P Reach DataOk := servedShips0_proved L P Reach DataOk hrow`.
  The statement text is compared against T1:112-125 at b4ee77eb (no Defs/T1 diff in the build range).
- C2 `example : T1Stmt … := t1_of_stepPF_served …`, with exactly `StepStmt`, `PostFactsStmt`, `hrow` as premises.
- C3 the old boundary is still derivable: `servedRealA_of_servedP shipsRes_real` on the producer's trace.
- C4 row controls (as `[g2s]` Tests/Gen2/DataBridgeCheck.lean): positive (`callerL` data, `decide`), negative
  synthetic `memShape0` (mem origin, no fields: row false), implication-form `memShape1` (memory parent passes).
- C5 non-vacuity of `hrow`: one concrete one-output package whose row decides `true`.

**Audit clause:**
- `#print axioms` on every new root shows `[propext, Classical.choice, Quot.sound]` or a subset.
- No `sorry`/`axiom`/`native_decide`.
- The diff vs b4ee77eb touches only F1, F2, the check file, the lakefile and docs.

**Size:**
- F1 ≈ 300-350 lines: (a) ~70, (b) ~20, clear ~15, (d) ~40, (e)+(f) ~90, (h) ~50, defs ~20.
- F2 ≈ 450-500 lines: (i) ~85, (j) ~125, (k) ~95, (l) ~110, (m) ~25, producer + corollary ~50, row copy ~30.
- Checks ~80.
- Risk: heartbeats in (j) (existing `maxHeartbeats 2000000`, ServedRealATrace:32).

**Build:** one issue-linked focused incremental build at the exact head.
`kjob -N sparkle-dev run --issue sparkle-gen3-served --name g3sv-<sha8> -m 12Gi -c 4 -- kjob lake build
sparkle_barrier sparkle_jit Tools.ShippingGen2ServedRun Tools.ShippingGen2Served Tests.Gen3.ServedCheck`.
Re-run after post lands, at the combined SHA, adding `Tools.ShippingGen2PostFacts` and `Tests.Gen3.T1Check`.

## 5. Decisions / stops
- **D1 (G-ONEOUT-REACH route):** R-ROW (recommended) / R-READ (stop today) / R-COMP (compiler, user) /
  R-WIDEN (rejected). Without a decision, (i) and the producer stop at `hord1`. F1 is unaffected.
- **D2 (row source):** (a) copy `noMemRowS`/`OneOutNoMemRow`/`hord_of_rowS`/`hord_of_row` text-identically into
  F2 (namespace `Tools.ShippingGen2Served`) and add an `rfl` bridge at integration; or (b) wait for `[g2s]`
  integration. Recommend (a).
- **D3 (names):** the issue's `closeInstsGM/M_ships` and `synthesizeChild_ships` vs GPOST P2's `…_runInv`/
  `…_runsInv`. Recommend the issue names, recorded in GPOST as the same lemmas. One F1 owner, so that the two
  issues do not edit one file concurrently.
- **Stop (report, do not patch):**
  - any copy in §1.3 that fails to elaborate with only the listed substitutions;
  - `hX` failing to match `synthesizeMachineCertified_soundX`'s callback;
  - any need for `BodyStepC`/`Nonempty ι`/a new semantic premise.

## 6. Not claimed
- Nothing is built or proved; all line numbers are by reading at b4ee77eb / 649a6bf5.
- G-ONEOUT-REACH is unresolved until D1. Row coverage is unmeasured.
- G-REACH, G-POST (P1/P2/DataRows/U1/U2 assembly), `StepStmt`/M2, G-LIFT, route-indexed `T1Hyp`, FG: all open.
- `RealChildA` is history, not freshness or runtime fit. No T1/M3 completion is claimed.
