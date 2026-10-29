# G-POST freeze rev1: `PostFactsStmt` and `InstClosed` in `ShipsRes` (option B) (FOR REVIEW)

- **Issue:** `sparkle-gen3-post`. **Branch:** `par/gen3-induct` at dcda5033. Read-only; no Lean written or built.
- **Context:** KEEPCHILD_POST_FREEZE.md §A, GPOST_COMPARE.md §2 (option B). The new `ShipsRes` is written `ShipsRes'`
  below. It is an IN-PLACE change of `ShipsRes` (ShippingGen2Defs.lean:128), so `CacheShips`/`InvAt`/`IHAt`/
  `ChildKeepsInv`/`KeepChildStmt`/`ServedShips0Stmt`/`StepStmt` (Defs:134-306, Gen2T1.lean:112) all read it
  without a text change.
- **Naming:** `t1_of_step'` already exists (Gen2T1.lean:240). The revised theorems are therefore named
  `ihAt_stepPF`, `ih_allPF`, `t1_of_stepPF`, `t1_of_stepPF'` (limit discharged) and `t1_of_stepPF_kc`.

## 1. Why `NoTopStmt'` alone is not enough
`NoTopStmt'` (KEEPCHILD_POST_FREEZE §A(a)) gives only (i), that no module of `Dg` is named `raw.name`. With
`ShipsRes'`, `ihAt_step`'s constructor (Gen2T1.lean:186) also needs `InstClosed (M', Dg')` for its OWN result,
which (i) does not give. Both facts are proved from one case split over the same run, so they are frozen as ONE
statement on the same `hcore`.

## 2. Definitions (exact types)
```lean
def InstClosed (r : Res) : Prop :=
  ∀ g ∈ r.2.modules, ∃ h ∈ r.1 :: r.2.modules, ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
    Sparkle.IR.AST.Stmt.inst g.name i cs ∈ h.body

-- Defs:128, in place (written ShipsRes' here)
def ShipsRes {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ (∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2) ∧ InstClosed r

-- frozen copies of the old text, used only by the projections (§4)
def ShipsResOld … := RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2
-- CacheShipsOld, InvAtOld, StepStmtOld: Defs:134, :144 and :293 verbatim, over ShipsResOld

/-- G-POST: (i) no top-named module, and (ii) InstClosed of the FULL entry's result, on one run. -/
def PostFactsStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (u u' w1 : Void IO.RealWorld)
    (M' raw : Sparkle.IR.AST.Module) (Dg' Dg : Design),
    Reach q.decl → P q.decl = some q → DataOk q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach (dv u) u →
    IHAt L P Reach (dv u + 1) → ChildKeepsInv L P Reach (dv u + 1) →
    RunsTo (synthesizeCombinational q.decl) mctx mref cctx cref u (M', Dg') u' →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1 →
    (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    Dg'.topModule = Dg.topModule →
    ((∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) →
    MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape raw Dg →
    (∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg')
```
- The full-entry relation is exactly the output of `synthesizeCombinational_designTop`
  (ShippingDesignWriterRun.lean:69-79), from the same start `u`.
- The `ran` binder is the `htaken` that `ihAt_step` already builds (Gen2T1.lean:180). Both conclusions are about
  the VALUES `raw, Dg, M', Dg'`, which `hcore` fixes, so they do not depend on which existential witness is used.
  The producer re-derives an `InvAt` witness from the same `hcore` (P1).

## 3. Revised theorems
```lean
theorem ihAt_stepPF {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (hT : T1Hyp L P Reach DataOk)
    (hStep : StepStmt L P DataOk) (hSS : ServedShips0Stmt L P Reach DataOk)
    (hPF : PostFactsStmt L P Reach DataOk)
    (D : Nat) (hIH : IHAt L P Reach (D + 1)) (hKI : ChildKeepsInv L P Reach (D + 1)) : IHAt L P Reach D
theorem ih_allPF … (hStep) (hKC : KeepChildStmt L P Reach) (hSS) (hPF : PostFactsStmt L P Reach DataOk)
    (hLim : LimitStmt L) : ∀ D, 1 ≤ D → IHAt L P Reach D ∧ ChildKeepsInv L P Reach D
theorem t1_of_stepPF {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (hStep : StepStmt L P DataOk) (hKC : KeepChildStmt L P Reach)
    (hSS : ServedShips0Stmt L P Reach DataOk) (hPF : PostFactsStmt L P Reach DataOk) (hLim : LimitStmt L) :
    T1Stmt L P Reach DataOk
```
- `t1_of_stepPF'` is `t1_of_stepPF` with `limitStmt_proved` (Gen2T1.lean:127).
- `t1_of_stepPF_kc` is `t1_of_stepPF` with `keepChild_proved` (Gen2KeepChild.lean:358).
- **`ihAt_stepPF` body.** It is Gen2T1.lean:164-183 unchanged, with the topModule conjunct of `designTop` kept
  as `htop` instead of `-`. It then ends:
```lean
  obtain ⟨hnt, hic⟩ := hPF hT q mctx cctx u u' w1 M' M Dg' Dg hc hPq hDq hA (by rw [hdv]; exact hu)
    hIH' hKI' hr hcore hb htop hmods htaken
  exact ⟨hreal, ⟨q, n, hPq, rfl, childShips_congr q n M' (hmods hnt).symm hCS⟩, hic⟩
```
- `ihAt_limit` (:149) and `t1_of_step`'s top-level part (:221-237) do not build a `ShipsRes`, so their text is
  unchanged.

## 4. Projections new → old
| lemma | statement | valid |
|---|---|---|
| `shipsRes_old` | `ShipsRes L P c r → ShipsResOld L P c r := fun h => ⟨h.1, h.2.1⟩` | yes |
| `cacheShips_old`, `invAt_old` | `InvAt L P Reach D w → InvAtOld L P Reach D w := fun h => ⟨h.1, fun c r hR hg => shipsRes_old (h.2 c r hR hg)⟩` | yes |
| `servedP_old` | `ServedP (ShipsRes L P) … → ServedP (ShipsResOld L P) …`, by `servedP_mono (fun _ _ => shipsRes_old)` (Gen2Connect.lean:64) | yes |
| `stepStmt_of_old` | `StepStmtOld L P DataOk → StepStmt L P DataOk`: the trace premise is mapped by `machineTraceLBX_mono` (Connect:47) + `servedP_old` | yes |
| `IHAt` vs `IHAtOld` | stronger hypothesis (`InvAt`) AND stronger conclusion | **incomparable** |
| `ChildKeepsInv`/`KeepChildStmt`/`ServedShips0Stmt` vs old | the invariant is in both pre and post, or the conclusion is stronger | not derivable; re-proved |
| `NoTopStmt` | not implied by `PostFactsStmt` (its premise is `JQC` only) | retired |

## 5. Producer of `PostFactsStmt`: `postFacts_proved (hrows : DataRows DataOk) : PostFactsStmt L P Reach DataOk` (MISSING)
**Run facts:**
| # | lemma (exact shape) | status |
|---|---|---|
| P1 | `machineRunInv_of_coreA (hA) (hr : RunsTo (synthesizeCombinationalCore c [] false) … w (m, d) w') (entry : MachineDefines mctx mref cctx cref c shape) (hw : InvAt L P Reach D w) : ∃ tenv b r w9 w10, RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape) mctx mref cctx cref w9 r w10 ∧ InvAt L P Reach (D + 1) w9 ∧ ∀ res, r = some res → res = (m, d)` | MISSING; copy of `machine_run_of_coreA` (ChildRunA.lean:225) over `core_reads_invA` (:89). Cache half: framed, or `{}` after the depth-0 clear (Elab.lean:5541), via `cacheShips_empty` (MISSING, trivial) |
| P2 | `synthesizeMachineCertified_runsInv`: the conclusion of `synthesizeMachineCertified_runsA` (ChildRunAKids.lean:109-121), with `ChildrenRealA` replaced by `ChildrenShipsI L P Reach shape children := children.length = shape.insts.length ∧ ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧ ((shape.instOrigins.getD k .ord).child? = some y ∨ (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → ShipsRes L P (shape.insts[k]).1 y)))`; premises `InvAt (D+1) w`, `IHAt (D+1)`, `ChildKeepsInv (D+1)` | MISSING. Harness: `mixed_keepsAP` (ChildFrontCP.lean:84) with `htr := translate_keepsInv_of_tele` (Gen2Keep.lean:39). Children: `closeInstsM_runInv`/`closeInstsGM_runInv`, copies of CallsCloseA.lean:64/:89 with each child's value from `synthesizeChild_shipsRes` (KeepChild:329) and its end world from `ChildKeepsInv (D+1)`. No `BodyStepC` needed |
| P3 | `closedBody_kinds_of_run` (ClosedKinds.lean:162): `(closeMachine …).name = ofDecl c ∧ d₀.modules = []` | EXISTING. Premises: `Pkg.ok` (Gen2Pkg.lean:79), `Pkg.body_eq` (:84), and `hC`/`hslots`/`hdomB` from `DataRows` (**MISSING**, see §8 S1) |

**Closing facts** (`CloseCalls`, MachineEntry.lean:948):
| # | fact | supplier |
|---|---|---|
| P4 | `d = designWith children d₀`, `m.name = m₀.name` | EXISTING: `closeInsts_design`/`closeInstsG_design` (CacheCoherentClose.lean:80/:97), `closeInsts_name`/`closeInstsG_name` (CacheCoherentCert.lean:146/:163) |
| P5 | every child top and child-design module is found in `d` as itself | EXISTING: `closeInsts_names` (ChildServe.lean:137) + `closeInsts_acyclic` 4th conjunct (:200); `closeInstsG_names` (MachineInstG.lean:369); then `moduleByName_mem` (HierPremisesBase.lean:123) |
| P6 | `NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body` (`noInstOfB`, checked at Machine.lean:423 and MachineInstG.lean:143) | EXISTING: `closeInsts_acyclic`/`closeInstsG_acyclic` (ChildServe.lean:200/:223) |
| P7 | `closeInsts_kids_inst`/`closeInstsG_kids_inst (h : … = some (m, d)) (hchL : children.length = insts.length) : ∀ c ∈ children, ∃ (i : String) (cs : List (String × Expr)), Stmt.inst c.1.name i cs ∈ m.body` | **MISSING.** This is NOT a check of either closing; it follows from how the instances are built. G: `callGroups_ok` coverage (MachineInstG.lean:193), group key equality `GroupsOk` (:106), `keys_get` (:206), `instStmtG` emitting `.inst mc.name` (Sparkle/IR/MachineInstG.lean:49), `mc = c.1` by P5, then the `isPermOf` check (:128) via `isPermOf_sound` (ReorderInvariance.lean:1550). One-output: `mapM` over `range insts.length` (Machine.lean:400-405), `instStmt` emitting `.inst mc.name` (:286). `hchL` is needed: a child past `insts.length` would join `d'` without an instance. It comes from P2's length conjunct |
| P8 | `mem_designWith` (SharedLeafExt.lean:150) | EXISTING |
| P9 | memory child: `instOrigin_child?_mem` (MachineEntry.lean:882), `memModule_design_modules : (memModule cb aw dw).2.modules = [(memModule cb aw dw).1]` (Srm12Corr.lean:139) | EXISTING |
| P10 | `inst_target_full` (Gen2InstKeep.lean:107) | EXISTING. Audited in Tests/Gen3/InstKeepCheck.lean (dcda5033). The file header (InstKeep:4) still says "NOT BUILT" and is stale |

**Assembly** (`d₀.modules = []` by P3, so every `g ∈ Dg` is, by P8, some child `k`'s top `k.1` or a member of
`k.2.modules`):
- **No calls (`insts = []`):** `Dg = d₀` (P2). Both (i) and (ii) are vacuous: `Dg'.modules = []` by `hmods`.
- **(i), `g = k.1`:** P7 puts an instance of `k.1.name` in `raw.body`. P6 at `raw.name` (P4: `raw.name = m₀.name`)
  gives `g.name ≠ raw.name`.
- **(i), `g ∈ k.2.modules`, `k` a memory child:** `g = k.1` by P9, so the previous case applies.
- **(i), `g ∈ k.2.modules`, `k` an ordinary child:** `T1Hyp.closed` (Defs:204) gives `Reach`. P2 then gives
  `ShipsRes' k`, hence `InstClosed k`, hence an `h` with an instance of `g.name`. `h ∈ Dg` by P5. P6 on `h.body`
  gives `g.name ≠ raw.name`.
- **(ii):** `Dg'.modules = Dg.modules` by `hmods (i)`. Then the same split:
  - `g = k.1`: P7, then P10 with `hb`, gives `h := M'`;
  - `g ∈ k.2.modules`: the `h` from `InstClosed k`, which is in `Dg = Dg'`.
- **Same shape:** the closing's `shape` is `q.d.shape`. This is the `entry` premise of P1, discharged by
  `hT.defines`.

## 6. Instances: the path from the closing to the core's return
The path was read and needs nothing new:
- `synthesizeMachineCertified` returns the closing's value directly (Elab.lean:5252-5264).
- `synthesizeFromConst` returns that `result` after only a `sparkleSubModuleCache` insert (:5321-5324).
- The core returns `doSynth` (:5574-5575). Its `finally` only restores caches.

The Lean supplier is the `∀ res, r = some res → res = (m, d)` conjunct of `machine_run_of_coreA`
(ChildRunA.lean:233-234), which P1 must keep. The only post-passes are the full entry's (:5600-5606), and P10
covers them.

## 7. Cache
- **Initial.** At depth 0 the cache is cleared (Elab.lean:5541), and `CacheShips' {}` holds trivially
  (`cacheShips_empty`, MISSING). T1 itself never needs `InvAt` at depth 0: `ServedShips0Stmt` has `dv w = 0 ∨ …`
  (Gen2T1.lean:118), and `ih_allPF` runs only at `D ≥ 1`.
- **Hit.** The text is unchanged and reads `hw.1.2` (KeepChild:304-305, :345).
- **Insert.** `cacheShips_insert` (:253) and `invAt_insert_runs` (:269) are generic in `ShipsRes`. Their argument
  becomes `ShipsRes'`, which `IHAt'` gives at the run (:321, :355).
- **Rebuild.** `keepChild_proved` (:358) must be RE-ELABORATED but needs no edit. The same holds for
  `stableA_invAt`/`shipsRes_real` (Connect:41/:86) and `keepBody` (Keep:54).
- **Replaced.** `t1_of_step_kc` (:371) calls `t1_of_step` with `NoTopStmt`, so it is replaced by
  `t1_of_stepPF_kc`.
- **Unaffected.** Tests/Gen2/PkgCompat.lean:66 is a local copy. Tests/Gen3/T1Check.lean:13-16 must list the PF
  names.

## 8. UNVERIFIED (not supplied) and stop conditions
- **S1 (stop for P3): `DataRows` has no supplier at generic `DataOk`.**
  - `d₀.modules = []` needs `callsOk q.kD`, `ss.length = slots.length` and
    `∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain`.
  - `DataOkB` (Gen2Data.lean:17-21) has the first two but NOT `hdomB`. `MemParentDataOk.rows` (MemData.lean:16)
    has all three.
  - **Decision needed:** add the `hdomB` row to `DataOkB`, derive it from `ok`, or keep `hrows` as a premise.
- **U1, memory child designs.**
  - In `closeInstsG`, a memory child's design is `[md.1]` (P9), not `[]`. It is NOT `InstClosed` either, since
    `memModule_instFree` (Gen2MemBd.lean:31) means the body has no instance. It is never needed: memory children
    are origin-built (Elab.lean:5237), never cached, and reduce to the top case.
  - In the one-output path, `closeInstsM` calls `synth c` for every entry, whatever its origin (Elab.lean:5210).
    Whether a memory-origin entry can occur with `instFields = []` is unverified. If it can, its result is a
    child of a placeholder name with no `Reach` (Defs:204-205 needs `child? = none`), and so no `InstClosed`.
- **U2, G-ONEOUT-REACH.** Every `closeInstsM` child is a reached name only through `T1Hyp.closed` on `q.d.shape`.
  How the static closure matches the translator's actual calls (G-REACH) is open, as before.
- **U3, the path from the closing to the core's return:** verified by reading (§6). It needs only P1 to keep the
  result conjunct.

## 9. Option A (correct wording)
In the specific top-name collision, some `x ∈ Dg` has `x.name = raw.name` with `x ≠ M'`. There
`ChildShips q n M' Dg` is vacuous, because `moduleByName` is `find?` (Machine.lean:360) and cannot return both
`x` and `M'`. So a bare transport `ChildShips … Dg → ChildShips … Dg'` cannot supply the target in that case
(GPOST_COMPARE §1). This shows nothing about other ways of changing StepStmt or the map, and implies no cost
ordering. GPOST_COMPARE.md:56 ("impossible … whatever the map's property") and :68 ("strictly more") overstate
this and are superseded here.

## 10. Order (no circularity)
1. Make the Defs change and the T1 statements change TOGETHER, after approval. The two must land in one build:
   - `InstClosed`, the 3rd conjunct, the `…Old` copies and §4;
   - `PostFactsStmt`, `ihAt_stepPF`, `ih_allPF`, `t1_of_stepPF(')`, `t1_of_stepPF_kc`;
   - retire `NoTopStmt`/`ihAt_step`/`ih_all`/`t1_of_step(')`/`t1_of_step_kc`, which stop elaborating once the
     conjunct is added (Gen2T1.lean:186).
2. P7, pure.
3. S1 decision, then `DataRows`.
4. P1, P2 (shared with G-SERVED).
5. `postFacts_proved` (§5).

`PostFactsStmt` uses only `IHAt'`/`ChildKeepsInv'` at `dv u + 1`, as binders, which `ih_allPF`'s hypothesis at
`D + 1` supplies. `keepChild_proved` does not use it. So there is no cycle.
