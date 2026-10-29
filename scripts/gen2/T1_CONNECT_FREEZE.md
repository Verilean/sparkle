# M3 lead: the T1 induction-step connection over the A-COMB interface — freeze rev1 (FOR REVIEW)

- **Issue:** `sparkle-gen3-induct`.
- **Plan:** LEAD_UNITS_PLAN.md (cf029631).
- **Status:** read-only survey at cf029631; no Lean. `Defs` = Tools/ShippingGen2Defs.lean.

**Everything here is CONDITIONAL.** The skeleton is conditional on `StepStmt` (M2) and on the premises of §4. It is labelled conditional and is not counted as M2 or M3 progress toward `done`.

## 1. The induction
**Claim.** `ih_all : ∀ D, 1 ≤ D → IHAt L P Reach D ∧ ChildKeepsInv L P Reach D`. It is proved by `key : ∀ k D, sparkleSynthDepthLimit - D = k → …`, in the shape of `childKeepsC_all` (ChildDepthC.lean:94) and `childKeepsP_all_of_tele` (ChildPinC.lean:357).

**Depth bookkeeping.**
- An `IHAt D` run starts with `dv u = D`.
- The core checks the limit, sets the depth to `D + 1` and runs the body (Elab.lean:5465).
- Nested `synthesizeChild` calls therefore start from `InvAt (D + 1)` worlds, covered by `IHAt (D + 1)`.

**Base case `k = 0` (`D ≥ limit`).** `IHAt D` is vacuous by `ihAt_limit` (the core throws at the limit; the limit branch of `core_tripleAC`, ChildCoreC.lean:128-133). `ChildKeepsInv D` follows from `KeepChildStmt` with the vacuous body premise.

**Step `k + 1`.** From `IH := (IHAt (D+1), ChildKeepsInv (D+1))`:
- **`IHAt D` by `ihAt_step`**, for a reached `c`, a world `u` with `InvAt D u`, and a full run:
  1. `synthesizeCombinational_designTop` (DesignWriterRun.lean:69) splits the run: core run `hcore`, `hpost`, and the design move.
  2. `T1Hyp.pkg` gives `q`.
  3. G-SERVED/G-START (`ServedShips0Stmt`) gives the trace with `ServedP (ShipsRes L P)`.
  4. `machineRunJQC_of_closesA` (ServedRealA.lean:94) gives `MachineTaken … (dv u + 1)`.
  5. `StepStmt` gives `∃ n, TopShips ∧ ChildShips q n b Dg`.
  6. `RealChildA.of_jqc` (ChildCacheA.lean:160) and `childShips_congr` (moving `Dg` to the full design, G-POST) give `ShipsRes`.
- **`ChildKeepsInv D`:** `KeepChildStmt D hD (keepBody (D+1) IH.2) IHAt_D`, using `keepBody` (Gen2Keep.lean:54, proved).

**`T1Stmt`.** `Start` gives `JQC 0 w`, so `dv w = 0`. Take `ih_all 1`, then `ServedShips0Stmt` with the depth-0 disjunct, `machineRunJQC_of_closesA` with `Or.inl rfl`, and `StepStmt`. `IHAt 0`/`ChildKeepsInv 0` are never needed.

**Same witnesses.**
- `ids`/`cache` and the served predicate `X` are existential inside `MachineTraceLBX` (TraceX.lean:389-393). So `ServedP`'s `ids`/`cache` ARE the trace's own, and `StepStmt` takes that one trace hypothesis without rebuilding it.
- The same `raw`, `Dg`, `w`, `w1`, `hcore`, `p` and `dv w` are passed to the served-ships lemma and to `StepStmt`.
- The served child's package is unique because `P` is a function, so `ShipsRes`'s `q` = `CallDec`'s `q'`.

## 2. Statements this unit adds (exact proposed types)
```lean
def LimitStmt (L : Laws mref cref) : Prop :=
  ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res) (D : Nat),
    AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet D w → sparkleSynthDepthLimit ≤ D →
    ¬ RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w r w'

def NoTopStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=          -- gap G-POST
  ∀ c (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld) (raw : Module) (Dg : Design),
    Reach c → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, Dg) w1 →
    ∀ x ∈ Dg.modules, x.name ≠ raw.name

def ServedShips0Stmt (L) (P) (Reach) (DataOk) : Prop :=                      -- G-SERVED + G-START
  T1Hyp L P Reach DataOk → ∀ (p : Pkg ι dom) mctx cctx (w w' : Void IO.RealWorld) (raw : Module) (D : Design),
    Reach p.decl → P p.decl = some p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    (dv w = 0 ∨ CacheShips L P Reach (cv w)) →
    IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w' →
    MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc
```
- **`ServedShips0Stmt`** is strictly stronger than the frozen `ServedShipsStmt` (Defs:249), which follows by `Or.inr`. It is needed because `Start` gives only `JQC 0 w`, not `InvAt 0 w`.
  - This is a NEW statement next to the frozen one. `ServedShipsStmt` is not changed.
- **Lemmas:**
  - `ihAt_limit (hL : LimitStmt L) (hD : limit ≤ D) : IHAt L P Reach D`;
  - `childShips_congr (h : D1.modules = D2.modules) : ChildShips q n mc D1 → ChildShips q n mc D2` (`ChildShips` reads `Dc.modules` only);
  - `ihAt_step` (step `k + 1` above);
  - `ih_all`.

## 3. The kernel-checkable skeleton (conditional)
```lean
theorem t1_of_step {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk) (hKC : KeepChildStmt L P Reach)
    (hSS : ServedShips0Stmt L P Reach DataOk) (hNT : NoTopStmt L Reach) (hLim : LimitStmt L) :
    T1Stmt L P Reach DataOk
```
It uses `keepBody`, `machineRunJQC_of_closesA`, `synthesizeCombinational_designTop`, `RealChildA.of_jqc`, `ihAt_limit`, `ihAt_step`, `ih_all` and `childShips_congr`. `LimitStmt` is discharged in the same unit, by the prefix of `core_tripleAC`.

**Deliverable of this unit:**
- `t1_of_step` and `limitStmt_proved`, built;
- an axiom audit;
- a result doc.

## 4. The premises the skeleton leaves, and their units
| premise | gap | unit / existing pieces |
|---|---|---|
| `StepStmt` | M2-b | `sparkle-gen2-step` |
| `KeepChildStmt` | G-KEEP-CHILD / G-EXC | port of `childKeepsP_of_body` (PinC:346) with `synthesizeChild_tripleP` (:255), `core_tripleAP` (:133), `full_tripleAP` (:207). Missing: `core/full_tripleAInv`, `synthesizeChild_tripleInv`, `invAt_insert_runs` |
| `ServedShips0Stmt` | G-SERVED / G-START | copies of the served-real chain, with `JQC → InvAt` and `RealChildA → ChildrenShips`: `cacheShips_insert`, `synthesizeChild_ships` (hit/miss), `ChildrenShips`, `closeInstsGM_ships`, `closeInstsM_ships`, `synthesizeMachineCertified_runsS`, `core_reads_invAt`, `soundX_ships_ran` (copy of ServedRealA:117); reused: `cacheInvA_insert`, `jqc_insert_runs`, `synthesizeChild_realA`, `servedP_mono` |
| `NoTopStmt` | G-POST | new-boundary analogue of `fresh_post` (CacheCoherentRun.lean:218); not proved on the new boundary |

## 5. Findings that change the plan (recorded; amendments reviewed before use)
1. **G-ONEOUT-REACH (new gap).**
   - **The difference.** `closeInstsGM` synthesises only `child? = none` calls (Elab:5235-5238), which matches `T1Hyp.closed`. `closeInstsM` (one-output parents, Elab:5210) synthesises EVERY instance, whatever its origin.
   - **The gap.** With `ShipsRes`, an origin-tagged instance of a one-output parent has neither `Reach` nor `Served1P`'s left disjunct.
   - **Ways out:** prove `instFields = [] → ∀ k, child? = none` (from the reader), or widen `T1Hyp.closed` for one-output parents. To be decided in the G-SERVED freeze.
2. **Route-indexed `T1Hyp`** (from ROUTE_CENSUS.md, 48704c38). `T1Hyp.defines`/`closed` make every reached callee a machine-route declaration, so a gate child cannot be reached.
   - **This unit:** keeps `T1Hyp` as frozen.
   - **What the skeleton therefore covers:** machine-route trees only.
   - **To be proposed:** a route-indexed `T1Hyp` with M4's first route unit. FG is not narrowed: T1 is not FG.
3. **G-MEMO is closed for REACHED names** by `T1Hyp.defines`/`closes`:
   - `MachineDefines` excludes the gates (MachineEntry:2345), and `MachineClosesAtA` (RunAKids:158) gives a result.
   - The memo branch (Elab:5334-5338) comes after the machine branch returns.

   The memo stays an M4 item for other routes.
4. **A-COMB.** The connection treats `ShipsRes` as opaque, so nothing gets harder here. The burden is inside `StepStmt`: per served `mc` cases (S3), and G-LIFT for both branches.
5. **The `T1Hyp.dec` split** (G3GEN_CALL_PLAN §3). If it is adopted, `ihAt_step` also needs a run-local `DecRunStmt`. That is not in this skeleton.

## 6. Isolation
- **Worktree:** the skeleton is built in its own worktree from the reviewed base (1fdbc18d or a later reviewed head).
- **Files:** one new file `Tools/ShippingGen2T1.lean` plus its registration. No edit of Defs, except new `def`s in that new file.
