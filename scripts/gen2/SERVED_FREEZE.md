# G-SERVED / G-START freeze rev1: `ServedShips0Stmt` producer (FOR REVIEW; F1 + conditional F2 written, NOT built)

## Changelog
- **rev1** (review of rev0 96cbd548, changes_requested). Decisions recorded:
  - D1: R-ROW may be implemented as a CONDITIONAL intermediate (premise `hrow`).
  - D2: the 4 DataBridge declarations are copied text-identically into a local file. At integration they are unified,
    with an `rfl` bridge.
  - D3: one canonical `Tools/ShippingGen2ServedRun.lean` with one owner. Post imports it.

  Fixes:
  - (a) A census, or one concrete package, is NOT supply of the universal `hrow`, and is NOT its non-vacuity
    (§2.3, §4 C5).
  - (b) The memory branch is limited to the finding "derivation route not supplied" (§2.1).
  - (c) The combined-Pkg `.comb` branch is kept. How it is handled is in §1.6.
  - (d) The complete Lean types of `SoundXAt`, `hreach`, `hord1` (and of every new F1/F2 statement) are FIXED in §1.5
    before code.
  - (e) F1 and the conditional F2 proceed before post completes (§3).
  - (f) No result that takes `hrow` completes G-SERVED, T1 or FG (§2.3).
  - (g) post/trace are re-verified at the integration SHA (§4.4).

  Files written in this revision (no build; see §6):
  - `Tools/ShippingGen2ServedRun.lean` (F1)
  - `Tools/ShippingGen2Served.lean` (F2, conditional)
  - `Tools/ShippingGen2ServedDataBridgeCopy.lean` (D2)
  - `Tests/Gen3/ServedCheck.lean` with its local helper `Tests/Gen3/ServedExpectedType.lean`
- rev0 (96cbd548): design only.

- **Issue:** `sparkle-gen3-served`. It depends on `sparkle-gen3-post` (doing) and `sparkle-gen3-keepchild` (done).
- **Base:** `par/gen3-induct` 96cbd548. Reference only: `par/gen2-spec` e134c63a, labelled `[g2s]`. Its DataBridge
  file was last changed at 48775f38 and its CombPkg file at 682dbb1c.
- **Rule kept:** no new semantic premise and no FG narrowing. No edit of Defs, T1, KeepChild, the compiler or the
  lakefile; only new files. The one extra premise is `hrow`. It is a decided per-declaration Bool data row, EXPLICIT,
  and it makes every result that takes it conditional (§2.3).

## 1. The target and the chain

### 1.1 Frozen statement (Tools/ShippingGen2T1.lean:112-122, unchanged)
`ServedShips0Stmt L P Reach DataOk := T1Hyp L P Reach DataOk → ∀ p mctx cctx w w' raw D, Reach p.decl →
P p.decl = some p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → (dv w = 0 ∨ CacheShips L P Reach (cv w)) →
IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
RunsTo (synthesizeCombinationalCore p.decl [] false) … w (raw, D) w' →
MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc`.

`ShipsRes` (Defs:135-136) has 3 conjuncts: `RealChildA ∧ ∃ q n, ChildShips ∧ InstClosed`. Consumers:
- `ihAt_stepPF` (T1:185);
- `t1_of_stepPF` (T1:241);
- `servedShipsStmt_of_0` (T1:136).

### 1.2 The existing served-real chain
Unchanged from rev0. The rows are:
- (a) `core_reads_invA` (ChildRunA:89)
- (b) `machine_run_of_coreA` (:225)
- (c) `MachineRunJQC` (ServedRealA:90)
- (d) `synthesizeChild_realC` (DepthC:275)
- (e) `closeInstsM_realC` (DepthC:283)
- (f) `closeInstsGM_realC` (RunAKids:59)
- (g) `ChildrenRealA` (RunAKids:51)
- (h) `synthesizeMachineCertified_runsA` (RunAKids:109)
- (i) `…_soundRA_ranA` (ServedRealA:116)
- (j) `machine_trace_lets_of_streamBRA_ranA` (ServedRealATrace:36)
- (k) `machine_traceL_of_data_causalRA_ranA` (ParentSeqComposedA:23)
- (l) `machine_traceL_of_loop_causalRA_ranA` (Gen2Loop:37)
- (m) `genTrace` (QuadComposed:156), `genTraceL` (Gen2Loop:213) and `Pkg.trace` (Gen2Pkg:103)

### 1.3 Correspondence (F1 = `Tools/ShippingGen2ServedRun.lean`, F2 = `Tools/ShippingGen2Served.lean`)
| source | new name / file | change |
|---|---|---|
| `tripleC_clear` (CacheA:218) | `cacheShips_empty`, `tripleInv_clear` / F1 | `cv = {}` gives both cache halves |
| (a) | `core_reads_invAt0` / F1 | peel walk copied; after the clear (D = 0) or from the start (nested), the stable invariant is `InvAt` |
| — | `synthesizeFromConst_machine_invAt` / F1 | copy of ChildRunA:200 at `InvAt` |
| (b) | `machineRunInv_of_core0` / F1; `machineRunInv_of_coreA` (= GPOST P1, the `InvAt` form, by `Or.inr hw.2`) | copy |
| (c) | `MachineRunInv`, `machineRunJQC_of_runInv`, `machineRunInv_of_closes0` / F1 | copy |
| (d) | `synthesizeChild_ships` / F1 | value: hit or miss decomposition (as KeepChild:331); end world: `ChildKeepsInv D`; no `BodyStepC` |
| (g) | `ChildrenShipsI` / F1 | GPOST P2 text verbatim |
| (e), (f) | `closeInstsM_ships`, `closeInstsGM_ships` / F1 | `mapM_hoareA`/`mapM_hoare` at `InvAt D` with (d) |
| (h) | `synthesizeMachineCertified_runsS` / F1 (= GPOST P2 `…_runsInv`, D3: the issue names are canonical) | harness `mixed_keepsAP` with `translate_keepsInv_of_tele` |
| (i) | `soundX_ships_ran` / F2 | `hreach`, `hord1` (§1.5); the general closing's memory case by `MemChildren` |
| (j) | `machine_trace_lets_of_streamBRX` / F2 | X-generic; the run is replaced by `hX : SoundXAt …` |
| (k), (l) | `machine_traceL_of_data_causalX`, `machine_traceL_of_loop_causalX` / F2 | pass `hX` |
| (m) | `genTraceX`, `genTraceLX`, `Pkg.traceX` / F2 | cases `gen`/`loop` on this base; `.comb`: §1.6 |
| producer | `servedShips0_proved` / F2 | CONDITIONAL on `hrow` |
| T1 corollary | `t1_of_stepPF_served` / F2 | CONDITIONAL on `StepStmt`, `PostFactsStmt`, `hrow` |

### 1.4 Producer assembly
1. `machineRunInv_of_closes0` at `JQC (dv w) w` and the cache disjunct gives `MachineRunInv … (dv w + 1)`.
2. `soundX_ships_ran` at `n := dv w + 1` with `hIH`/`hKI`, using:
   - `hreach := fun k hk hn => hT.closed p.decl hR p hP k hk hn`;
   - `hord1 := fun hf k hk => hord_of_row (hrow p hDp) hf k hk`, where `hDp : DataOk p` comes from `hT.pkg` and
     `P p.decl = some p`.
3. `Pkg.traceX p hX`.

The body's own translator calls keep `InvAt` by `ChildKeepsInv` alone (G-REACH is not used).

### 1.5 FIXED Lean types (rev1; the code and `Tests/Gen3/ServedCheck.lean` follow this text)
Common binders, in this order wherever they occur:
```lean
{ι : Type} {dom : ι → DomainConfig}
{mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
(L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
{mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
```

Definitions:
```lean
def SoundXAt (X : List FVarId → IO.Ref (ExprStructMap String) → Prop) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  ∀ (bsIn slotBs letBs : List (Name × MixedGateBinder)),
    shape.binders = bsIn ++ slotBs ++ letBs → shape.layout.lets = letBs.length →
    PositiveBinders shape.binders → (∀ b ∈ slotBs, b.2 ≠ .domain) → (∀ b ∈ letBs, b.2 ≠ .domain) →
    Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2) shape.layout.slots slotBs →
    (∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true) →
    (shape.layout.outs.map (·.name)).Nodup →
    MachinePreservesX X declName shape bsIn slotBs letBs m dsn

def MachineRunInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (mctx : Meta.Context)
    (cctx : Core.Context) (n : Nat) (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (tenv : Lean.Environment), ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧ InvAt L P Reach n w9

def ChildrenShipsI (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (shape : MachineShape)
    (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → ShipsRes L P (shape.insts[k]).1 y)))
```

`hreach` and `hord1` (binders of `soundX_ships_ran`, after `ran`, `hIH`, `hKI`):
```lean
(hreach : ∀ k (hk : k < shape.insts.length),
  (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
(hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
  (shape.instOrigins.getD k .ord).child? = none)
```

Statements (common binders elided as `⋯`):
```lean
theorem synthesizeChild_ships ⋯ {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : InvAt L P Reach D w) (hIH : IHAt L P Reach D) (hKI : ChildKeepsInv L P Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    RealChildA L.O n r ∧ (Reach n → ShipsRes L P n r) ∧ InvAt L P Reach D w'
theorem machineRunInv_of_closes0 ⋯ {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA L.O mctx cctx declName shape)
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w)) :
    MachineRunInv L P Reach mctx cctx (D + 1) declName shape m d
theorem synthesizeMachineCertified_runsS ⋯ {n : Nat} {tenv : Lean.Environment}
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n) {b : Bool} {declName : Name}
    {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design} {w w' : Void IO.RealWorld}
    (hw : InvAt L P Reach n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
          ChildrenShipsI L P Reach shape children))
theorem soundX_ships_ran ⋯ {n : Nat} {declName : Name} {shape : MachineShape}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (ran : MachineRunInv L P Reach mctx cctx n declName shape m d)
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n) (hreach : …) (hord1 : …) :
    SoundXAt (ServedP (ShipsRes L P) declName shape m d) declName shape m d
theorem servedShips0_proved {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2ServedDataBridgeCopy.OneOutNoMemRow q = true) :
    ServedShips0Stmt L P Reach DataOk
theorem t1_of_stepPF_served {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2ServedDataBridgeCopy.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk) (hPF : PostFactsStmt L P Reach DataOk) :
    T1Stmt L P Reach DataOk
theorem Pkg.traceX {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom)
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop} {m : Sparkle.IR.AST.Module} {design : Design}
    (hX : SoundXAt X p.decl p.d.shape m design) :
    MachineTraceLBX X p.decl p.d m design dom p.src p.extS p.extBS p.lsrc
```
The remaining F1 statements are copies of their sources with the substitutions of §1.3:
- `core_reads_invAt0`
- `synthesizeFromConst_machine_invAt`
- `machineRunInv_of_core0`, and `machineRunInv_of_coreA` (GPOST P1's text)
- `closeInstsM_ships`, `closeInstsGM_ships`

`(j)`-`(l)` take `hX : SoundXAt X declName d.shape m design` in place of `O, hB, hA, htr, ran`. Every other binder is
verbatim.

### 1.6 The combined-Pkg `.comb` branch (fix c)
- On `[g2s]`, `Pkg = gen | loop | comb` (Tools/ShippingGen2Pkg.lean:33-36). `.comb` holds a `CombPkg`
  (Tools/ShippingGen2CombPkg.lean). Its `Pkg.trace` case is `combTrace`, which goes through
  `machine_traceL_of_comb_callsRA_ranA` (CombPkg:63-83). That in turn is (j) at the stream witness
  `⟨fun _ => inits, rfl, hnext, hres, lets⟩`.
- On this base (96cbd548), `Pkg` has only `gen | loop`. So `Pkg.traceX` here has exactly those two cases, and `.comb`
  cannot be written on this branch (`CombPkg` does not exist here).
- **It is NOT dropped.** At integration with `[g2s]`, the exhaustive `cases p` of `Pkg.traceX` stops elaborating until
  two things are added:
  - (i) `machine_traceL_of_comb_callsX`: the text of CombPkg:63-83 with `O hB hA htr ran` replaced by `hX`, and the
    call to `machine_trace_lets_of_streamBRA_ranA` replaced by `machine_trace_lets_of_streamBRX … hX`. The witness is
    verbatim;
  - (ii) the case `| comb p => exact machine_traceL_of_comb_callsX (declName := p.decl) p.d dom p.inits p.src
    p.facts hX`.
- This is a mechanical copy of the same kind as (k)/(l). It is listed in §4.4 as an integration obligation. Until then,
  `servedShips0_proved` is a statement about the 2-constructor `Pkg` of this base only.

## 2. G-ONEOUT-REACH

### 2.1 Finding (fix b: limited to "derivation route not supplied")
- `closeInstsM` (Elab:5206-5219) calls `synth c` for every entry, whatever its origin. It is selected when
  `instFields.isEmpty` (:5261-5262).
- `Served1P` (Defs:231-240) asks, for every served entry, one of:
  - `child? = some md ∧ mc = md.1`, or
  - `ShipsRes`.
- `ShipsRes` is available only under `Reach (insts[k]).1` (`IHAt`/`CacheShips`). `T1Hyp.closed` gives `Reach` only
  for `child? = none`.
- So (i)'s one-output case needs `hord1` (§1.5).
- **Finding:** no derivation route of `hord1` is supplied.
  - Not from `T1Hyp`: `.dec` does not give it, since `MemDec` is vacuous for an empty `ι`.
  - Not from `MachineDefines`: the reader route is R-READ.
  - Not from the run: the run route is R-RUN.
- This revision does not claim that a memory-origin entry with `instFields = []` occurs in a successful compilation,
  nor that it cannot occur. That question is part of the unsupplied derivation.

### 2.2 Routes (rev0 table kept)
| route | status |
|---|---|
| R-ROW (D1) | `hrow`; implemented as CONDITIONAL intermediate |
| R-READ | blocked: reader partial; fuel candidate not switched |
| R-RUN | needs an environment premise; rejected |
| R-WIDEN | edits frozen `T1Hyp`; rejected |
| R-COMP | compiler change; user decision |

The row is used through local copies of `noMemRowS`/`OneOutNoMemRow`/`hord_of_rowS`/`hord_of_row` (D2, §5).

### 2.3 Status of everything that takes `hrow` (fixes a, f)
- `servedShips0_proved` proves `(∀ q, DataOk q → OneOutNoMemRow q = true) → ServedShips0Stmt …`. It is an
  INTERMEDIATE. It is NOT `ServedShips0Stmt` at the abstract `DataOk`.
- `t1_of_stepPF_served` has one premise more than `T1Stmt`'s skeleton premises.
- Neither completes G-SERVED, T1/M3 or FG while `hrow` is unsupplied.
- **Supply** of `hrow` means a proof for every package of every successful compilation (or a `DataOk` that is shown to
  imply it without narrowing FG). That is the open G-DATA coverage obligation, tracked under
  `sparkle-gen3-data-supply`. None of the following is supply:
  - a census of rows over a corpus (measured or not);
  - one concrete package whose row decides `true`;
  - a synthetic shape.
- **Non-vacuity** of `hrow` is also NOT shown by one instance. The check file contains a SINGLE-INSTANCE control
  (§4 C5), labelled as such: `hrow` holds at `DataOk := (· = leaf16Pkg)`. It shows only that the premise is not
  contradictory at that one point.
- Making the row part of `DataOkB`/`T1Hyp` is NOT approved and is not done.

## 3. Interface to G-POST (fix e)
- **F1 is canonical** (D3). Post imports `Tools.ShippingGen2ServedRun` and uses:
  - P1 = `machineRunInv_of_coreA` (GPOST text) / `machineRunInv_of_core0`;
  - P2 = `synthesizeMachineCertified_runsS` with `ChildrenShipsI`, `closeInstsM_ships`, `closeInstsGM_ships`,
    `synthesizeChild_ships`.

  GPOST_FREEZE's names `…_runsInv`/`closeInsts(G)M_runInv` denote these lemmas. One owner edits F1; post does not
  copy it.
- **Unconditional on post:** F1 (no `hrow`), and F2's `servedShips0_proved` under `hrow`. Only
  `t1_of_stepPF_served` also needs `PostFactsStmt` (and `StepStmt`).
- **Acceptance** of `sparkle-gen3-served` still waits for `sparkle-gen3-post` done.

## 4. Staging, controls, audit, build

### 4.1 Stages
- S0: rev1 reviewed.
- S1: F1 (this revision).
- S2: F2 (this revision, conditional).
- S3: `Tests/Gen3/ServedCheck.lean`, lakefile entries (listed in §6; the lakefile is NOT edited by the coder of this
  revision), and `SERVED_RESULT.md` after the build.

### 4.2 Controls (`Tests/Gen3/ServedCheck.lean`)
- **C1 expected types.** Mechanical binder-by-binder comparison (`checkExpected`, local copy of `[g2s]`
  Tests/Gen3/ExpectedType.lean as `Tests/Gen3/ServedExpectedType.lean`) of these against independent `Expected…`
  statements written from §1.5:
  - `SoundXAt`, `MachineRunInv`, `ChildrenShipsI`;
  - `synthesizeChild_ships`, `machineRunInv_of_closes0`, `synthesizeMachineCertified_runsS`, `soundX_ships_ran`
    (incl. `hreach`, `hord1`);
  - `servedShips0_proved`, `t1_of_stepPF_served`, `Pkg.traceX`.

  Mutants must be rejected (`checkMutant`):
  - `SoundXAt` without `outsNodup`;
  - `ChildrenShipsI` without the `Reach →` guard;
  - `soundX_ships_ran` with `hreach` lacking its `child? = none` antecedent;
  - `soundX_ships_ran` without `hord1`;
  - `servedShips0_proved` without `hrow` (= claiming the unconditional statement);
  - `t1_of_stepPF_served` without `hPF`.
- **C2** `example : T1Stmt … := t1_of_stepPF_served L P Reach DataOk hrow hStep hPF`. Its premises are exactly `hrow`,
  `StepStmt`, `PostFactsStmt`.
- **C3** old boundary: `servedRealA_of_servedP shipsRes_real` applied to `soundX_ships_ran`'s `X`, through
  `machineTraceLBX_mono`.
- **C4** rows on shapes (copies of the `[g2s]` DataBridgeCheck shapes):
  - positive: synthetic one-output shape with one `.ord` entry;
  - negative: `memShape0`;
  - implication form: `memShape1`;
  - out of range: `memShapeX`.
- **C5** SINGLE-INSTANCE control (fix a): `leaf16Pkg` (Tests/Gen2/LeafInstance.lean) has row `true`, so `hrow` holds
  at `DataOk := (· = leaf16Pkg)`. Labelled in the file as one instance only: not supply, not coverage, not
  non-vacuity of the universal premise.
- **Audit:**
  - `#print axioms` of every new root, plus `checkAxioms` (`[propext, Classical.choice, Quot.sound]` or a subset);
  - no `sorry`/`axiom`/`native_decide`.

### 4.3 Build (to be run by the integrator; NOT run in this revision)
```
kjob -N sparkle-dev run --issue sparkle-gen3-served --name g3sv-<sha8> -m 12Gi -c 4 -- kjob lake build \
  Tools.ShippingGen2ServedDataBridgeCopy Tools.ShippingGen2ServedRun Tools.ShippingGen2Served \
  Tests.Gen3.ServedExpectedType Tests.Gen3.ServedCheck
```
Heartbeat risk: (j)-(l) keep `maxHeartbeats 2000000`.

### 4.4 Integration plan (fix g; post/trace re-verified at the integration SHA)
At the combined SHA (this branch + `sparkle-gen3-post` + `[g2s]` Pkg.comb/DataBridge), in one commit range:
1. **D2 unify.** Delete the copy file. Import `Tools.ShippingGen2DataBridge` instead.
   - Before deleting, a one-off check file proves the 4 `rfl` bridges:
     - `Tools.ShippingGen2ServedDataBridgeCopy.noMemRowS = Tools.ShippingGen2DataBridge.noMemRowS`;
     - `…OneOutNoMemRow = …OneOutNoMemRow` (as functions at every `ι dom`);
     - the 2 theorem statements, compared with `checkExpected`.
   - Then retarget `servedShips0_proved`'s `hrow`.
2. **`.comb`.** Add `machine_traceL_of_comb_callsX` and the `comb` case of `Pkg.traceX` (§1.6).
3. **Post.** Post's file imports F1 and uses P1/P2 from it. No second copy.
4. **Re-elaborate** at the exact integration SHA, with no reuse of evidence from another SHA:
   - F1, F2, `Tests.Gen3.ServedCheck`;
   - `Tools.ShippingGen2PostFacts`, `Tests.Gen3.T1Check`;
   - `Tools.ShippingGen2KeepChild`, `Tools.ShippingGen2Pkg`;
   - `[g2s]` `Tests.Gen2.DataBridgeCheck`.
5. Record exit codes and the `#print axioms` output in `SERVED_RESULT.md` with that SHA.

## 5. Decisions (rev0 §5, decided)
- **D1:** R-ROW as a conditional intermediate.
- **D2:** text-identical local copies in `Tools/ShippingGen2ServedDataBridgeCopy.lean`.
  - Namespace `Tools.ShippingGen2ServedDataBridgeCopy`.
  - Header: source `[g2s]` path, the SHA of its last change (48775f38) and the reference SHA (e134c63a).
  - Unify + `rfl` at integration (§4.4).
- **D3:** F1 canonical, one owner, the issue names.
- **Stop (report, do not patch):**
  - a copy that fails to elaborate with only the listed substitutions;
  - `hX` failing to match `synthesizeMachineCertified_soundX`'s callback;
  - any need for `BodyStepC`/`Nonempty ι`/a new semantic premise.

## 6. Not claimed / status
- F1, F2, D2 copy and checks are WRITTEN BY READING ONLY. None was elaborated (no lake/lean run in this revision).
  Every proof text is a substitution copy of a built source. Any elaboration failure is a STOP item for the build
  round.
- G-ONEOUT-REACH remains a conditional premise. `hrow` is unsupplied, and its coverage is unmeasured.
- Still open:
  - G-REACH;
  - G-POST assembly (P3, DataRows, U1/U2);
  - `StepStmt`/M2, G-LIFT, route-indexed `T1Hyp`, FG.
- `RealChildA` is history, not freshness or runtime fit. No T1/M3/G-SERVED completion is claimed.
- lakefile entries needed (NOT added here):
  - `Tools.ShippingGen2ServedDataBridgeCopy`
  - `Tools.ShippingGen2ServedRun`
  - `Tools.ShippingGen2Served`
  - `Tests.Gen3.ServedExpectedType`
  - `Tests.Gen3.ServedCheck`
