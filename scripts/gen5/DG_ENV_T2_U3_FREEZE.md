# DG-ENV T2 unit U3 freeze: per-field aggregation of the closed `FramedA` rows, class D re-survey, what `QuietStrength` / C0 still lack (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r8` 756e6662 (U3 freeze, reviewer changes_requested R1 + 3 wording points; this revision r9 answers them). U2 approved at ec02705c.
Extends `scripts/gen5/DG_ENV_T2_FREEZE_R3.md` (rev3.1) and `scripts/gen5/DG_ENV_T2_U2_FREEZE.md`. Nothing here adds a law, a `Laws` /
`RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, a premise with new content, or a shared definition; nothing narrows FG or
strengthens `GenWF`; nothing supplies C0 / QuietStrength / AdmDown / Start L′ / FG. Every theorem below is CONDITIONAL: the cell premises
(`ReadWorld`, `SetFrame`, `SetGet`, distinctness), `QuietStrength L L′ env₀` and `AdmDown L L′` are hypotheses. "未供給 / この調査で経路未発見"
below is a result of THIS survey (what was read at ec02705c and probed in this Pod, Lean 4.32.1), not a claim of impossibility.

## 0.0 Revision r9 (answers to the review of 756e6662)
* **R1 (choice made: E4 is a general lemma about an ARBITRARY quiet predicate).** E4 is now `admCtx_down_of_none` over any `q q' : Void IO.RealWorld → Prop`; its statement
  and proof mention no `Laws` / `RefLawsAOps` / `RefLawsATele` / `T1Hyp` / `T1HypND` constant. The instantiation `q := L.O.quiet`, `q' := L'.O.quiet` is done at the use site and is covered by a
  separate "quiet-only" mode of the closure walker (§7): there ONLY `Laws.O` and `RefLawsAOps.quiet` are allowed; every law-bearing field (`RefLawsAOps.<other>`, `Laws.T`, `RefLawsATele.*`,
  `T1Hyp.*`, `T1HypND.*`), every recursor and every raw projection stays forbidden. So E1-E3 and E4 are no longer under one rule: E1-E3 and E4 are law-free roots (no `Laws` constant at all), the
  8 F roots are "field roots" (the allowed set is exactly `Laws.O`, `RefLawsAOps.quiet`, the row's own field), and the E4 instantiation fixture is a "quiet-only" positive control.
* **Wording.** "40 − 13 = 27" is the number of `FramedA` constructors left after removing the 13 `DRow` constructors (a constructor count). It is NOT a proof that the 27 actions are
  mutually non-overlapping as `MetaM` values, and NOT a proof that each of the 27 rows has a supplier of `¬ DRow p`. In §3.4 and §6 statements of the form "does not follow" / "only a T1 would close"
  are limited to: this route supplies nothing for them (未供給 / この調査で経路未発見).
* **Kept.** Scratch probes are not acceptance evidence. `L′`, `CellPrem`, `AdmDown` (beyond `canUnfold? = none`), `QuietStrength`, C0 stay unsupplied, and are kept distinct from each other (§6).

## 0. Findings (summary)
1. **Laws fields, 13 (`RefLawsAOps` 9 + `RefLawsATele` 4).** With U1 + U2 the env part of `L′` (the fields of `L′` whose `quiet` is
   `quiet ∧ ReadsAt env₀ cref`, `QuietStrength`) has: **closed 7** (`frameT excOk cacheSetQ depthSetQ frame cacheSet depthSet`), **partly closed 1**
   (`frameQ`: 27 of the 40 `FramedA` constructors), **not closed 5** (`diag telescope lamTelescope localDecl letDecl`). 7 + 1 + 5 = 13.
   "Closed" means: the field's statement at `L′` (with `L′.O.quiet` for `quiet`) follows from the same field of `L`, `QuietStrength`, `AdmDown` and
   (for the `quiet`-keeping ones) the named cell premise `CellPrem`; it is not a proof that the premises hold.
2. **`Throws` (field `frameT`) closes**: `Throws.err` is U2 A2 (`throwError`); `Throws.coreErr` (`liftM (throwError msg : CoreM α)`) closes from
   `ReadWorld cref` by the shape of U2-9 (probe, §2). In rev3.1 this row was "candidate, unchecked".
3. **`FramedA` 40 = 27 closed + 13 class D.** 27 = B 13 + B′ 8 + C 6 (U1 + U2). The 13 D constructors are exactly `ioEnv monoMs mkExprCache localMk whnf
   inferType isClass? whnfUntil instantiateForall mkLambdaFVars mkAppM unfoldDefinition? reduce`. Re-survey (§3): each reaches opaque / partial
   constants for which no premise name exists; no row moved out of D.
4. **`Diag`, the four telescope fields, `AdmCtx` / `InertUnfold`:** re-surveyed with the U1 / U2 parts available (§3); no route found; the stopping constants
   are recorded. `AdmDown` is derivable only for contexts with `canUnfold? = none` (existing `admCtx_none`); that is a fact about those contexts,
   not a supply for FG, which must also cover callbacks (narrowing FG is excluded).
5. **`QuietStrength` (an `L′`) is not obtained**, `C0` is not obtained: §6 lists, row by row, what is still missing.

## 1. Field table (Laws fields; `L′` = the bundle with `L′.O.quiet w ↔ L.O.quiet w ∧ ReadsAt env₀ cref w`)
`Mix` = the field theorem below needs `hq : QuietStrength L L′ env₀` and `hd : AdmDown L L′` (always), and `CellPrem` when marked.
| # | field | what its statement at `L′` needs | U3 status | theorem |
|---|---|---|---|---|
| 1 | `diag` | env frame of the 9 `Diag` constructors | **not closed**: 未供給 / この調査で経路未発見 (§3.3) | — |
| 2 | `frameT` | env frame of `Throws` (2 constructors) | **closed**, `CellPrem` | F-frameT |
| 3 | `excOk` | none (conclusion is `OkExc`) | **closed**, env-free | F-excOk |
| 4 | `frameQ` | env frame of each `FramedA` constructor | **partly**: 27 / 40 closed, 13 class D open | F-frameQ (hypothesis `¬ DRow p`) |
| 5 | `cacheSetQ` | env frame of `sparkleChildCache.set v` | **closed**, `CellPrem` | F-cacheSetQ |
| 6 | `depthSetQ` | env frame of `sparkleSynthDepth.set v` | **closed**, `CellPrem` | F-depthSetQ |
| 7 | `frame` | none (conclusion `cv/sv/dv`) | **closed**, env-free | F-frame |
| 8 | `cacheSet` | none | **closed**, env-free | F-cacheSet |
| 9 | `depthSet` | none | **closed**, env-free | F-depthSet |
| 10-13 | `telescope lamTelescope localDecl letDecl` | stability premise of `L′` is weaker than `L.T`'s; telescope wrappers reach opaque partial constants | **not closed**: 未供給 / この調査で経路未発見 (§3.4) | — |
Counting rule: per Laws field; closed 7 (rows 2, 3, 5, 6, 7, 8, 9), partly 1 (row 4), not closed 5 (rows 1, 10-13). Env-free rows (3, 7, 8, 9) use no U1 / U2
part: they need only `quiet′ ⇒ quiet` (from `QuietStrength`) and `AdmCtx quiet′ ⇒ AdmCtx quiet` (`AdmDown`), so they are Q-series transport, not env frames.
The `quiet` component of `RefLawsAOps` is given by the premise `QuietStrength`, not built.

## 2. Probes (scratch files, NOT committed, NOT acceptance evidence; Lean 4.32.1, this Pod)
* `Throws.coreErr`: `(liftM (throwError msg : CoreM α) : MetaM α)` at the applied world equals, by `rfl`, `.error e (getW cref w)` for some `e`
  (the shape of `envFrameEnd_fvarThrowUnknown`); `ReadWorld cref` closes it. Accepted.
* The aggregate theorem over the `FramedA` constructors (case split, 40 cases; the 13 D constructors discharged by `¬ DRow p`, the 27 others by the
  U1 / U2 lemma plus `CellPrem`) and the 8 field theorems of §4 elaborated and were accepted in a scratch file (no `sorry`).
* Reachability (value closure of definitions, stopping at `opaque` / `axiom`; types and theorems not followed; script not committed): see §3.

## 3. Re-survey of the open rows (what stops the unfolding)
Method: for each operation, the opaque / axiom constants reachable through definition bodies. Pure data primitives (`mixHash`, `Expr.mkData`,
`PersistentHashMap.insertAux`, `String.*`, …) do not touch the world and are omitted. World-relevant stops are listed.

### 3.1 Allocation and OS prims (D: `mkExprCache localMk ioEnv monoMs`)
`IO.mkRef` reaches `ST.Prim.mkRef` (opaque); `IO.getEnv` is opaque; `IO.monoMsNow` is opaque. The existing cell premises (`ReadWorld`, `ReadKeeps`,
`SetGet`, `SetFrame`) talk about `ST.Prim.Ref.get/set` of a given ref; none talks about allocation or an OS call. This survey found no premise name
that applies. 未供給 / この調査で経路未発見.

### 3.2 Meta library (D: `whnf inferType isClass? whnfUntil instantiateForall mkLambdaFVars mkAppM unfoldDefinition? reduce`)
| operation | world-relevant stops (opaque / partial) |
|---|---|
| `whnf`, `inferType` | themselves (`opaque`) |
| `isClass?` | `isClassQuick?`, `isClassExpensive?` (private, partial), `Ref.get/set` |
| `whnfUntil` | `whnfHeadPred` (opaque) |
| `instantiateForall` | `instantiateForallAux` (private, partial) |
| `mkLambdaFVars` | `MetavarContext.MkBinding.elim` (via `WellFounded.opaqueFix`), `Ref.get/set` |
| `mkAppM` | `ST.Prim.mkRef`, `IO.getNumHeartbeats`, `IO.monoNanosNow` (profiler trace options), `instantiateExprMVarsImp`, `ppExt` state, `mkAppMArgs.loop` (partial), `Ref.get/set` |
| `unfoldDefinition?` | `whnf` (opaque), `smartUnfoldingReduce?.go`, `getStructuralRecArgPos?`, `instantiateExprMVarsImp`, `ST.Prim.mkRef`, `Ref.get/set` |
| `reduce` | `reduce.visit` (private, partial), `ST.Prim.mkRef`, `Ref.get` |
So even with `ReadWorld mref` / `SetFrame mref cref` / U2 `freshFVar`, each row has at least one stop that is a partial or opaque function whose behaviour on `envAt`
is not given by any existing premise. 未供給 / この調査で経路未発見.

### 3.3 `Diag` (9 constructors, field `diag`)
`profLog`/`ioEprintln`: `IO.getStderr` (opaque) and `Handle.putStr` (opaque); `ioGetStderr`, `ioHandleMk`, `ioHandleFlush`: single opaque IO prims; `stderrFlush`:
`Sparkle.Compiler.flushStderr` (an IO prim); `msgToString`: `MessageData.formatAux` (partial) over the message class `OkMsg`; `ppExpr`: `ppExt` state (user-registered printers),
`instantiateExprMVarsImp`, `ST.Prim.mkRef`. No premise name applies. 未供給 / この調査で経路未発見.

### 3.4 Telescope fields (4) and `AdmCtx` / `InertUnfold`
* `forallTelescopeReducing` reaches `forallTelescopeReducingAux` (private, partial); `lambdaTelescope` reaches `lambdaTelescopeImp.process` (partial);
  `withLocalDeclD` / `withLetDecl` reach `isClassExpensive?` (partial) besides `Ref.get/set` and `mkFreshFVarId` (closed by U2-8). The wrappers also run an arbitrary
  continuation `k`; the field is a `Keeps I` statement, not an env frame, and `L′`'s stability premise (`quiet′ w → quiet′ w′`) is weaker than the premise `L.T` accepts
  (`quiet w → quiet w′`), so this route does not obtain `L′.T` from `L.T` (rev3.1 §1 rows 10-13; unchanged by U1 / U2). 未供給 / この調査で経路未発見.
* `InertUnfold quiet′ f` / `AdmCtx`: `f : Meta.Config → ConstantInfo → CoreM Bool` is arbitrary; U1 / U2 give nothing about an arbitrary `f`. The only closed
  fragment is `canUnfold? = none` (`admCtx_none`, §4 `admCtx_down_of_none`). Whether `AdmCtx quiet′ ⇒ AdmCtx quiet` holds for contexts with a callback: 未供給 / この調査で経路未発見.

## 4. Frozen types. New file `Tools/ShippingGen5EnvFrame3.lean` (lean_lib `Tools.ShippingGen5EnvFrame3`), imports `Tools.ShippingGen5EnvFrame2`, `Tools.ShippingGen5EnvQ`, `Tools.ShippingChildFresh`
```lean
namespace Tools.ShippingGen5EnvFrame3
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Throws Op SideRef LocalRefType OkExc)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA (FramedA AdmCtx)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame SetGet)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame (EnvFrameEnd)
open Tools.ShippingGen5EnvQ (QuietStrength AdmDown)
open Tools.ShippingGen2 (Laws)
open Sparkle.Compiler.Elab (sparkleChildCache sparkleChildSynth sparkleSynthDepth)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (D1) the 13 class-D constructors of `FramedA`, with the same result types. -/
inductive DRow : {α : Type} → MetaM α → Prop
  | ioEnv (n : String) : DRow (liftM (IO.getEnv n) : MetaM _)
  | monoMs : DRow (liftM IO.monoMsNow : MetaM Nat)
  | mkExprCache (v : Lean.ExprStructMap String) : DRow (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
  | localMk {σ : Type} (v : σ) : LocalRefType σ → DRow (liftM (IO.mkRef v) : MetaM (IO.Ref σ))
  | whnf (e : Lean.Expr) : DRow (Lean.Meta.whnf e)
  | inferType (e : Lean.Expr) : DRow (Lean.Meta.inferType e)
  | isClass? (e : Lean.Expr) : DRow (Lean.Meta.isClass? e)
  | whnfUntil (e : Lean.Expr) (n : Name) : DRow (Lean.Meta.whnfUntil e n)
  | instantiateForall (e : Lean.Expr) (ps : Array Lean.Expr) : DRow (Lean.Meta.instantiateForall e ps)
  | mkLambdaFVars (xs : Array Lean.Expr) (e : Lean.Expr) (usedOnly usedLetOnly etaReduce generalizeNondepLet : Bool)
      (bi : BinderInfo) :
      DRow (Lean.Meta.mkLambdaFVars xs e usedOnly usedLetOnly etaReduce generalizeNondepLet bi)
  | mkAppM (c : Name) (xs : Array Lean.Expr) : DRow (Lean.Meta.mkAppM c xs)
  | unfoldDefinition? (e : Lean.Expr) : DRow (Lean.Meta.unfoldDefinition? e)
  | reduce (e : Lean.Expr) (explicitOnly skipTypes skipProofs : Bool) :
      DRow (Lean.Meta.reduce e explicitOnly skipTypes skipProofs)

/-- (D2) the three cell premises of one ref, as in U1 / U2. -/
def CellOK {σ : Type} (cref : ST.Ref IO.RealWorld Core.State) (r : IO.Ref σ) : Prop :=
  ReadWorld r ∧ r.ref ≠ cref.ref ∧ SetFrame r cref

/-- (D3) the cell premises the closed rows use, bundled under one name (an abbreviation of existing premise names; no new content;
NOT supplied for the runtime). In order: the three tracked refs; the 24 `SideRef` cells; the `Fresh` refs; `ReadWorld mref`;
`SetFrame mref cref`; `mref.ref ≠ cref.ref`; `ReadWorld cref`; `SetGet cref`. -/
def CellPrem (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  CellOK cref sparkleChildCache ∧ CellOK cref sparkleChildSynth ∧ CellOK cref sparkleSynthDepth ∧
  (∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) ∧
  (∀ (σ : Type) (r : IO.Ref σ), Fresh σ r → CellOK cref r) ∧
  ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref ∧ SetGet cref

-- partition guard (a constructor-count statement: 40 − 13 = 27 cases remain; no claim that the 27 are disjoint as MetaM values or that each has a `¬ DRow` supplier)
/-- (E1) the 13 D constructors are `FramedA` constructors (the subtraction `¬ DRow p` below removes real rows). -/
theorem drow_toFramedA {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α} (h : DRow p) : FramedA Fresh p

-- law-free env frames (no `Laws` / `T1Hyp` field)
/-- (E2) every non-D `FramedA` row is `EnvFrameEnd`. -/
theorem envFrameEnd_framedA {Fresh : (σ : Type) → IO.Ref σ → Prop} (hcell : CellPrem Fresh mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α} (hp : FramedA Fresh p) (hnd : ¬ DRow p) :
    EnvFrameEnd p mctx mref cctx cref
/-- (E3) both `Throws` constructors are `EnvFrameEnd`. -/
theorem envFrameEnd_throws {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α}
    (hp : Throws p) (hc : ReadWorld cref) (hm : ReadWorld mref) : EnvFrameEnd p mctx mref cctx cref
/-- (E4) `AdmCtx` is down-closed on the contexts without a callback, for ANY two quiet predicates (law-free; instantiate at `L'.O.quiet` / `L.O.quiet` at the use site). -/
theorem admCtx_down_of_none {q q' : Void IO.RealWorld → Prop} {mctx : Meta.Context} {cctx : Core.Context}
    (h : mctx.canUnfold? = none) : AdmCtx q' mctx cctx → AdmCtx q mctx cctx

-- per-field conclusions at L′ (the field statement of RefLawsAOps with `L'.O.quiet`; `L'` appears only through `L'.O.quiet`)
/-- (F-frameT, row 2) -/
theorem frameT_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, L'.O.quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ L'.O.quiet (endW mctx mref cctx cref p w)
/-- (F-excOk, row 3) -/
theorem excOk_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', L'.O.quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
/-- (F-frameQ, row 4; the 27 non-D rows) -/
theorem frameQ_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ¬ DRow p → ∀ w, L'.O.quiet w →
    L'.O.quiet (endW mctx mref cctx cref p w)
/-- (F-cacheSetQ, row 5) -/
theorem cacheSetQ_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w → L'.O.quiet w'
/-- (F-depthSetQ, row 6) -/
theorem depthSetQ_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    L'.O.quiet w → L'.O.quiet w'
/-- (F-frame, row 7) -/
theorem frame_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ∀ w, L'.O.quiet w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w
/-- (F-cacheSet, row 8) -/
theorem cacheSet_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w
/-- (F-depthSet, row 9) -/
theorem depthSet_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v
end Tools.ShippingGen5EnvFrame3
```
Proof plans. E1: case split on `DRow`, each case is the `FramedA` constructor of the same name. E2: destructure `CellPrem`, case split on `FramedA` (40 cases); the 27 non-D cases
are the U1 / U2 lemma named in the table of U2 (`get/set/modify/modifyGet`, their `IO` lifts, `getEnv`, `metaGet`, `metaModify`, `coreModifyTrace`, `freshFVar`, `fvarThrowUnknown`,
`constInfo`) fed by the matching component of `CellPrem`; the 13 D cases by `absurd (DRow.c …) hnd`. E3: `err` is U2 A2; `coreErr` is the U2-9 shape. E4: `fun _ => admCtx_none h` (general `q`, so no `Laws` constant occurs).
F-rows: `(hq w).mp` splits `L′.O.quiet w` into `L.O.quiet w ∧ ReadsAt env₀ cref w`; the `L.O` field gives the `L`-part (at `AdmCtx L.O.quiet` from `hd`); the `ReadsAt` part is
`readsAt_endW` (U1-8) applied to E2 / E3 / U1-4 at `sparkleChildCache` / `sparkleSynthDepth` (for rows 5, 6 after `endW_of_runs`); `(hq _).mpr` reassembles. Rows 3, 7, 8, 9 use the `L.O` field only.

Counting: 3 definitions / inductives (DRow with 13 constructors, CellOK, CellPrem) + 12 theorems (E1-E4, F × 8) = 15 items; TYPE compares 13 constructor types + 2 definition bodies + 12 theorems = 27.
Rows served: Laws fields 2, 3, 5, 6, 7, 8, 9 fully; 4 for 27 of 40 constructors. Fields 1, 10-13 and the 13 D constructors are NOT served.

## 5. Rows that stay open, and the exact statements that would close them (NOT adopted)
Same discipline as rev3.1 §3: these are the specifications that would be needed by this proof route; this survey found no route that avoids them; that is not a proof that none exists. Adopting any
of them is a T1 (new TRUSTED) decision for the user; U3 does not adopt, import or assume them.
* **T1-D** (`frameQ` for the 13 `DRow` constructors; rows ioEnv / monoMs / mkExprCache / localMk / the 9 Meta-library rows):
```lean
  envFrameD : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), DRow p → ∀ w, quiet w → envAt cref (endW mctx mref cctx cref p w) = envAt cref w
```
  Impact: one TRUSTED clause about 13 operations including the opaque `whnf` / `inferType`, allocation and OS prims; it is a statement about the runtime. A statement over arbitrary
  actions is false in the model (`frame_all_false`); this one is restricted to the 13 listed constructors and to `AdmCtx quiet`; whether it is true of the real Lean runtime was not examined.
* **T1-Diag** (`diag`): the same clause with `Diag p` (9 constructors); `ppExpr` runs registered printers, the others are opaque IO prims.
* **T1-Tele ×4** (`telescope lamTelescope localDecl letDecl`): the four fields with the stability premise
  `(cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') → envAt w' = envAt w → I w → I w')` (the `envAt` equation is the added part).
* **T1-Unfold** (`AdmDown` for contexts with a `canUnfold?` callback): `∀ f, mctx.canUnfold? = some f → InertUnfold quiet′ f → InertUnfold quiet f`, or `InertUnfold` strengthened to keep `envAt`.
* **Premise-level alternatives** (not laws about `Laws`, still new premise names, so also NOT adopted): an allocation premise for `ST.Prim.mkRef` (`envAt` unchanged by the world of an allocation) would
  serve `mkExprCache localMk` and the `mkRef` stops of §3.2; a premise for `IO.getEnv` / `IO.monoMsNow` would serve `ioEnv monoMs`. Neither is among `ReadKeeps / ReadWorld / SetGet / SetFrame`.
Impact (as FREEZE §4.4.4 / §4.4.6): these add ≈ 8-10 TRUSTED clauses about `envAt`. Reversible until a downstream theorem imports them. If not decided, the env part of `L′` stays open for rows 1, 10-13 and 13 constructors of row 4.

## 6. `QuietStrength` (construction of `L′`) and C0 after U3: what is still missing, row by row
| item | after U1 + U2 + U3 | missing |
|---|---|---|
| `QuietStrength L L′ env₀` (an `L′` exists) | fields 2, 3, 5, 6, 7, 8, 9 and 27 / 40 of field 4 have their `L′` statements (§4); `L′` is NOT built (no structure value) | fields 1 (`diag`) and 10-13 (telescopes); 13 `DRow` constructors of field 4 |
| `AdmDown L L′` | only `canUnfold? = none` (E4, for arbitrary quiet predicates; `AdmDown L L′` itself is not obtained) | contexts with a callback: no route found |
| `CellPrem` (cell premises) | named, used as hypothesis | not supplied for the runtime (ReadWorld / SetFrame / SetGet / distinctness / `Fresh`-ref non-aliasing) |
| `Start L′` | unchanged (rev3.1 §4) | `CacheInvA L′.O (cv w₀)` |
| C0 (generic, all worlds) | an induction over every operation the compiler runs would use E2 / E3 for the 27 + 2 rows | the 13 D rows, `Diag`, telescopes, callbacks; plus `CellPrem` at the runtime |
| FG / M5 | not touched | not supplied |
Rows for which this route supplies nothing: §5 lists the statements a T1 could add (law statement and impact only; nothing adopted, and no claim that a T1 is the only way).

## 7. Checks (`Tests/Gen5/EnvFrame3Check.lean`, lean_lib `Tests.Gen5.EnvFrame3Check`), Expected written from §4 of THIS file, not from the implementation
Imports `Tools.ShippingGen5EnvFrame3`, `Tests.Gen5.EnvFrame2Check` (reuses `reach`, `mkForbid`, fixtures; no walker change for the law-free roots) and `Tests.Gen3.ExpectedType`.
* TYPE: the 13 `DRow` constructor types, the bodies of `CellOK` and `CellPrem`, and the 12 theorems against Expected propositions, one comparator (`withReducible checkExpected`) for positive and negative. Total 27.
* MUTANT (well-typed single changes, rejected by the same comparator; signature / defeq rejections, NOT semantic counterexamples): N1 `frameQ_plus` without `¬ DRow p`; N2 `frameQ_plus` without `hd`;
  N3 `frameQ_plus` concluding `L.O.quiet` instead of `L′.O.quiet`; N4 `cacheSetQ_plus` without `hcell`; N5 `frameT_plus` dropping the `quiet` conjunct; N6 `frameT_plus` dropping the `cv/sv/dv` conjunct;
  N7 `cacheSet_plus` dropping the last conjunct `dv w' = dv w`; N8 `envFrameEnd_framedA` without `hnd`; N9 `envFrameEnd_throws` without `hm`; N10 `excOk_plus` without `hd`; N11 `CellPrem` without `SetGet cref`;
  N12 `CellOK` without `r.ref ≠ cref.ref`; N13 `admCtx_down_of_none` without `h`. MUTANT total = 13 (N5-N7 are conjunct-dropping mutants of the conjunctive conclusions).
* PARTITION: `DRow` has exactly 13 constructors and each is a result type of a `FramedA` constructor (E1); `FramedA` has 40 constructors, so 40 − 13 = 27 constructor cases remain (counts read from the environment). This is a constructor count only; it is not a proof of non-overlap of the 27 actions as `MetaM` values or of a `¬ DRow` supplier for any of them.
* CLOSURE (same walker, root self judged, unknown name `throwError`, intended name and path asserted) in three modes. (i) LAW-FREE: E1-E4 (4 roots) use the full forbid list (no `Laws` / `RefLawsAOps` / `RefLawsATele` / `T1Hyp` / `T1HypND` field, recursor, raw
  `Expr.proj`, no `GetEnvFrame` / `EnvSnapshot` / `getEnvFrame_of_readKeeps` / `envFrame_getConstInfo`); E4 is law-free because it is stated for an arbitrary quiet predicate. (ii) QUIET-ONLY (E4 at the laws): a Check fixture
  instantiates E4 at `L.O.quiet` / `L'.O.quiet`; with the forbid list minus {`Laws.O`, `RefLawsAOps.quiet`} it must be clean and its collected guarded set must be exactly {`Laws.O`, `RefLawsAOps.quiet`} (positive). Negatives in the same mode,
  each flagged with the intended constant on the path: a fixture using `L.O.frame` (another `RefLawsAOps` field), `L.T` (`Laws.T`), `L.T.telescope` (`RefLawsATele`), `T1Hyp.defines`, a raw projection of `RefLawsAOps`. (iii) FIELD ROOTS: see next. (iii) The 8 F roots use `L.O` by design: for them the walker is run in collect mode and the reached set of guarded constants
  must be EXACTLY {`Laws.O`, `RefLawsAOps.quiet`, `RefLawsAOps.<the row's field>`} (and for rows 2, 5, 6 the same plus nothing else): no `Laws.T`, no `RefLawsATele` field, no `T1Hyp` / `T1HypND` field, no other `RefLawsAOps`
  field, no raw guarded projection. Negative controls: a fixture reaching a second field must be flagged as an extra; a fixture reaching `Laws.T`; the U1 / U2 control suites re-run against the same walker. Counts reported as
  `n law-free roots + n field roots / n negatives (direct + helper, per mode) + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root; no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvFrame3Check` (one target, `-c 2`). The tree that is committed is the tree that is built before the commit.
Lean commit ⇒ the Issue stays `doing`, the note says "clean build は coder".

## 8. Not claimed
* No claim that the cell premises, `QuietStrength`, `AdmDown` hold of the runtime, or that C0, `defines`, FG, M5, `Start L′`, `L′` hold or exist.
* No claim that class D, `Diag`, the telescope fields or callbacks are underivable; "未供給 / この調査で経路未発見" is a result of this survey.
* Probes (§2) and the reachability table (§3) are not proofs; mutants are signature / defeq rejections, not semantic counterexamples.
* No change to `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, the compiler, FG or `GenWF`; no edit of an existing file except `lakefile.lean` (two `lean_lib` entries).
