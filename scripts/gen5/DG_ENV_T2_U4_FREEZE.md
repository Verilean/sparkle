# DG-ENV T2 unit U4 freeze: survey of the unsupplied rows, and the first unit (`Start L′` at an empty cache, no callback) (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r9` fe5c28aa (U3 approved, build env9v-fe5c28aa exit 0, 756 jobs, TYPE 27 / MUT 13 / AX 15), plus 36a93441 (header comment sync, no proof change).
Nothing here adds a law, a `Laws` / `RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, a premise with new content, or a shared definition; nothing narrows FG or strengthens `GenWF`;
nothing supplies C0 / QuietStrength / AdmDown / CellPrem / `¬ DRow` / L′ / FG. "未供給 / この調査で経路未発見" below is a result of THIS survey (what was read at fe5c28aa), not a claim of impossibility.

## 0. The five unsupplied items stay distinct
| item | what it is | status after this survey |
|---|---|---|
| `¬ DRow p` | per-action hypothesis of `envFrameEnd_framedA` / `frameQ_plus`: `p` is none of the 13 class-D constructors | 未供給 / この調査で経路未発見 (§1.1) |
| `CellPrem` | the named cell premises (`ReadWorld`, `SetFrame`, `SetGet`, distinctness, `SideRef` / `Fresh` cells) | 未供給 (premise about the runtime; §1.2) |
| `QuietStrength L L′ env₀` | an `L′` with `L′.O.quiet w ↔ L.O.quiet w ∧ ReadsAt env₀ cref w` is GIVEN | 未供給; `L′` is not built (§1.3) |
| `AdmDown L L′` | `AdmCtx L′.O.quiet ⇒ AdmCtx L.O.quiet` at every context | only for `canUnfold? = none` (U3 E4); callbacks 未供給 / この調査で経路未発見 (§1.4) |
| `L′` / `Start L′` | the law bundle itself, and its start condition | `L′` 未供給. `Start L′` has ONE closed fragment (§2, the chosen unit): empty cache and no callback |
`40 − 13 = 27` remains a constructor count only. C0 and FG are not complete and not touched.

## 1. Rows examined (existing lemmas, full names and types)
### 1.1 `¬ DRow p`
`DRow` is an inductive predicate on `MetaM α` values (functions). To prove `¬ DRow p` for a concrete `p`, one would need `p ≠` each of 13 constructor values (`liftM (IO.getEnv n)`, `Lean.Meta.whnf e`, …).
These are function values, so the proof routes enumerated in this survey for a disequality are: a world on which the two differ (an obligation: a premise about the runtime's behaviour on that world, e.g. what `getEnv` returns) or injectivity of constructors (an obligation: `MetaM` terms are functions and no such injectivity lemma was found). This lists the obligations of the routes examined here, not a necessary condition over all routes.
Existing lemmas read: `Tools.ShippingGen5EnvFrame3.drow_toFramedA`, `envFrameEnd_framedA`, `Tools.ShippingChildInvA.FramedA` constructors. None gives `¬ DRow`. 未供給 / この調査で経路未発見.
### 1.2 `CellPrem`
Components: `ReadWorld`, `SetFrame`, `SetGet` (`Tools.ShippingStRefCorrespondence`, premises "for the real runtime"), `r.ref ≠ cref.ref`. Existing lemma `ReadWorld.readKeeps : ReadWorld r → ReadKeeps r` goes between premises only.
`sparkleChildCache` is introduced by `initialize … ← IO.mkRef {}` (Sparkle/Compiler/Elab.lean:1032); `initialize` constants are opaque, so nothing about `ST.Prim.Ref.get/set` follows. 未供給 / この調査で経路未発見.
### 1.3 `QuietStrength`
`def QuietStrength (L L′ : Laws mref cref) (env₀ : Environment) : Prop := ∀ w, L′.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt env₀ cref w)` (Tools/ShippingGen5EnvQ.lean). Building an `L′` needs a value for each of the 13 fields
(`diag`, 4 telescope fields, `frameQ` for the 13 D constructors are not closed in U3) plus `T`. 未供給 / この調査で経路未発見.
### 1.4 `AdmDown` beyond `canUnfold? = none`
`def AdmDown L L′ := ∀ mctx cctx, AdmCtx L′.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx`. For `canUnfold? = some f` one needs `InertUnfold L′.O.quiet f → InertUnfold L.O.quiet f`. `InertUnfold q f` quantifies over worlds with `q w`;
`L.O.quiet` holds on worlds where `L′.O.quiet` need not (by `QuietStrength` it is the weaker one), so the hypothesis on `f` says nothing about those worlds. Existing: `admCtx_none`, `admCtx_down_of_none` (U3 E4) only. 未供給 / この調査で経路未発見.
### 1.5 `Start L′`
`def Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w` (Tools/ShippingGen2Defs.lean:52); `JQC O D w := JQ O.quiet D w ∧ CacheInvA O (cv w)`;
`CacheInvA O m := ∀ c r, m.get? c = some r → RealChildA O c r`.
Closed parts with existing lemmas: `Tools.ShippingGen5EnvQ.jq_start : QuietStrength L L′ (envAt cref w₀) → Start L mctx cctx w₀ → JQ L′.O.quiet 0 w₀` (the `JQ` half);
`Tools.ShippingChildInvA.admCtx_none` (the `AdmCtx` half when `mctx.canUnfold? = none`); `Tools.ShippingChildCacheA.cacheInvA_empty (O) : CacheInvA O {}` (the cache half when the cache is empty).
Not closed: the cache half for a NON-empty cache: `RealChildA L′.O` from `RealChildA L.O` is "old ⇒ new"; the routes examined here would carry the obligations `AdmDown`-converse and a quiet-strength-in-reverse for the stored runs (this lists the obligations of the examined routes, not a necessary condition over all routes) (`RealChildA.run` stores `quiet`, `adm`, `hr` of the old law bundle).
未供給 / この調査で経路未発見 (`realChildA_down` is the other direction).

## 2. Chosen first unit: U4 = `Start L′` at an empty cache and a no-callback context
Reason: it is the only row of §0 that closes from existing lemmas by name (jq_start, admCtx_none, cacheInvA_empty), it does not need `CellPrem`, `AdmDown`, `¬ DRow` or any `Laws` field,
and it removes the `Start L′` line (`CacheInvA L′.O (cv w₀)`) of the U3 §6 table for the case that the runtime's start cache is `{}` and the top context has no `canUnfold?`. The two extra hypotheses are premises
(`cv w₀ = {}` is a statement about the runtime's start world: the cell is created by `initialize … IO.mkRef {}`; this unit does NOT supply it; `canUnfold? = none` is a statement about the top-level Meta context). It does not give `L′`, `QuietStrength`, C0, FG.

## 3. Frozen types. New file `Tools/ShippingGen5EnvStart.lean` (lean_lib `Tools.ShippingGen5EnvStart`), imports `Tools.ShippingGen5EnvQ`
```lean
namespace Tools.ShippingGen5EnvStart
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (cv)
open Tools.ShippingChildCacheA (JQC CacheInvA)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvQ (QuietStrength)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (S1) the `Start L′` assembled from its three parts; the cache half and the context half are hypotheses. -/
theorem start_up_of_parts {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀)
    (hA : AdmCtx L'.O.quiet mctx cctx) (hC : CacheInvA L'.O (cv w₀)) : Start L' mctx cctx w₀

/-- (S2) the closed fragment: empty start cache and no `canUnfold?` callback. -/
theorem start_up_empty {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀)
    (hE : cv w₀ = {}) (hn : mctx.canUnfold? = none) : Start L' mctx cctx w₀

/-- (S3) the cache half alone at the empty cache (law-free in the bundle: any `O`). -/
theorem cacheInvA_of_empty {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref)
    {w₀ : Void IO.RealWorld} (hE : cv w₀ = {}) : CacheInvA O (cv w₀)
end Tools.ShippingGen5EnvStart
```
Proof plans. S1: `⟨hA, jq_start hq hS, hC⟩` (`JQC` unfolds to `JQ ∧ CacheInvA`; `jq_start` is Q9). S2: S1 with `admCtx_none hn` and `cacheInvA_of_empty`. S3: `rw [hE]; exact cacheInvA_empty O` (rewrite `cv w₀` to `{}`; the earlier `hE ▸` form had the direction reversed).
If the exact `open` / implicit-argument shapes of `RefLawsAOps` need an adjustment when elaborating, the statements above are the frozen content and any change is reported before review.
Counting: 3 theorems, no definitions. TYPE = 3 Expected comparisons.

## 4. Checks (`Tests/Gen5/EnvStartCheck.lean`, lean_lib `Tests.Gen5.EnvStartCheck`), Expected written from §3 of THIS file
Same discipline as `EnvFrame3Check`: reuses `Tests.Gen3.ExpectedType` (`checkExpected`) and the walker `reach` from `Tests.Gen5.EnvFrame2Check`.
* TYPE: the 3 theorems against independently written Expected propositions, one comparator (`withReducible checkExpected`). Total 3.
* MUTANT (well-typed single changes rejected by the same comparator; signature / defeq rejections, NOT semantic counterexamples): M1 `start_up_empty` without `hn`; M2 `start_up_empty` without `hE`;
  M3 `start_up_empty` concluding `Start L` instead of `Start L'`; M4 `start_up_of_parts` without `hq`; M5 `start_up_of_parts` without `hC`; M6 `cacheInvA_of_empty` with `cv w₀ = {}` replaced by `True` shaped hypothesis
  (`hE : cv w₀ = cv w₀`); M7 `start_up_empty` with `hE : cv w₀ = {}` replaced by `(cv w₀).isEmpty = true`. MUTANT total 7.
* CLOSURE (walker `reach`, root self judged, unknown name `throwError`, intended name and path asserted): LAW-FREE mode with the full forbid list MINUS the structure projections the statements mention:
  the roots S1-S3 may reach `Laws.O` and `RefLawsAOps.quiet` only through `jq_start` (Q9, which uses `L.O.quiet` / `L′.O.quiet` projections). So the mode is QUIET-ONLY as in U3: the guarded set reached must be
  exactly {`Laws.O`, `RefLawsAOps.quiet`} for S1, S2; S3 reaches no guarded constant. Forbidden everywhere: any other `RefLawsAOps` field, `Laws.T`, `RefLawsATele.*`, `T1Hyp.*`, `T1HypND.*`, recursors on those, raw projections, `GetEnvFrame` / `EnvSnapshot`.
  Controls: positive = the 3 roots; negative = fixtures reaching `L.O.frame`, `L.T`, `L.T.telescope`, `T1Hyp.defines` (each flagged with the intended constant), counted direct + helper; unresolved (throwing) controls; self-root controls (a forbidden constant as root). Counts reported as `n roots / n negatives + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root; no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvStartCheck` (one target, `-c 2`). Lean commit ⇒ the Issue stays `doing`, the note says "clean build は coder".

## 5. Not claimed
* `cv w₀ = {}` and `canUnfold? = none` are hypotheses; this unit does not show they hold of the runtime start world / top-level context. `Start L′` for a non-empty cache or a callback context: 未供給 / この調査で経路未発見.
* `L′`, `QuietStrength`, `AdmDown` (callbacks), `CellPrem`, `¬ DRow`, C0, FG, M5: not supplied and not touched. No new law or TRUSTED; no decision document needed for this unit.
* Mutants are signature / defeq rejections, not semantic counterexamples. Probes are not acceptance evidence. No edit of `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`; only `lakefile.lean` (two `lean_lib` entries) among existing files.
