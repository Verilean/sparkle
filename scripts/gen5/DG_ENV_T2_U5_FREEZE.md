# DG-ENV T2 unit U5 freeze: survey of the rows left after U4, and the first unit (`Start L′` at a NON-empty cache, restricted derivations) (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r12` 26f3413c (U4 approved at b86a9535, build env11v-b86a9535 exit 0, 758 jobs, TYPE 3 / MUT 7 / AX 3; 26f3413c is a comment/docs sync only).
Nothing here adopts a new law, adds a `Laws` / `RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, or changes a shared definition. `hN` (every start-cache entry has a restricted derivation `RealChildN`) is introduced as a NEW explicit restricting hypothesis, conditionally; it is not supplied; nothing narrows FG or strengthens `GenWF`.
Nothing here supplies `L′`, `QuietStrength`, `hE`, `hn`, `CellPrem`, `¬ DRow`, non-empty-cache `Start L′` for the OLD `RealChildA`, callbacks, C0 or FG. "未供給 / この調査で経路未発見" is a result of THIS survey (existing lemmas read at b86a9535), not a claim of impossibility.
The audit of the Check covers kernel types / values with the permitted projections as leaves; it does not show that a law bundle was constructed.

## 0. Rows examined after U4
| row | existing lemmas read (full names) | result |
|---|---|---|
| `¬ DRow p` | `Tools.ShippingGen5EnvFrame3.DRow` (13 constructors on function values `MetaM α`), `drow_toFramedA`, `envFrameEnd_framedA` | 未供給 / この調査で経路未発見 (no disequality or injectivity lemma on `MetaM` values was found; U4 §1.1) |
| `CellPrem` | `ReadWorld`, `SetFrame`, `SetGet`, `ReadWorld.readKeeps`; `sparkleChildCache` etc. are `initialize` constants (opaque) | 未供給 / この調査で経路未発見 (U4 §1.2) |
| `QuietStrength` / `L′` | `Tools.ShippingGen5EnvQ.QuietStrength`, `Laws` has the fields `O` (13) and `T` | 未供給 / この調査で経路未発見 (U4 §1.3) |
| `AdmDown` with `canUnfold? = some f` | `AdmDown`, `InertUnfold`, `admCtx_none`, `admCtx_down_of_none` | 未供給 / この調査で経路未発見. `InertUnfold L′.O.quiet f` says nothing about worlds quiet for `L` but not `L′`; a route would carry a premise on `f` (e.g. that its runs preserve `ReadsAt env₀`), which is a new premise and is not introduced here |
| `Start L′`, NON-empty start cache, for the OLD `RealChildA L.O` entries | `realChildA_down` (new ⇒ old only), `cacheInvA_down`, `RealChildA.run` fields `adm`, `quiet`, `cache` | 未供給 / この調査で経路未発見 for the old inductive: an entry's stored `AdmCtx L.O.quiet` and stored `L.O.quiet w` do not give `AdmCtx L′.O.quiet` nor `ReadsAt env₀ cref w` |
| `Start L′`, non-empty cache, for entries whose stored derivation is RESTRICTED to no-callback contexts and `ReadsAt env₀` worlds | `admCtx_none`, `quiet` characterisation by `QuietStrength`, `RealChildA` | CLOSES from existing lemmas by name: this is the chosen unit (§1) |
`40 − 13 = 27` remains a constructor count only. C0 and FG are not complete and not touched.

## 1. Chosen first unit: U5 = transport of restricted cache entries from `L` to `L′`
Reason: it is the only row of §0 whose proof is assembled from existing lemmas (`admCtx_none` for the context half, `QuietStrength` for the quiet half, structural induction on the new inductive for the recursive cache field), it needs no `Laws` field beyond `O.quiet`, no `CellPrem`, no `AdmDown`, no `¬ DRow`, and it replaces the single hypothesis "`cv w₀ = {}`" of U4 by a weaker one ("every entry of `cv w₀` has a restricted derivation").
What it does NOT do: it does not show that the runtime's start cache, or any cache reached in a run, has restricted derivations (that is a premise about the runtime and is not supplied); `RealChildN` is a NEW restricted definition, not a change of `RealChildA` (a shared definition is not edited); the restriction (`canUnfold? = none` and `ReadsAt env₀ cref w` at every stored run) is exactly what makes the transport go through, and the restricted notion is not claimed to cover the entries the real compiler stores.
The two kinds of facts the restriction names are exactly the two things the old derivation lacks: `AdmCtx L′.O.quiet` (supplied here by `admCtx_none`) and `L′.O.quiet w` (supplied here by `QuietStrength` from `L.O.quiet w` and `ReadsAt env₀ cref w`).

## 2. Frozen types. New file `Tools/ShippingGen5EnvCache.lean` (lean_lib `Tools.ShippingGen5EnvCache`), imports `Tools.ShippingGen5EnvStart`
```lean
namespace Tools.ShippingGen5EnvCache
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (AdmCtx admCtx_none)
open Tools.ShippingChildBndCore (cv sv)
open Tools.ShippingChildCacheA (RealChildA CacheInvA)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (N0) `RealChildA` with the stored `AdmCtx` replaced by `canUnfold? = none`, the stored quiet world required to read the fixed environment `env₀`; the bundle is `L`. -/
inductive RealChildN (L : Laws mref cref) (env₀ : Environment) : Name → Res → Prop
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (hn : mctx.canUnfold? = none)
      (rd : ReadsAt env₀ cref w)
      (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildN L env₀ c' r')
      (synth : sv w = some synthesizeChild)
      (quiet : L.O.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildN L env₀ c r

/-- (N1) a restricted entry is an old entry (the restriction only strengthens the stored data). -/
theorem realChildA_of_N {L : Laws mref cref} {env₀ : Environment} {c : Name} {r : Res}
    (h : RealChildN L env₀ c r) : RealChildA L.O c r

/-- (N2) a restricted entry is a new entry, from `QuietStrength`. -/
theorem realChildA_up_of_N {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {c : Name} {r : Res} (h : RealChildN L env₀ c r) : RealChildA L'.O c r

/-- (N3) the cache half over a map. -/
theorem cacheInvA_up_of_N {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {m : Std.HashMap Name Res} (h : ∀ c r, m.get? c = some r → RealChildN L env₀ c r) : CacheInvA L'.O m

/-- (N4) `Start L′` at a non-empty start cache whose entries all have restricted derivations, and a no-callback top context. -/
theorem start_up_of_N {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀) (hn : mctx.canUnfold? = none)
    (hN : ∀ c r, (cv w₀).get? c = some r → RealChildN L (envAt cref w₀) c r) : Start L' mctx cctx w₀
end Tools.ShippingGen5EnvCache
```
Proof plans. N1: induction on `h`, `.run mctx cctx w w' (admCtx_none hn) ih synth quiet hr`. N2: induction on `h`, `.run mctx cctx w w' (admCtx_none hn) ih synth ((hq w).mpr ⟨quiet, rd⟩) hr`. N3: `fun c r hc => realChildA_up_of_N hq (h c r hc)`. N4: `Tools.ShippingGen5EnvStart.start_up_of_parts hq hS (admCtx_none hn) (cacheInvA_up_of_N hq hN)` (`env₀ := envAt cref w₀`).
If the exact `open` / implicit-argument shapes need an adjustment when elaborating (e.g. whether `RealChildA` takes `Fresh` implicitly), the statements above are the frozen content and any change is reported before review. Counting: 1 inductive definition, 4 theorems. TYPE = 4 Expected comparisons plus 1 for the constructor type of `RealChildN.run`.
Note that U4 `start_up_empty` is the special case `cv w₀ = {}` of N4 only in the sense that both give `Start L′`; no relation is claimed beyond that.

## 3. Checks (`Tests/Gen5/EnvCacheCheck.lean`, lean_lib `Tests.Gen5.EnvCacheCheck`), Expected written from §2 of THIS file
Same discipline as `EnvStartCheck`: `Tests.Gen3.ExpectedType` (`checkExpected`), independent Expected, the walker `reach` from `Tests.Gen5.EnvFrame2Check`.
* TYPE: N1-N4 and the type of `RealChildN.run` against independently written Expected propositions, one comparator (`withReducible checkExpected`).
* MUTANT (well-typed single changes rejected by the same comparator; signature / defeq rejections, NOT semantic counterexamples): M1 N2 without `hq`; M2 N4 without `hn`; M3 N4 without `hN`; M4 N4 concluding `Start L` ; M5 N3 concluding `CacheInvA L.O m`; M6 `RealChildN.run` without `hn`; M7 `RealChildN.run` without `rd`; M8 N1 concluding `RealChildA L′.O c r` with `L′` explicitly bound as a binder (well-typed; needs `hq`, rejected by signature); only mutants that are well-typed with `L′` explicitly bound are counted. Total 8, counted with the sum rule.
* CLOSURE (walker, root self judged, unknown name `throwError`, intended name and path asserted): quiet-only mode as in U4: the guarded constants reached from N1-N4 are exactly `Laws.O` and `RefLawsAOps.quiet` (`QuietStrength` mentions `L.O.quiet`, `L′.O.quiet`; `RealChildA` mentions `AdmCtx O.quiet`); N1 may reach `Laws.O` and `RefLawsAOps.quiet` (the type of `RealChildN` mentions `L.O.quiet`, so quiet appears there). Forbidden everywhere: any other `RefLawsAOps` field, `Laws.T`, `RefLawsATele.*`, `T1Hyp.*`, `T1HypND.*`, recursors on those, raw projections, `GetEnvFrame` / `EnvSnapshot`.
  Controls: positive = the 4 theorems; negative law-bearing fixtures reaching `L.O.frame`, `L.T`, `L.T.telescope`, `T1Hyp.defines` (each flagged with the intended constant; direct and helper counted separately); controls for `unknown` (unresolved, throwing) and `forbidden` (flagged) are kept separate, unknown ones including a helper whose type alone is an unknown name; self-root controls. Counts reported as `n roots / n negatives + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root and for `RealChildN`'s recursor use; no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvCacheCheck` (one target, `-c 2`). Lean commit ⇒ the Issue stays `doing`; the note says "clean build は coder".

## 4. Not claimed
* `hn`, `hN` and `QuietStrength` are hypotheses; this unit does not show they hold of the runtime start world, start cache or top-level context. The old-`RealChildA` non-empty-cache row, callbacks (`canUnfold? = some f`), `L′`, `CellPrem`, `¬ DRow`, C0, FG, M5: not supplied and not touched (未供給 / この調査で経路未発見).
* `RealChildN` is a restricted copy for this transport; it is not claimed to be what the compiler's cache stores. No new law or TRUSTED; no decision document is needed for this unit.
* Mutants are signature / defeq rejections, not semantic counterexamples. Probes are not acceptance evidence. No edit of `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`; only `lakefile.lean` (two `lean_lib` entries) among existing files.

## 5. Sync after approval (no type change)
The reviewer's four notes (hN as new conditional premise; N1 closure allows `O`/`quiet`; unknown vs forbidden controls separated; M8 counted only when well-typed with `L′` bound) are folded into the text above. This unit permits non-empty caches as a TYPE; it supplies no non-empty instance and no real-cache `hN`. `L′`, `QuietStrength`, `hE`, `hn`, `CellPrem`, `¬ DRow`, C0, FG remain unsupplied.
