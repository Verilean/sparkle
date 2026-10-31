# DG-ENV T2 unit U7 freeze: survey after U6, and the first unit (`CacheInvN`: the restricted cache invariant, its empty / insert / run-step lemmas) (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r15` e511ffc0 (U6 B1-B4 approved, build env15v-e511ffc0 exit 0, 760 jobs, TYPE 4 / MUT 8 / AX 4), plus 33250ef1 (header comment sync only).
Nothing here adds a law, a `Laws` / `RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, a premise with runtime content, or changes a shared definition; nothing narrows FG or strengthens `GenWF`.
Nothing here supplies a real-run `hN`, `L′`, `QuietStrength`, `hE`, `CellPrem`, `¬ DRow`, callbacks, C0 or FG. "未供給 / この調査で辿った候補経路では未供給" is a result of THIS survey (existing lemmas read at e511ffc0), not a claim of impossibility.
The Check audits kernel types / values with the permitted projections as leaves; it does not show that a law bundle was constructed.

## 0. Rows examined (existing lemmas, full names)
| row | existing lemmas read | result |
|---|---|---|
| `hN` from a real run | `Tools.ShippingChildCacheA.RealChildA.of_jqc`, `cacheInvA_insert`, `cacheInvA_empty`, `jqc_cacheGet`, `Tools.ShippingChildFrontCP.childEntryA_JQC_of_childSynthA` (all stated for `RealChildA` / `JQC`, i.e. the `AdmCtx` form); `Tools.ShippingGen5EnvCache.RealChildN` (U5) | The restricted analogues (empty / insert / run-step for `RealChildN`) are NOT yet stated anywhere: the U5/U6 files have `realChildA_of_N`, `realChildA_up_of_N`, `cacheInvA_up_of_N`, `realChildN_up/down` only. They follow by the same one-line proofs as their `RealChildA` counterparts. CLOSES: chosen unit (§1). The entries of a REAL start cache `cv w₀` remain 未供給 (below). |
| real start-cache `hN` (every entry of `cv w₀`) | `Start L` stores `CacheInvA L.O (cv w₀)` (Tools/ShippingGen2Defs.lean:52), `RealChildA.run` stores `adm : AdmCtx L.O.quiet mctx cctx`, `quiet : L.O.quiet w` | この調査で辿った候補経路では未供給. From `RealChildA` to `RealChildN` one needs, per stored entry, `mctx.canUnfold? = none` (from `adm` only if `AdmCtx` implies it; `AdmCtx` also admits `some f` with `InertUnfold`) and `ReadsAt env₀ cref w` for the stored world `w` (not given by `L.O.quiet w`). Both would be premises about the stored runs. |
| non-empty concrete `RealChildN` | `RealChildN.run` needs `RunsTo (synthesizeCombinational c) …` | この調査で辿った候補経路では未供給 (an opaque `Meta`/`Core` run; U4 §1.2) |
| `L′` / `QuietStrength` | `Laws.O` (13 fields), `Laws.T`; `QuietStrength` | この調査で辿った候補経路では未供給 (U4 §1.3) |
| `CellPrem` | `ReadWorld`, `SetFrame`, `SetGet`, `ReadWorld.readKeeps` | この調査で辿った候補経路では未供給 (U4 §1.2; premises about `initialize … IO.mkRef {}` opaque constants) |
| `¬ DRow p` | `drow_toFramedA`, `envFrameEnd_framedA` | この調査で辿った候補経路では未供給 (U4 §1.1) |
| `AdmDown` for `canUnfold? = some f` | `AdmDown`, `InertUnfold`, `admCtx_down_of_none` | この調査で辿った候補経路では未供給 (U5 §0) |
| `readsAt` along a run (a step that preserves `ReadsAt env₀` when `L.O.quiet`) | `Tools.ShippingGen5RunReads.*`, `Tools.ShippingGen5EnvQ.readsAt_of_quiet` | Owned by the run/reads rows (`ShippingGen5RunReads`); not re-derived here. Rows owned by DG-READKINDS / DG-ACC / readertrace are named only. |
`40 − 13 = 27` remains a constructor count only. C0 and FG are not complete and not touched.

## 1. Chosen first unit: U7 = the restricted cache invariant and its three closed steps
Reason: of §0 it is the only row whose statements follow from existing definitions with no new premise beyond those already in the `RealChildN` constructor (it is the `RealChildA` triple `cacheInvA_empty` / `cacheInvA_insert` / `RealChildA.of_jqc` restated at `RealChildN`, whose proofs are `rw`/`split` and `RealChildN.run`). It names `hN` of U5 (`∀ c r, (cv w₀).get? c = some r → RealChildN …`) as one definition, so later units that grow a cache (insert after a run) or start from `{}` state `hN` once. It does not supply any premise: `ReadsAt`, `hn`, `quiet`, `synth` and the `RunsTo` witness of the run-step lemma remain hypotheses.
What it does NOT do: it does not give `hN` for a real start cache, a non-empty concrete example, or `QuietStrength`.

## 2. Frozen types. New file `Tools/ShippingGen5EnvCacheC.lean` (lean_lib `Tools.ShippingGen5EnvCacheC`), imports `Tools.ShippingGen5EnvCacheB`
```lean
namespace Tools.ShippingGen5EnvCacheC
open Lean
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv sv)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen5EnvCache (RealChildN)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (O0) every entry of the map is a restricted real child (the `hN` of `start_up_of_N`, as one definition). -/
def CacheInvN (L : Laws mref cref) (env₀ : Environment) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → RealChildN L env₀ c r

/-- (O1) the empty cache. -/
theorem cacheInvN_empty (L : Laws mref cref) (env₀ : Environment) : CacheInvN L env₀ {}

/-- (O2) the insert of a restricted real child keeps the invariant. -/
theorem cacheInvN_insert {L : Laws mref cref} {env₀ : Environment} {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : CacheInvN L env₀ m) (hr : RealChildN L env₀ c r) : CacheInvN L env₀ (m.insert c r)

/-- (O3) a run of the real entry from a world with a restricted cache is a restricted real child. -/
theorem realChildN_of_run {L : Laws mref cref} {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context}
    {c : Name} {r : Res} {w w' : Void IO.RealWorld}
    (hn : mctx.canUnfold? = none) (rd : ReadsAt env₀ cref w) (hw : CacheInvN L env₀ (cv w))
    (synth : sv w = some synthesizeChild) (quiet : L.O.quiet w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildN L env₀ c r

/-- (O4) the invariant transports along `QuietStrength` (`realChildN_up` entry-wise). -/
theorem cacheInvN_up {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {m : Std.HashMap Name Res} (h : CacheInvN L env₀ m) : CacheInvN L' env₀ m
end Tools.ShippingGen5EnvCacheC
```
Proof plans. O1: `intro c r h; rw [Std.HashMap.get?_empty] at h; cases h` (with the `simp at h` fallback used by `cacheInvA_empty`). O2: the proof of `cacheInvA_insert` with `RealChildN`. O3: `.run mctx cctx w w' hn rd hw synth quiet hr` (the `cache` field is `hw`, unfolded by `CacheInvN`). O4: `fun c r hc => Tools.ShippingGen5EnvCacheB.realChildN_up hq (h c r hc)`.
Statements are the frozen content; if an `open` / implicit-argument shape needs adjusting when elaborating, any change is reported before review.
Counting: 1 definition + 4 theorems. TYPE = 4 Expected comparisons (O1-O4) plus 1 definition-body comparison for O0 (unfolds to the stated `∀`): TYPE 5.

## 3. Checks (`Tests/Gen5/EnvCacheCCheck.lean`, lean_lib `Tests.Gen5.EnvCacheCCheck`), Expected written from §2 of THIS file
Same discipline as `EnvCacheBCheck`: `Tests.Gen3.ExpectedType` (`checkExpected`), independent Expected, one comparator (`withReducible`), walker `reachQ` from `Tests.Gen5.EnvFrame3Check`.
* TYPE 5: O0 (the definition's value against the independently written `∀`), O1-O4.
* MUTANT (well-typed single changes rejected by the same comparator; signature / defeq rejections, NOT semantic counterexamples; only well-typed mutants counted): M1 O1 for a bound `m` instead of `{}` (needs a premise-free claim, well-typed); M2 O2 without `hr`; M3 O2 without `h`; M4 O3 without `rd`; M5 O3 without `hn`; M6 O3 without `quiet`; M7 O3 with `hw` replaced by `CacheInvN L env₁ (cv w)` for a second bound `env₁`; M8 O4 without `hq`; M9 O4 concluding `CacheInvN L env₁ m`. Total 9, sum rule.
* CLOSURE (quiet-only mode as in U6; root self judged; unknown name `throwError`; intended name and path asserted): guarded constants reached from O0-O4 are at most `Laws.O` and `RefLawsAOps.quiet` (O3 states `L.O.quiet w`; O4 via `realChildN_up`). Forbidden: any other `RefLawsAOps` field, `Laws.T`, `RefLawsATele.*`, `T1Hyp.*`, `T1HypND.*`, recursors on those, raw projections, `GetEnvFrame` / `EnvSnapshot`. Controls: law-bearing negative fixtures (direct and helper counted separately; each flagged with its intended constant), `unknown` (including a helper whose type alone is an unknown name) and `forbidden` as separate controls, self-root controls, clean controls; each negative asserts that the forbidden-flag is set by the intended constant alone. Counts as `n roots / n negatives + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root; no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvCacheCCheck` (one target, `-c 2`). Lean commit ⇒ the Issue stays `doing`; the note says "clean build は coder".

## 4. Not claimed
* `hn`, `hN`, `rd`, `quiet`, `synth`, the `RunsTo` witness and `QuietStrength` remain hypotheses. A real-cache `hN`, a non-empty concrete example, `L′`, `hE`, `CellPrem`, `¬ DRow`, callbacks, C0, FG, M5: not supplied (この調査で辿った候補経路では未供給). U7 is bookkeeping that restates the `RealChildA` cache lemmas at the restricted predicate; it is not progress toward supplying those premises and is not Issue completion.
* No new law or TRUSTED; no decision document is needed. Mutants are signature / defeq rejections, not semantic counterexamples. No edit of `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`; only `lakefile.lean` (two `lean_lib` entries) among existing files.
