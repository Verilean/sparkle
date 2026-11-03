# DG-ENV T2 unit U8 freeze: survey after U7, and the first unit (the executed cache insert keeps `CacheInvN`) (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r17` 3fa51023 (U7 O0-O4 approved, build env17v-3fa51023 exit 0, 761 jobs, TYPE 5 / MUT 9 / AX 5), plus 475c2361 (header comment sync only).
Nothing here adds a law, a `Laws` / `RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, a premise with runtime content, or changes a shared definition; nothing narrows FG or strengthens `GenWF`.
Nothing here supplies a real-run `hN`, `L′`, `QuietStrength`, `hE`, `CellPrem`, `¬ DRow`, callbacks, C0 or FG. "未供給 / この調査で辿った候補経路では未供給" is a result of THIS survey (existing lemmas read at 3fa51023), not a claim of impossibility.
The Check audits kernel types / values with the permitted projections as leaves; it does not show that a law bundle was constructed.

## 0. Rows examined (existing lemmas, full names)
| row | existing lemmas read | result |
|---|---|---|
| executed cache insert keeps `CacheInvN` (the step "end cache `cv w′` of `sparkleChildCache.modify (·.insert c r)`") | `Tools.ShippingChildInvA.RefLawsAOps.cacheModify'` (`O hA f hq h : cv w' = f (cv w) ∧ sv w' = sv w ∧ dv w' = dv w`, from `RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w'`, `hq : O.quiet w`), `Tools.ShippingChildInvA.admCtx_none`, `Tools.ShippingChildCacheA.jqc_insert_runs` (the `RealChildA`/`JQC` form), `Tools.ShippingGen5EnvCacheC.cacheInvN_insert` (U7 O2) | CLOSES: chosen unit (§1). `cacheModify'` is an existing theorem proved from the existing fields `O.frame`, `O.frameQ`, `O.cacheSet` (no new field); composing it with O2 gives the restricted analogue of `jqc_insert_runs`'s cache half. |
| terminal `cv w′` of a whole `synthesizeChild n` run (hit: end world of the cache read; miss: world after the nested `synthesizeCombinational` run, then the insert) | `Tools.ShippingChildCacheA.synthesizeChild_realA` (takes `hentry`: a returning nested run from a `JQC O D` world ends in `JQC O D`), `jqc_cacheGet`, `jqc_insert_runs` | この調査で辿った候補経路では未供給 for the nested part: the miss branch needs the nested run's end cache `cv w2` to satisfy the invariant, which `synthesizeChild_realA` takes as the premise `hentry`; no existing lemma found in this survey proves it. Only the insert step after it is closed by §1. The hit branch needs `O.frame` at `FramedA.cacheGet` (as `jqc_cacheGet`) plus `JQ` data (`sv`, depth) not carried by `CacheInvN`: not attempted in this unit. |
| real start-cache `hN` (every entry of `cv w₀`) | `Start L` stores `CacheInvA L.O (cv w₀)` (Tools/ShippingGen2Defs.lean:52) | この調査で辿った候補経路では未供給 (unchanged from U7 §0: needs `canUnfold? = none` and `ReadsAt env₀ cref w` per stored run). |
| non-empty concrete `RealChildN` | `RealChildN.run` needs `RunsTo (synthesizeCombinational c) …` | この調査で辿った候補経路では未供給 (opaque `Meta`/`Core` run). |
| `L′` / `QuietStrength` | `Laws.O` (13 fields), `Laws.T`; `QuietStrength` | この調査で辿った候補経路では未供給. |
| `CellPrem` | `ReadWorld`, `SetFrame`, `SetGet`, `ReadWorld.readKeeps` | この調査で辿った候補経路では未供給 (premises about `initialize … IO.mkRef {}` opaque constants). |
| `¬ DRow p` | `drow_toFramedA`, `envFrameEnd_framedA` | この調査で辿った候補経路では未供給. |
| `readsAt` along a run, callbacks/`AdmDown` for `canUnfold? = some f` | `Tools.ShippingGen5RunReads.*`, `readsAt_of_quiet`, `AdmDown`, `InertUnfold` | Rows owned by DG-READKINDS / DG-ACC / readertrace / G-REACH are named only, not re-derived. |
`40 − 13 = 27` remains a constructor count only. C0 and FG are not complete and not touched.

## 1. Chosen first unit: U8 = the executed insert step
Reason: of §0 it is the only row whose statement is an existing theorem (`cacheModify'`) composed with an already-approved one (O2) and whose premises are all already premises of U7 (`hn`, `quiet`, a `RealChildN` for the inserted entry, `CacheInvN` at the start world). It is the first statement about the END world `w′` of an actual cache operation (a `RunsTo` of `sparkleChildCache.modify`), which U7 O3 deliberately did not give. It uses the existing `O.frame` / `O.frameQ` / `O.cacheSet` fields through `cacheModify'`, as `jqc_insert_runs` already does; this is existing-field use, not a new law, so no decision document is needed. If the reviewer reads the use of these fields as a new boundary, the Issue goes to `decision` before any Lean.
What it does NOT do: it does not prove `hentry` (the cache coherence of the nested run), does not show that the run of `synthesizeCombinational c` ends in a `CacheInvN` world, does not give a real start-cache `hN`, a non-empty example, `QuietStrength`, or `L′`. The hypotheses `hw` (`CacheInvN` at the start world of the insert) and `hr` (`RealChildN` of the inserted entry) remain hypotheses.

## 2. Frozen type. Append to NEW file `Tools/ShippingGen5EnvCacheD.lean` (lean_lib `Tools.ShippingGen5EnvCacheD`), imports `Tools.ShippingGen5EnvCacheC`
```lean
namespace Tools.ShippingGen5EnvCacheD
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (admCtx_none)
open Tools.ShippingChildBndCore (cv)
open Sparkle.Compiler.Elab (sparkleChildCache)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheC (CacheInvN cacheInvN_insert)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (P1) the executed cache insert of a restricted real child, from a quiet world with a restricted cache, keeps the restricted cache. -/
theorem cacheInvN_insert_runs {L : Laws mref cref} {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context}
    {c : Name} {r : Res} {w w' : Void IO.RealWorld} {u : Unit}
    (hn : mctx.canUnfold? = none) (quiet : L.O.quiet w)
    (hw : CacheInvN L env₀ (cv w)) (hr : RealChildN L env₀ c r)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w') :
    CacheInvN L env₀ (cv w')
end Tools.ShippingGen5EnvCacheD
```
Proof plan: `obtain ⟨hk, -, -⟩ := Tools.ShippingChildInvA.RefLawsAOps.cacheModify' L.O (admCtx_none hn) (fun m : Std.HashMap Name Res => m.insert c r) quiet h; rw [hk]; exact cacheInvN_insert hw hr`. If `Tools.ShippingChildInvA.RefLawsAOps.cacheModify'` needs its `Fresh` / `mctx` / `cctx` arguments given differently, any change is reported before review; the statement above is the frozen content.
Counting: 1 theorem. TYPE = 1 Expected comparison (P1).

## 3. Check (`Tests/Gen5/EnvCacheDCheck.lean`, lean_lib `Tests.Gen5.EnvCacheDCheck`), Expected written from §2 of THIS file
Same discipline as `EnvCacheCCheck`: `Tests.Gen3.ExpectedType` (`checkExpected`), independent Expected, one comparator (`withReducible`), walker `reachQ` from `Tests.Gen5.EnvFrame3Check`.
* TYPE 1: P1.
* MUTANT (well-typed single changes rejected by the same comparator; signature / defeq rejections, NOT semantic counterexamples; only well-typed mutants counted, count reported as measured): M1 without `hn`; M2 without `quiet`; M3 without `hw`; M4 without `hr`; M5 `hw` stated at `CacheInvN L env₁ (cv w)` for a second bound `env₁`; M6 conclusion `CacheInvN L env₀ (cv w)` (start world instead of `w'`); M7 inserted function `fun m => m.insert c r` replaced by `fun m => m` ; M8 `L.O.quiet w'` instead of `L.O.quiet w`. Ill-typed ones are dropped, not counted.
* CLOSURE (quiet-plus-three mode, unknown/forbidden separated; root self judged; unknown name `throwError`; intended name and path asserted): guarded constants reached from P1 are at most `Laws.O`, `RefLawsAOps.quiet`, `RefLawsAOps.frame`, `RefLawsAOps.frameQ`, `RefLawsAOps.cacheSet` (reached through `cacheModify'`, as for `jqc_insert_runs`). The freeze says "at most"; the observed per-root set is reported. Forbidden: every other `RefLawsAOps` field (`diag`, `frameT`, `excOk`, `cacheSetQ`, `depthSetQ`, `depthSet`), `Laws.T`, `RefLawsATele.*`, `T1Hyp.*`, `T1HypND.*`, recursors on those, raw projections, `GetEnvFrame` / `EnvSnapshot`. Controls: law-bearing negative fixtures (direct and helper counted separately; each flagged with its intended constant, including one for each of the three allowed-but-guarded fields being detected as ALLOWED and one for a forbidden field such as `RefLawsAOps.depthSet` being flagged), `unknown` (including a helper whose type alone is an unknown name) and `forbidden` as separate controls, self-root controls, clean controls; each negative asserts that the forbidden-flag is set by the intended constant alone. Counts as `n roots / n negatives + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvCacheDCheck` (one target, `-c 2`). Lean commit ⇒ the Issue stays `doing`; the note says "clean build は coder".

## 4. Not claimed
* `hn`, `quiet`, `hw`, `hr`, the `RunsTo` witness of the modify, and `QuietStrength` remain hypotheses. A real-cache `hN`, the cache coherence `hentry` of a nested run, a non-empty concrete example, `L′`, `hE`, `CellPrem`, `¬ DRow`, callbacks, C0, FG, M5: not supplied (この調査で辿った候補経路では未供給). U8 is not the terminal `cv w′` of a whole `synthesizeChild` run and is not preservation of `CacheInvN` by the entry run; it is the insert step only. Not Issue completion.
* No new law or TRUSTED; no decision document is needed unless the reviewer reads §1's use of existing fields differently. Mutants are signature / defeq rejections, not semantic counterexamples. No edit of `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`; only `lakefile.lean` (two `lean_lib` entries) among existing files.
