# DG-ENV T2 unit U9 freeze: survey after U8, and the first unit (one whole `synthesizeChild n` call keeps `CacheInvN` and yields `RealChildN`) (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r20` bb49da59 (U8 `cacheInvN_insert_runs` approved, build env20v-bb49da59 exit 0, 762 jobs, TYPE 1 / MUT 8 / AX 1), plus 8abea24a (header comment sync only).
Nothing here adds a law, a `Laws` / `RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, or changes a shared definition; nothing narrows FG or strengthens `GenWF`.
Nothing here supplies a real-run `hN`, `L′`, `QuietStrength`, `CellPrem`, `¬ DRow`, callbacks, C0 or FG. "未供給 / この調査で辿った候補経路では未供給" is a result of THIS survey (existing lemmas read at bb49da59), not a claim of impossibility. Mutants (below) are signature / defeq rejections, not semantic counterexamples.

## 0. Rows examined (existing lemmas, full names)
| row | existing lemmas read | result |
|---|---|---|
| `CacheInvN` kept by one whole `synthesizeChild n` call (hit branch and miss branch plus last insert) | `Tools.ShippingChildCacheA.synthesizeChild_realA` (old `RealChildA`/`JQC` form; takes `hentry`), `jqc_cacheGet`, `Tools.ShippingGen5EnvCacheD.cacheInvN_insert_runs` (U8), `Tools.ShippingGen5EnvCacheC.realChildN_of_run` (U7 O3) | CLOSES, relative to a premise `hentry` that is the exact restricted analogue of the old `hentry` (chosen unit, §1). The nested core run's end cache is NOT proved (as in the old lemma). |
| `hr` (`RealChildN L env₀ n y`) from an actual run | `realChildN_of_run` needs `hn`, `ReadsAt env₀ cref w1`, `CacheInvN L env₀ (cv w1)`, `sv w1 = some synthesizeChild`, `L.O.quiet w1`, `RunsTo (synthesizeCombinational n) … w1 y w2` | CLOSES inside §1 for the miss branch (all inputs come from the call's start world plus the cache-read step), and for the hit branch from `hw` by `m.get? n = some y`. `ReadsAt` at the world after the cache read needs `ReadWorld sparkleChildCache` (§1 premise `hrw`, U1 `envFrameEnd_get` + `readsAt_endW`); that premise is not supplied for the runtime here. |
| `quiet` of the world after the cache read / insert | `RefLawsAOps.frame` / `frameQ` (at `FramedA.cacheGet`), `cacheModify'`, `cacheSetQ` (through `jqc_insert_runs`) | CLOSES for the cache read (`frameQ`) and the end-of-insert quiet is NOT in `cacheInvN_insert_runs` (U8 returns only `CacheInvN`); §1 gets it from the nested run's premise (`hentry` returns `quiet w2`) and `cacheSetQ`. This uses the existing field `cacheSetQ` (the old `jqc_insert_runs` does the same). It is existing-field use, not a new law; if the reviewer reads it otherwise the Issue goes to `decision` before Lean. |
| `quiet` / `ReadsAt` / `CacheInvN` at the end of the nested `synthesizeCombinational` run | `Tools.ShippingGen5RunReads.*`, `readsAt_of_quiet`, `Tools.ShippingChildCacheA.closeInstsM_realA` | この調査で辿った候補経路では未供給 (it is the premise `hentry`; rows owned by G-REACH / DG-READKINDS are named only). |
| real start-cache `hN`, non-empty concrete `RealChildN`, `L′` / `QuietStrength`, `CellPrem`, `¬ DRow`, callbacks | as U8 §0 | この調査で辿った候補経路では未供給 (unchanged). |
`40 − 13 = 27` remains a constructor count only. C0 and FG are not complete and not touched.

## 1. Chosen first unit: U9 = one whole `synthesizeChild n` call, restricted
Reason: it is the first statement about the END world of an entire `synthesizeChild` call (U8 was one insert only). Both branches reduce to approved lemmas (U7 O3 for `hr`, U8 for the last insert, `frame`/`frameQ` through `admCtx_none hn` for the read) and it exposes exactly one new premise `hentry`, the same one the old `synthesizeChild_realA` exposes, now in restricted form. Nested synthesizeChild preservation then follows by supplying `hentry` from the induction of a caller; that is not done here (the nested core run is opaque, row 4).
What it does NOT do: it does not prove `hentry`, does not give a real start-cache `hN`, a non-empty example, `QuietStrength`, `L′`, `CellPrem`, `¬ DRow`, callbacks, C0 or FG. `ReadsAt` at the end world is not claimed (no `ReadsAt` through the insert is proved).

## 2. Frozen type. New file `Tools/ShippingGen5EnvCacheE.lean` (lean_lib `Tools.ShippingGen5EnvCacheE`), imports `Tools.ShippingGen5EnvCacheD`
```lean
namespace Tools.ShippingGen5EnvCacheE
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv sv)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheC (CacheInvN)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (Q1) a whole `synthesizeChild n` call from a quiet world with a restricted cache: the result is a restricted real child, the end cache is restricted, the end world is quiet with the synthesis ref intact. -/
theorem synthesizeChild_realN {L : Laws mref cref} {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context}
    {n : Name} {w w' : Void IO.RealWorld} {y : Res}
    (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2))
    (quiet : L.O.quiet w) (synth : sv w = some synthesizeChild) (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild
end Tools.ShippingGen5EnvCacheE
```
(`sparkleChildCache` is opened from `Sparkle.Compiler.Elab` in the real file; the `IO.Ref` ascription is as in `ReadWorld`'s argument type and is adjusted only if elaboration needs it, reported before review.)
Proof plan: `unfold synthesizeChild at h`; `RunsTo.bind` for the cache read (`runsTo_get_readOf` gives `m = cv w`; `L.O.frame`/`frameQ` at `FramedA.cacheGet` with `admCtx_none hn` give `cv`/`sv`/quiet at `w1`; `ReadsAt env₀ cref w1` from `readsAt_endW (envFrameEnd_get hrw) rd` and `endW_of_runs`). Hit: `y = ` the entry, `RealChildN` from `hw`, end world = `w1`. Miss: `realChildN_of_run hn rd1 hw1 synth1 quiet1 hrun` for `hr`; `hentry` for the end of the nested run; then `cacheInvN_insert_runs` (U8) for `CacheInvN (cv w3)`; quiet at `w3` by `L.O.cacheSetQ` after `modify_split` (as `jqc_insert_runs`); `sv w3 = sv w2` from `cacheModify'`. Any change of the argument list needed to make this elaborate is reported before review; the statement above is the frozen content.
Counting: 1 theorem. TYPE = 1 Expected comparison (Q1).

## 3. Check (`Tests/Gen5/EnvCacheECheck.lean`, lean_lib `Tests.Gen5.EnvCacheECheck`), same requirements as U8
* Independent Expected written from §2 (`Tests.Gen3.ExpectedType`, one comparator, walker `reachQ` from `Tests.Gen5.EnvFrame3Check`). TYPE 1.
* MUTANT (well-typed single changes only; signature / defeq rejections; the count is the measured count): M1 without `hn`; M2 without `hrw`; M3 without `hentry`; M4 `hentry` conclusion without `L.O.quiet w2`; M5 `hentry` without its `CacheInvN` hypothesis; M6 without `quiet`; M7 without `synth`; M8 without `rd`; M9 without `hw`; M10 conclusion without `CacheInvN L env₀ (cv w')`; M11 `CacheInvN L env₀ (cv w)` in the conclusion (start world); M12 `RealChildN L env₀ n y` replaced by a second bound `env₁`. Ill-typed ones are dropped, not counted.
* CLOSURE: allowed guarded constants (leaf, at most): `Laws.O`, `RefLawsAOps.quiet`, `RefLawsAOps.frame`, `RefLawsAOps.frameQ`, `RefLawsAOps.cacheSet`, `RefLawsAOps.cacheSetQ` (the last through the quiet-after-insert step). Forbidden: every other `RefLawsAOps` field (`diag`, `frameT`, `excOk`, `depthSetQ`, `depthSet`), `Laws.T`, `RefLawsATele.*`, `T1Hyp.*`, `T1HypND.*`, recursors on those, raw projections, `GetEnvFrame` / `EnvSnapshot`. Controls: allowed-field controls (one per allowed field), law-bearing negative fixtures (direct and helper counted separately, each flagged by its intended constant alone), `unknown` (name `throwError`, kept apart from `forbidden`), self-root controls, clean controls, root judged itself; observed per-root set reported. Counts as `n roots / n negatives + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvCacheECheck` (one target, `-c 2`). After the Lean commit the Issue stays `doing`; the note says "clean build は coder".

## 4. Not claimed
* `hn`, `hrw`, `hentry`, `quiet`, `synth`, `rd`, `hw` and the `RunsTo` witness remain hypotheses. The cache coherence of the nested core run (`hentry`), a real start-cache `hN`, a non-empty concrete example, `ReadsAt` at the end world, `L′`, `QuietStrength`, `CellPrem` (`hrw` is one conjunct of it, not supplied), `¬ DRow`, callbacks, C0, FG, M5: not supplied (この調査で辿った候補経路では未供給). Q1 is one call of `synthesizeChild`, conditional on `hentry`; it is not preservation of `CacheInvN` by every run and not Issue completion.
* No new law or TRUSTED. `cacheSetQ` is an existing field already used by `jqc_insert_runs`. No edit of `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`; only `lakefile.lean` (two `lean_lib` entries) among existing files.
