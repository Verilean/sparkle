import Tools.ShippingGen5EnvCacheD
import Tools.ShippingGen5EnvFrame
set_option autoImplicit false
-- BUILT: clean issue-linked build env22v-b6b3206b exit 0 (763 jobs, dirty=false) at b6b3206b: U9 implementation of freeze scripts/gen5/DG_ENV_T2_U9_FREEZE.md; build pending (clean build is run by the coder).

/-! # DG-ENV unit U9: one whole `synthesizeChild n` call keeps `CacheInvN` and yields `RealChildN`, CONDITIONAL
(scripts/gen5/DG_ENV_T2_U9_FREEZE.md §2)

Hit and miss branches. `hentry` (the nested `synthesizeCombinational` run keeps quiet / synthesis ref / `ReadsAt` / `CacheInvN`)
is a hypothesis, as in `synthesizeChild_realA`; `hn`, `hrw`, the start-world premises and the `RunsTo` witness stay hypotheses.
Does NOT supply a real start-cache `hN`, a non-empty example, `ReadsAt` at the end world, `L'`, `QuietStrength`, `CellPrem`,
`¬ DRow`, callbacks, C0 or FG. Uses the existing field `cacheSetQ` (as `jqc_insert_runs`); no new law, no TRUSTED boundary. -/
namespace Tools.ShippingGen5EnvCacheE
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res endW_of_runs)
open Tools.ShippingChildInvA (admCtx_none FramedA)
open Tools.ShippingChildBndCore (cv sv modify_split)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational sparkleChildCache)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame (envFrameEnd_get readsAt_endW)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheC (CacheInvN realChildN_of_run)
open Tools.ShippingGen5EnvCacheD (cacheInvN_insert_runs)
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
    RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild := by
  have hA := admCtx_none (quiet := L.O.quiet) (cctx := cctx) hn
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  have hk := L.O.frame hA _ FramedA.cacheGet w quiet
  have hq1 := L.O.frameQ hA _ FramedA.cacheGet w quiet
  have hrd1 := readsAt_endW (mctx := mctx) (mref := mref) (cctx := cctx) (envFrameEnd_get hrw) rd
  rw [endW_of_runs hget] at hk hq1 hrd1
  have hm : m = cv w := Tools.ShippingChildBndInit.runsTo_get_readOf _ hget
  have hsy1 : sv w1 = some synthesizeChild := hk.2.1.trans synth
  have hcv1 : cv w1 = cv w := hk.1
  cases hc : m.get? n with
  | some r =>
    simp only [hc] at h
    obtain ⟨rfl, rfl⟩ := Tools.ShippingChildInv.RunsTo.pure_world h
    rw [hm] at hc
    exact ⟨hw n _ hc, hcv1 ▸ hw, hq1, hsy1⟩
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
    have hw1 : CacheInvN L env₀ (cv w1) := hcv1 ▸ hw
    have hr : RealChildN L env₀ n r := realChildN_of_run hn hrd1 hw1 hsy1 hq1 hrun
    obtain ⟨hq2, hs2, hc2⟩ := hentry w1 w2 r hq1 hsy1 hrd1 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
    obtain ⟨rfl, rfl⟩ := Tools.ShippingChildInv.RunsTo.pure_world h
    have hkm := L.O.cacheModify' hA
      (fun m : Std.HashMap Name Res => m.insert n y) hq2 hmod
    have hq3 : L.O.quiet w' := by
      obtain ⟨w4, hg, hs⟩ := modify_split sparkleChildCache
        (fun m : Std.HashMap Name Res => m.insert n y) hmod
      have hqa := L.O.frameQ hA _ FramedA.cacheGet w2 hq2
      rw [endW_of_runs hg] at hqa
      exact L.O.cacheSetQ hA _ _ _ _ hs hqa
    exact ⟨hr, cacheInvN_insert_runs hn hq2 hc2 hr hmod, hq3, hkm.2.1.trans hs2⟩
end Tools.ShippingGen5EnvCacheE
