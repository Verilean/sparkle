import Tools.ShippingLegacySemDispatch

/-! # The legacy caching shim, walked: where its stage holds today

`Rec.translateExprToWireCached` (`Sparkle/Compiler/Elab.lean`): for a
cacheable call under a context with an expression cache, read the `IO.Ref`
map and return its wire on a hit; otherwise run the body
`Rec.translateExprToWireImpl`, insert the result into the map, return it.

**Proved** (`legacyShim_returns`), for every successful run of today's shim
from `s` to `t` returning `w`: either it is a successful run of the body from
`s` to `t` returning `w` (the map's update does not touch the builder state),
or the call is cacheable, the context has a cache, and `t = s` — a hit, about
whose wire NOTHING is known (it is whatever the map holds).

So the shim stage `ShimAt` of `Tools/ShippingLegacySemDispatch.lean` holds
today exactly where no hit can occur: `shimAt_of_uncacheable` (the call is
`named`, `top`, or an `fvar`) and `shimAt_of_noCache` (the context has no
expression cache). `reachesAt_uncacheable` assembles the dispatch for those
calls; the body stage stays its premise.

For a cacheable call under the entry's context (`exprCache = some _`, always)
`ShimAt` does not follow, and it is false of a run that hits a stale entry:
the validated alternative `s.translateRecord.get? w = some e` is exactly what
today's shim does not check.

This file is separate from the dispatch file because its one proof walks a
program with an early `return` (a join point) whose elaborated shape was
inferred from `translateControlCachedWith_returns`, not observed. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

set_option maxHeartbeats 1000000 in
/-- **The shim, inverted**: the body's run, or an unvalidated hit. -/
theorem legacyShim_returns {tr : TranslateFn} {e : Lean.Expr} {hint w : String}
    {top named : Bool} {ctx : CompilerState} {s t : CircuitState}
    (h : Returns (Rec.translateExprToWireCached tr e hint top named) ctx s w t) :
    Returns (Rec.translateExprToWireImpl (fun e h t n => tr e h t n) e hint top named)
        ctx s w t ∨
      ((!named && !e.isFVar && !top) = true ∧ (∃ ref, ctx.exprCache = some ref) ∧ t = s) := by
  unfold Rec.translateExprToWireCached at h
  -- Every inversion gives its continuation a NEW name: a `subst` on a state
  -- or context variable would otherwise bring the old hypothesis back under
  -- the reused name.
  obtain ⟨c, s1, hread, k0⟩ := Returns.bind h
  obtain ⟨hc, hs1⟩ := Returns.read hread
  rw [hs1] at k0
  dsimp only at k0
  -- After the body's run `hl`, what is left (`j1`) is one of three shapes,
  -- depending on what the earlier `split`s already decided (observed in the
  -- first build): `pure r`; the map's update then `pure r`; or a `match` on
  -- the context's cache over those two. `hfin` handles all three.
  split at k0
  · -- a cacheable call
    split at k0
    · -- the context has a cache: the lookup
      obtain ⟨look, s2, hlook, k1⟩ := Returns.bind k0
      have hs2 := Returns.liftMetaM hlook
      rw [hs2] at k1
      split at k1
      · -- a hit: the counter, then the map's wire
        obtain ⟨u, s3, hhit, k2⟩ := Returns.bind k1
        have hs3 := Returns.liftMetaM hhit
        obtain ⟨hw, ht⟩ := Returns.pure k2
        have hex : ∃ ref, ctx.exprCache = some ref := by
          rw [← hc]
          exact ⟨_, by assumption⟩
        exact Or.inr ⟨by assumption, hex, ht.trans hs3⟩
      · -- a miss: the body, the map's update, the result
        first
          | (obtain ⟨r, sm, hl, j1⟩ := Returns.bind k1
             have hfin : w = r ∧ t = sm := by
               repeat' split at j1
               all_goals first
                 | exact Returns.pure j1
                 | (obtain ⟨u, s4, hmid, j2⟩ := Returns.bind j1
                    obtain ⟨hw, ht⟩ := Returns.pure j2
                    exact ⟨hw, ht.trans (Returns.liftMetaM hmid)⟩)
             refine Or.inl ?_
             rw [hfin.1, hfin.2]
             exact hl)
          | (obtain ⟨u0, s0, hp, k3⟩ := Returns.bind k1
             obtain ⟨-, hs0⟩ := Returns.pure hp
             rw [hs0] at k3
             obtain ⟨r, sm, hl, j1⟩ := Returns.bind k3
             have hfin : w = r ∧ t = sm := by
               repeat' split at j1
               all_goals first
                 | exact Returns.pure j1
                 | (obtain ⟨u, s4, hmid, j2⟩ := Returns.bind j1
                    obtain ⟨hw, ht⟩ := Returns.pure j2
                    exact ⟨hw, ht.trans (Returns.liftMetaM hmid)⟩)
             refine Or.inl ?_
             rw [hfin.1, hfin.2]
             exact hl)
    · -- no cache in the context: the body
      obtain ⟨r, sm, hl, j1⟩ := Returns.bind k0
      have hfin : w = r ∧ t = sm := by
        repeat' split at j1
        all_goals first
          | exact Returns.pure j1
          | (obtain ⟨u, s4, hmid, j2⟩ := Returns.bind j1
             obtain ⟨hw, ht⟩ := Returns.pure j2
             exact ⟨hw, ht.trans (Returns.liftMetaM hmid)⟩)
      refine Or.inl ?_
      rw [hfin.1, hfin.2]
      exact hl
  · -- not cacheable: the body
    obtain ⟨r, sm, hl, j1⟩ := Returns.bind k0
    have hfin : w = r ∧ t = sm := by
      repeat' split at j1
      all_goals first
        | exact Returns.pure j1
        | (obtain ⟨u, s4, hmid, j2⟩ := Returns.bind j1
           obtain ⟨hw, ht⟩ := Returns.pure j2
           exact ⟨hw, ht.trans (Returns.liftMetaM hmid)⟩)
    refine Or.inl ?_
    rw [hfin.1, hfin.2]
    exact hl

/-- The shim stage for a call that is not cacheable: no lookup happens. -/
theorem shimAt_of_uncacheable {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {hint : String} {top named : Bool}
    (hnc : (!named && !e.isFVar && !top) = false) :
    ShimAt rec ctx e hint top named := by
  intro s t w hr
  rcases legacyShim_returns hr with hbody | ⟨hc, _, _⟩
  · exact Or.inl hbody
  · exact absurd (hnc.symm.trans hc) (by decide)

/-- The shim stage under a context without an expression cache. -/
theorem shimAt_of_noCache {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {hint : String} {top named : Bool} (hno : ctx.exprCache = none) :
    ShimAt rec ctx e hint top named := by
  intro s t w hr
  rcases legacyShim_returns hr with hbody | ⟨_, ⟨ref, href⟩, _⟩
  · exact Or.inl hbody
  · rw [hno] at href
    cases href

/-- **The dispatch of a call that is not cacheable, today**: for a plain call
of kind `.other`, from the body stage alone. -/
theorem reachesAt_uncacheable {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {mn : Name} {us : List Level} {hint : String} {top named : Bool}
    (hkind : fallbackKind e = .other) (hfn : e.getAppFn = .const mn us)
    (hplain : PlainHead mn) (hnc : (!named && !e.isFVar && !top) = false)
    (body : BodyReachesInline rec ctx e) :
    ReachesAt rec ctx e hint top named :=
  reachesAt_of_stages hkind hfn hplain (shimAt_of_uncacheable hnc) body

/-- The same under a context without an expression cache, for every call. -/
theorem reachesAt_noCache {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {mn : Name} {us : List Level} {hint : String} {top named : Bool}
    (hkind : fallbackKind e = .other) (hfn : e.getAppFn = .const mn us)
    (hplain : PlainHead mn) (hno : ctx.exprCache = none)
    (body : BodyReachesInline rec ctx e) :
    ReachesAt rec ctx e hint top named :=
  reachesAt_of_stages hkind hfn hplain (shimAt_of_noCache hno) body

end Tools.ShippingLegacySem
