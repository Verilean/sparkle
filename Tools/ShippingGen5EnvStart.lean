import Tools.ShippingGen5EnvQ
set_option autoImplicit false
-- Built: Pod kjob lake build Tests.Gen5.EnvStartCheck exit 0, 758 jobs, at tree 0d506a98 (Lean commit; clean issue-linked build is run by the coder). Result: TYPE 3, MUTANT 7, CLOSURE 3 roots, AXIOMS 3 standard.

/-! # DG-ENV unit U4: `Start L'` at an empty start cache and a no-callback context, CONDITIONAL
(scripts/gen5/DG_ENV_T2_U4_FREEZE.md §3)

`cv w₀ = {}` and `mctx.canUnfold? = none` are HYPOTHESES (premises about the runtime start world / top-level context);
this file does not supply them. `L'`, `QuietStrength`, `AdmDown` (callbacks), `CellPrem`, `¬ DRow`, C0, FG are not supplied.
No new law, no TRUSTED boundary, no shared-definition change. Not M5 or FG completion. -/
namespace Tools.ShippingGen5EnvStart
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx admCtx_none)
open Tools.ShippingChildBndCore (cv)
open Tools.ShippingChildCacheA (JQC CacheInvA cacheInvA_empty)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvQ (QuietStrength jq_start)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (S1) the `Start L'` assembled from its three parts; the cache half and the context half are hypotheses. -/
theorem start_up_of_parts {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀)
    (hA : AdmCtx L'.O.quiet mctx cctx) (hC : CacheInvA L'.O (cv w₀)) : Start L' mctx cctx w₀ :=
  ⟨hA, jq_start hq hS, hC⟩

/-- (S3) the cache half alone at the empty cache (law-free in the bundle: any `O`). -/
theorem cacheInvA_of_empty {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref)
    {w₀ : Void IO.RealWorld} (hE : cv w₀ = {}) : CacheInvA O (cv w₀) := by
  rw [hE]; exact cacheInvA_empty O

/-- (S2) the closed fragment: empty start cache and no `canUnfold?` callback. -/
theorem start_up_empty {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀)
    (hE : cv w₀ = {}) (hn : mctx.canUnfold? = none) : Start L' mctx cctx w₀ :=
  start_up_of_parts hq hS (admCtx_none hn) (cacheInvA_of_empty L'.O hE)

end Tools.ShippingGen5EnvStart
