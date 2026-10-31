import Tools.ShippingGen5EnvCacheC
set_option autoImplicit false
-- Built: clean issue-linked build env20v-bb49da59 exit 0 (762 jobs, dirty=false), approved at bb49da59 (freeze scripts/gen5/DG_ENV_T2_U8_FREEZE.md). Conditional bookkeeping: hn/quiet/hw/hr/RunsTo witness remain hypotheses.

/-! # DG-ENV unit U8: the executed cache insert keeps `CacheInvN`, CONDITIONAL
(scripts/gen5/DG_ENV_T2_U8_FREEZE.md §2)

Composes the existing `RefLawsAOps.cacheModify'` (from the existing fields `frame` / `frameQ` / `cacheSet`) with U7 `cacheInvN_insert`.
Insert step only: it does NOT show the cache coherence of a nested run, a real start-cache `hN`, a non-empty example, `L'`, `QuietStrength`,
`CellPrem`, `¬ DRow`, callbacks, C0 or FG. No new law, no TRUSTED boundary, no shared-definition change. Not M5 or FG completion. -/
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
    CacheInvN L env₀ (cv w') := by
  obtain ⟨hk, -, -⟩ := Tools.ShippingChildInvA.RefLawsAOps.cacheModify' L.O (admCtx_none hn)
    (fun m : Std.HashMap Name Res => m.insert c r) quiet h
  rw [hk]
  exact cacheInvN_insert hw hr
end Tools.ShippingGen5EnvCacheD
