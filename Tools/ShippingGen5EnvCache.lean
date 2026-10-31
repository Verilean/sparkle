import Tools.ShippingGen5EnvStart
set_option autoImplicit false
-- Built: clean issue-linked build env13v-9b886655 exit 0 (759 jobs, dirty=false), approved at 9b886655 (freeze scripts/gen5/DG_ENV_T2_U5_FREEZE.md). Conditional intermediate result: hN/hn/QuietStrength are hypotheses, not supplied for a real cache.

/-! # DG-ENV unit U5: `Start L'` at a NON-empty start cache whose entries have RESTRICTED derivations, CONDITIONAL
(scripts/gen5/DG_ENV_T2_U5_FREEZE.md §2)

`RealChildN` is a NEW restricted definition (no `RealChildA` edit). `hn`, `hN` and `QuietStrength` are HYPOTHESES; this file
supplies no non-empty instance and no real-cache `hN`. `L'`, `hE`, `CellPrem`, `¬ DRow`, callbacks, C0, FG are not supplied.
No new law, no TRUSTED boundary, no shared-definition change. Not M5 or FG completion. -/
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
    (h : RealChildN L env₀ c r) : RealChildA L.O c r := by
  induction h with
  | run mctx cctx w w' hn rd _ synth quiet hr ih =>
    exact .run mctx cctx w w' (admCtx_none hn) (fun c' r' hc => ih c' r' hc) synth quiet hr

/-- (N2) a restricted entry is a new entry, from `QuietStrength`. -/
theorem realChildA_up_of_N {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {c : Name} {r : Res} (h : RealChildN L env₀ c r) : RealChildA L'.O c r := by
  induction h with
  | run mctx cctx w w' hn rd _ synth quiet hr ih =>
    exact .run mctx cctx w w' (admCtx_none hn) (fun c' r' hc => ih c' r' hc) synth ((hq w).mpr ⟨quiet, rd⟩) hr

/-- (N3) the cache half over a map. -/
theorem cacheInvA_up_of_N {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {m : Std.HashMap Name Res} (h : ∀ c r, m.get? c = some r → RealChildN L env₀ c r) : CacheInvA L'.O m :=
  fun c r hc => realChildA_up_of_N hq (h c r hc)

/-- (N4) `Start L'` at a non-empty start cache whose entries all have restricted derivations, and a no-callback top context. -/
theorem start_up_of_N {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀) (hn : mctx.canUnfold? = none)
    (hN : ∀ c r, (cv w₀).get? c = some r → RealChildN L (envAt cref w₀) c r) : Start L' mctx cctx w₀ :=
  Tools.ShippingGen5EnvStart.start_up_of_parts hq hS (admCtx_none hn) (cacheInvA_up_of_N hq hN)

end Tools.ShippingGen5EnvCache
