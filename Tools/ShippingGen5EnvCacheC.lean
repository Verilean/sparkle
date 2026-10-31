import Tools.ShippingGen5EnvCacheB
set_option autoImplicit false
-- NOT BUILT (U7 O0-O4 implementation; freeze scripts/gen5/DG_ENV_T2_U7_FREEZE.md approved at 047c2f7c as design only). Conditional bookkeeping: hn/rd/quiet/synth/RunsTo witness/QuietStrength remain hypotheses.

/-! # DG-ENV unit U7: the restricted cache invariant `CacheInvN` and its empty / insert / run-step / transport lemmas, CONDITIONAL
(scripts/gen5/DG_ENV_T2_U7_FREEZE.md §2)

Restates the `RealChildA` cache lemmas (`cacheInvA_empty`, `cacheInvA_insert`, `RealChildA.run`) at `RealChildN`.
(O3) builds a `RealChildN` for the SAME start world `w` from its inputs; it does NOT show that the end cache `cv w'` satisfies
`CacheInvN` and does not execute any cache insert. Supplies no real-cache `hN`, non-empty example, `L'`, `QuietStrength`,
`hE`, `CellPrem`, `¬ DRow`, C0 or FG. No new law, no TRUSTED boundary, no shared-definition change. Not M5 or FG completion. -/
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
theorem cacheInvN_empty (L : Laws mref cref) (env₀ : Environment) : CacheInvN L env₀ {} := by
  intro c r h
  first
    | simp at h
    | (rw [Std.HashMap.get?_empty] at h; cases h)

/-- (O2) the insert of a restricted real child keeps the invariant. -/
theorem cacheInvN_insert {L : Laws mref cref} {env₀ : Environment} {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : CacheInvN L env₀ m) (hr : RealChildN L env₀ c r) : CacheInvN L env₀ (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

/-- (O3) a run of the real entry from a world with a restricted cache is a restricted real child. -/
theorem realChildN_of_run {L : Laws mref cref} {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context}
    {c : Name} {r : Res} {w w' : Void IO.RealWorld}
    (hn : mctx.canUnfold? = none) (rd : ReadsAt env₀ cref w) (hw : CacheInvN L env₀ (cv w))
    (synth : sv w = some synthesizeChild) (quiet : L.O.quiet w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildN L env₀ c r :=
  .run mctx cctx w w' hn rd hw synth quiet hr

/-- (O4) the invariant transports along `QuietStrength` (`realChildN_up` entry-wise). -/
theorem cacheInvN_up {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {m : Std.HashMap Name Res} (h : CacheInvN L env₀ m) : CacheInvN L' env₀ m :=
  fun c r hc => Tools.ShippingGen5EnvCacheB.realChildN_up hq (h c r hc)

end Tools.ShippingGen5EnvCacheC
