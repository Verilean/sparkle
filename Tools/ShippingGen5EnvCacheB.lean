import Tools.ShippingGen5EnvCache
set_option autoImplicit false
-- NOT BUILT (clean issue-linked build): awaiting coder; incremental kjob lake build of Tests.Gen5.EnvCacheBCheck passed on this tree (agent g5env-r15). Conditional intermediate result: bookkeeping between existing premises; hN/hn/QuietStrength remain hypotheses.

/-! # DG-ENV unit U6: `QuietStrength` composition and `RealChildN` independence of the related bundle, CONDITIONAL
(scripts/gen5/DG_ENV_T2_U6_FREEZE.md §2)

Uses no `Laws` field beyond `O.quiet`. Supplies no `hN`, `L'`, `QuietStrength`, `hE`, `CellPrem`, `¬ DRow`, C0 or FG.
No new law, no TRUSTED boundary, no shared-definition change. Not M5 or FG completion. -/
namespace Tools.ShippingGen5EnvCacheB
open Lean
open Tools.ShippingChildInv (Res)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen5EnvCache (RealChildN)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (B1) `QuietStrength` composes at one fixed `env₀`. -/
theorem quietStrength_trans {L L' L'' : Laws mref cref} {env₀ : Environment}
    (h1 : QuietStrength L L' env₀) (h2 : QuietStrength L' L'' env₀) : QuietStrength L L'' env₀ :=
  fun w => ⟨fun h => let p := (h2 w).mp h; ⟨((h1 w).mp p.1).1, p.2⟩,
            fun h => (h2 w).mpr ⟨(h1 w).mpr h, h.2⟩⟩

/-- (B2) `QuietStrength L L env₀` is exactly "every `L`-quiet world reads `env₀`". -/
theorem quietStrength_self_iff {L : Laws mref cref} {env₀ : Environment} :
    QuietStrength L L env₀ ↔ ∀ w : Void IO.RealWorld, L.O.quiet w → ReadsAt env₀ cref w :=
  ⟨fun h w hw => ((h w).mp hw).2, fun h w => ⟨fun hw => ⟨hw, h w hw⟩, fun hw => hw.1⟩⟩

/-- (B3) a restricted entry at `L` is a restricted entry at `L′` (induction on `RealChildN`). -/
theorem realChildN_up {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {c : Name} {r : Res} (h : RealChildN L env₀ c r) : RealChildN L' env₀ c r := by
  induction h with
  | run mctx cctx w w' hn rd _ synth quiet hr ih =>
    exact .run mctx cctx w w' hn rd (fun c' r' hc => ih c' r' hc) synth ((hq w).mpr ⟨quiet, rd⟩) hr

/-- (B4) and conversely (induction on `RealChildN`). -/
theorem realChildN_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {c : Name} {r : Res} (h : RealChildN L' env₀ c r) : RealChildN L env₀ c r := by
  induction h with
  | run mctx cctx w w' hn rd _ synth quiet hr ih =>
    exact .run mctx cctx w w' hn rd (fun c' r' hc => ih c' r' hc) synth ((hq w).mp quiet).1 hr

end Tools.ShippingGen5EnvCacheB
