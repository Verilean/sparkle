import Tools.ShippingGen5AccRoute
set_option autoImplicit false
-- Built in the Pod (g5ac-r10) at 5b542e30: `kjob lake build Tools.ShippingGen5AccGates`, exit 0, 722 jobs. Not yet a clean issue-linked build (the coder runs it). No sorry / axiom / native_decide.

/-! # DG-ACC unit A6b: `GatesNoneAt` from reader runs (scripts/gen5/DG_ACC_FREEZE_REV5.md §2)

PROVED here: `gatesNoneAt_of_gateRunsAt` transports the two gate refusals from the entry built out of a `getEnv` run result and a
`getConstInfo` run result (at worlds where `ReadsAt env₀` holds) to the entry built from `env₀` and the `env₀`-found constant.

`GateRunsAt` drops `wE' = w1` (the connection of the two runs), so it is NOT the conclusion of `readMachine_gates` itself; it is a weaker
sufficient interface that can be built from that conclusion. At integration the linked witness of the same reader run is to be supplied
(an obligation, not done here).

NOT supplied here (this investigation found no supplier or route): a `readMachine c false` run for any reached name, `ReadsAt` at the two
worlds, `ReachCover`, `ClosesOfShape`, `ReadsSupplyAt`, `DataOfShape`, off-route, `GenSFacts`. The parts that could supply them
(`readMachine_gates` etc.) live on branches that are not ancestors of this checkout; this is a limit of the current un-integrated checkout,
not a permanent import impossibility. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
open Tools.ShippingGen5Env (ReadsAt ci_of_readsAt envR_of_readsAt)

/-- For every reached name found in `env₀`: a `getEnv` run and a `getConstInfo` run at worlds where the Core environment agrees with `env₀`
(`ReadsAt`), with both gate refusals at the entry built from THOSE run results. -/
def GateRunsAt (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ wE envR wE' w1 ci w2,
      ReadsAt env₀ cref wE ∧ ReadsAt env₀ cref w1 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none

theorem gatesNoneAt_of_gateRunsAt {env₀ : Environment} (mctx : Meta.Context)
    (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (Reach : Name → Prop) (h : GateRunsAt env₀ mctx mref cctx cref Reach) : GatesNoneAt env₀ Reach := by
  intro c ci₀ hc hf
  obtain ⟨wE, envR, wE', w1, ci, w2, hrE, hr1, hE, hG, hg1, hg2⟩ := h c hc ci₀ hf
  have hci : ci = ci₀ := Option.some.inj ((ci_of_readsAt hG hr1).symm.trans hf)
  obtain ⟨-, hi, hu, hs⟩ := envR_of_readsAt hE hrE
  subst hci
  rw [hi, hu, hs] at hg1 hg2
  exact ⟨hg1, hg2⟩

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.gatesNoneAt_of_gateRunsAt
