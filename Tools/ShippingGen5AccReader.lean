import Tools.ShippingGen5AccGates
import Tools.ShippingMachineCommand
import Tools.ShippingEnvSnapshot
set_option autoImplicit false
-- NOT BUILT yet (g5ac-r12, A6c): the build SHA is recorded here by a comment-only commit after the Pod build. No sorry / axiom / native_decide.

/-! # DG-ACC unit A6c: `GateRunsAt` from one reader run (scripts/gen5/DG_ACC_FREEZE_REV6.md §1)

PROVED here (conditionally): from `ReaderRunsAt` (one `readMachine c false` run per reached name found in `env₀`, whose start world satisfies
`ReadsAt env₀`), the existing premise `GetEnvFrame`, and `hshape` (the statement of `readMachine_gates`, dg-readkinds U8d, as a premise of its
exact type), `GateRunsAt` follows, using the linked `getEnv` end world `w1` as the `getConstInfo` start (`ReadsAt.of_frame`), and then `GatesNoneAt`.

LIMITS: `GetEnvFrame`, `ReaderRunsAt` and the start `ReadsAt` are INPUTS. "law-free" means only that no new law is introduced; it does NOT mean those
inputs are supplied. `hshape` is not discharged here (`readMachine_gates` is on a branch that is not an ancestor of this checkout); discharging it
is an obligation to verify at the integration SHA. NOT supplied: a reader run, `ReadsAt` at any start world, `ReachCover`, `ClosesOfShape`,
`ReadsSupplyAt`, `DataOfShape`, off-route, `GenSFacts`. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEnvSnapshot (GetEnvFrame)

/-- The statement of `readMachine_gates` (dg-readkinds U8d), for one name, with `GenEntry ci env` written out as `entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)`. -/
def ReaderGateShape (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (c : Name) : Prop :=
  ∀ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
    RunsTo (readMachine c false) mctx mref cctx cref w r w' →
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
        (instancePredicate env) = none

/-- For every reached name found in `env₀`: one successful `readMachine c false` run whose start world satisfies `ReadsAt env₀`. -/
def ReaderRunsAt (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
      ReadsAt env₀ cref w ∧ RunsTo (readMachine c false) mctx mref cctx cref w r w'

theorem gateRunsAt_of_readerRuns {env₀ : Environment} (mctx : Meta.Context)
    (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (Reach : Name → Prop) (hg : GetEnvFrame mctx mref cctx cref)
    (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c)
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) : GateRunsAt env₀ mctx mref cctx cref Reach := by
  intro c hc ci₀ hf
  obtain ⟨w, r, w', hw, hrun⟩ := h c hc ci₀ hf
  obtain ⟨ci, env, w1, w2, he, hci, hg1, hg2⟩ := hshape c hc w r w' hrun
  exact ⟨w, env, w1, w1, ci, w2, hw, Tools.ShippingGen5Env.ReadsAt.of_frame hg he hw, he, hci, hg1, hg2⟩

theorem gatesNoneAt_of_readerRuns {env₀ : Environment} (mctx : Meta.Context)
    (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (Reach : Name → Prop) (hg : GetEnvFrame mctx mref cctx cref)
    (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c)
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) : GatesNoneAt env₀ Reach :=
  gatesNoneAt_of_gateRunsAt mctx mref cctx cref Reach (gateRunsAt_of_readerRuns mctx mref cctx cref Reach hg hshape h)

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.gateRunsAt_of_readerRuns
#print axioms Tools.ShippingGen5Acc.gatesNoneAt_of_readerRuns
