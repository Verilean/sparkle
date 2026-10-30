import Tools.ShippingEnvSnapshot
import Tools.ShippingMachineEntry
set_option autoImplicit false
-- Built in g5env2-6f966746 (clean, exit 0, 747 jobs; first build g5env-c62ffd50). No sorry / axiom / native_decide.

/-! # DG-ENV law-free lemmas E1-E6 (scripts/gen5/DG_ENV_FREEZE.md rev1 §2, par/gen5-t2 2d8c6498)

`ReadsAt env₀ cref w`: the Core environment at `w` agrees with `env₀` on every constant it finds (one-way inclusion)
and on the three environment-derived arguments of the entry (`instancePredicate`, `userInliner`, `structEnv`).
(E1) the start world agrees with its own environment; (E2)/(E3) equal environments / an `EnvFrame` run carry it;
(E4)/(E5) what a `getConstInfo` / `getEnv` run returns at such a world; (E6) a SUFFICIENT condition for
`MachineDefines` (all-world `ReadsAt`; not shown necessary).

LAW-FREE: no `Laws`/`RefLawsAOps`/`RefLawsATele` field, no `T1Hyp`/`T1HypND` field, no `GetEnvFrame`/`ReadKeeps`/
`EnvSnapshot`. `EnvFrame` (E3) and `∀ u, ReadsAt env₀ cref u` (E6) are PREMISES of those lemmas and are supplied
nowhere. C0 stays NOT SUPPLIED (DG_ENV_FREEZE §0 S1); no M5 or FG claim. -/
namespace Tools.ShippingGen5Env
open Lean
open Sparkle.Compiler.Elab (instancePredicate userInliner structEnv entryConst certifiedShape? mixedCertifiedShape?
  machineShape? MachineShape)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt getEnv_value getConstInfo_value)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- C0 at one world: the Core environment at `w` agrees with `env₀` on every constant it finds and on the three
environment-derived arguments of the entry (DGEN §2.5 C0, with the "plus" made explicit). -/
def ReadsAt (env₀ : Environment) (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop :=
  (∀ X ci, (envAt cref w).find? X = some ci → env₀.find? X = some ci) ∧
  instancePredicate (envAt cref w) = instancePredicate env₀ ∧
  userInliner (envAt cref w) = userInliner env₀ ∧
  structEnv (envAt cref w) = structEnv env₀

/-- (E1) The start world agrees with its own environment. -/
theorem readsAt_self (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) :
    ReadsAt (envAt cref w) cref w :=
  ⟨fun _ _ h => h, rfl, rfl, rfl⟩

/-- (E2) Equal Core environments carry `ReadsAt`. -/
theorem ReadsAt.of_envEq {env₀ : Environment} {w w' : Void IO.RealWorld}
    (he : envAt cref w' = envAt cref w) (h : ReadsAt env₀ cref w) : ReadsAt env₀ cref w' := by
  unfold ReadsAt; rw [he]; exact h

/-- (E3) A run of an environment-framed operation carries `ReadsAt` (from E2 and `EnvFrame`). -/
theorem ReadsAt.of_frame {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : Tools.ShippingEnvSnapshot.EnvFrame x mctx mref cctx cref) {w w' : Void IO.RealWorld} {a : α}
    (hr : RunsTo x mctx mref cctx cref w a w') (h : ReadsAt env₀ cref w) : ReadsAt env₀ cref w' :=
  ReadsAt.of_envEq (hx w a w' hr) h

/-- (E4) The constant a `getConstInfo` run returns is `env₀`'s. -/
theorem ci_of_readsAt {env₀ : Environment} {X : Name} {w w' : Void IO.RealWorld} {ci : ConstantInfo}
    (hget : RunsTo (Lean.getConstInfo X : MetaM ConstantInfo) mctx mref cctx cref w ci w')
    (h : ReadsAt env₀ cref w) : env₀.find? X = some ci :=
  h.1 X ci (getConstInfo_value hget)

/-- (E5) The environment a `getEnv` run returns agrees with `env₀` (the `ReadsAt` conjuncts at `envR`). -/
theorem envR_of_readsAt {env₀ envR : Environment} {w w' : Void IO.RealWorld}
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w')
    (h : ReadsAt env₀ cref w) :
    (∀ X ci, envR.find? X = some ci → env₀.find? X = some ci) ∧
    instancePredicate envR = instancePredicate env₀ ∧ userInliner envR = userInliner env₀ ∧
    structEnv envR = structEnv env₀ := by
  rw [getEnv_value henv]; exact h

/-- (E6) A SUFFICIENT condition only: `ReadsAt env₀` at EVERY world, plus the gate/shape facts computed from
`env₀`, gives `MachineDefines` (T1Hyp.defines' form). Conditional: `hall` is NOT supplied anywhere, and no necessity is
claimed. -/
theorem machineDefines_of_readsAll {env₀ : Environment} {c : Name} {ci₀ : ConstantInfo} {shape : MachineShape}
    (hall : ∀ u, ReadsAt env₀ cref u) (hc : env₀.find? c = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape) :
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c shape := by
  intro w1 ci w2 w5 envR w6 w7 envR' w8 hget henv henv'
  have hci : ci = ci₀ := Option.some.inj ((ci_of_readsAt hget (hall w1)).symm.trans hc)
  obtain ⟨-, hi, hu, hs⟩ := envR_of_readsAt henv (hall w5)
  obtain ⟨-, -, -, hs'⟩ := envR_of_readsAt henv' (hall w7)
  subst hci
  rw [hi, hu, hs, hs']
  exact ⟨hg1, hg2, hsh⟩

end Tools.ShippingGen5Env
