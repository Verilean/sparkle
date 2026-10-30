import Tools.ShippingGen5Env
set_option autoImplicit false
-- Built in g5envr-8ebda2f3 (clean, exit 0, 749 jobs). No sorry / axiom / native_decide.

/-! # DG-ENV unit (a): the relative `defines` candidate D2 (scripts/gen5/DG_ENV_FREEZE.md rev2.1 §4.4.3, par/gen5-t2 f5169a75)

`MachineDefinesR env₀ …`: `MachineDefines` (ShippingMachineEntry.lean:2345-2358) with three `ReadsAt env₀` premises at
the read worlds `w1`, `w5`, `w7`; the three conjuncts verbatim. (R1) old ⇒ new: `MachineDefines ⇒ MachineDefinesR`.
(R2) the supplier from `env₀`-side facts (E6's proof with the per-world premises in place of `hall`).

A CANDIDATE definition only: `T1Hyp.defines`/`T1HypND.defines` are NOT changed (that would be a shared-definition
change, unapproved). LAW-FREE: no `Laws`/`T1Hyp`/`T1HypND` field, no `GetEnvFrame`/`ReadKeeps`/`EnvSnapshot`.
No M5 or FG claim. -/
namespace Tools.ShippingGen5Env
open Lean
open Sparkle.Compiler.Elab (instancePredicate userInliner structEnv entryConst certifiedShape? mixedCertifiedShape?
  machineShape? MachineShape)
open Tools.ShippingEntrySoundness (RunsTo)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- D2: `MachineDefines` at read worlds where the environment agrees with `env₀`. -/
def MachineDefinesR (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ w1 ci w2 w5 envR w6 w7 envR' w8,
    ReadsAt env₀ cref w1 → ReadsAt env₀ cref w5 → ReadsAt env₀ cref w7 →
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (structEnv envR') = some shape

/-- (R1) old ⇒ new. -/
theorem machineDefinesR_of_defines {env₀ : Environment} {declName : Name} {shape : MachineShape}
    (h : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName shape) :
    MachineDefinesR env₀ mctx mref cctx cref declName shape :=
  fun w1 ci w2 w5 envR w6 w7 envR' w8 _ _ _ hget henv henv' => h w1 ci w2 w5 envR w6 w7 envR' w8 hget henv henv'

/-- (R2) The supplier from `env₀`-side facts (E6 with per-world `ReadsAt` in place of `hall`). -/
theorem machineDefinesR_of_env {env₀ : Environment} {c : Name} {ci₀ : ConstantInfo} {shape : MachineShape}
    (hc : env₀.find? c = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape) :
    MachineDefinesR env₀ mctx mref cctx cref c shape := by
  intro w1 ci w2 w5 envR w6 w7 envR' w8 h1 h5 h7 hget henv henv'
  have hci : ci = ci₀ := Option.some.inj ((ci_of_readsAt hget h1).symm.trans hc)
  obtain ⟨-, hi, hu, hs⟩ := envR_of_readsAt henv h5
  obtain ⟨-, -, -, hs'⟩ := envR_of_readsAt henv' h7
  subst hci
  rw [hi, hu, hs, hs']
  exact ⟨hg1, hg2, hsh⟩

end Tools.ShippingGen5Env
