import Tools.ShippingFGCircuitS1iHead
set_option autoImplicit false
-- FG circuit pilot S1i, unit 2: the checked environment `env₀` and the start world, as ONE named premise `CheckedStart`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1i-2: `CheckedStart` (env₀ and the run's start environment, through `ReadsAt`)

S1h-3 moved three statements about the start environment to `env₀` plus `ReadsAt env₀ cref w`.  Here they are bundled:
* `CheckedEnv lvl env₀ X ty val dd`: facts about ONE environment.  `root` is the part that is **a statement on types**: `env₀.find? X = some (.defnInfo d)` with `d.levelParams = []`, `d.type = ty`, `d.value = val`, where `ty`/`val` are the closed kernel terms of the declaration (`counterLoopType`, `counterLoopValue`, …).
  `gates` (`entryGatesB env₀ X = true`) and `reader` (`ReaderAt`: `machineShape?` and the `partial` `dataOfAt`) are **evaluations**: an `Environment` is a runtime object, so they are checked by running the functions on a built environment in `MetaM` (Check8 SNAPSHOT8), not by the kernel.
* `CheckedStart …`: `CheckedEnv` plus `ReadsAt env₀ cref w` (DG-ENV C0; the start world's constants are `env₀`'s and its three derived arguments are equal).

What `root` already fixes on types (`entry₀_of_rootInEnv`, `entryGatesB_of_rootInEnv`): the entry constant of `env₀` is `entryConst true false [] (.defnInfo d) (instancePredicate env₀) (userInliner env₀) (structEnv env₀)` for the declaration `d` with the closed type and value, and the gate checker
is the pair of `isNone` tests on exactly that term.  So the only dependence of `gates` and `reader` on `env₀` beyond the closed declaration is through the three derived arguments `instancePredicate`, `userInliner`, `structEnv` — the same three `ReadsAt` equates.  That is the extent to which `env₀` being "the environment with the counterLoop declaration" is shown without evaluation;
the values of `certifiedShape?`/`mixedCertifiedShape?`/`machineShape?`/`dataOfAt` on that term with the real derived arguments are not kernel-evaluable (`userInliner` unfolds the environment, `dataOfAt` is a `partial` helper). -/
namespace Tools.ShippingFGCircuitS1iEnv
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env (ReadsAt)

/-- facts about one environment: the root is a closed declaration (types), the gates and the reader outputs (evaluations) -/
structure CheckedEnv (lvl : Lean.Expr → Nat) (env₀ : Environment) (X : Name) (ty val : Lean.Expr)
    (dd : Tools.ShippingMachineAuto.MachineData) : Prop where
  root : ∃ d : DefinitionVal, RootInEnv env₀ X ty val d
  gates : entryGatesB env₀ X = true
  reader : ReaderAt lvl env₀ X dd

/-- the single named premise: a checked environment, read by the start world -/
structure CheckedStart (lvl : Lean.Expr → Nat) (env₀ : Environment) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (X : Name) (ty val : Lean.Expr) (dd : Tools.ShippingMachineAuto.MachineData) : Prop where
  env : CheckedEnv lvl env₀ X ty val dd
  link : ReadsAt env₀ cref w

theorem quoteAt_of_rootInEnv {env : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal}
    (h : RootInEnv env X ty val d) : QuoteAt env X ty val := by
  intro ci hci
  obtain ⟨hf, hl, ht, hv⟩ := h
  rw [hf] at hci
  cases Option.some.inj hci
  exact ⟨d, rfl, hl, ht, hv⟩

/-- on types: the entry constant of an environment with the root is the closed declaration with the three environment-derived arguments -/
theorem entry₀_of_rootInEnv {env : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal}
    (h : RootInEnv env X ty val d) :
    Tools.ShippingGen5Acc.entry₀ env X =
      some (entryConst true false [] (.defnInfo d) (instancePredicate env) (userInliner env) (structEnv env)) := by
  unfold Tools.ShippingGen5Acc.entry₀
  rw [h.1]; rfl

/-- on types: the gate checker is the pair of `isNone` tests on that term -/
theorem entryGatesB_of_rootInEnv {env : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal}
    (h : RootInEnv env X ty val d) :
    entryGatesB env X =
      ((certifiedShape? false [] (entryConst true false [] (.defnInfo d) (instancePredicate env) (userInliner env) (structEnv env))).isNone &&
       (mixedCertifiedShape? false [] (entryConst true false [] (.defnInfo d) (instancePredicate env) (userInliner env) (structEnv env)) (instancePredicate env)).isNone) := by
  unfold entryGatesB
  rw [entry₀_of_rootInEnv h]

/-- the start-environment facts the endpoint theorems need, from `CheckedStart` and the lookup the run supplies -/
theorem startFacts_of_checked {lvl : Lean.Expr → Nat} {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {X : Name} {ty val : Lean.Expr} {dd : Tools.ShippingMachineAuto.MachineData}
    (h : CheckedStart lvl env₀ cref w X ty val dd) (hfind : ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci) :
    EntryGates (envAt cref w) X ∧ (∃ d : DefinitionVal, RootInEnv (envAt cref w) X ty val d) ∧ RootReader lvl (envAt cref w) X dd := by
  obtain ⟨d0, hroot⟩ := h.env.root
  have hq := quoteAt_of_readsAt h.link (quoteAt_of_rootInEnv hroot)
  have hr := readerAt_of_readsAt h.link h.env.reader
  obtain ⟨hE, hRead⟩ := rootEnv_of_lookup hq hr hfind
  exact ⟨entryGatesB_sound (entryGatesB_of_readsAt h.link h.env.gates), hE, hRead⟩

/-- a start world whose constants are `env₀`'s and a root found in the start environment has the root as in `env₀` (the lookup is `env₀`'s) -/
theorem find_eq_of_checked {lvl : Lean.Expr → Nat} {env₀ : Environment} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {X : Name} {ty val : Lean.Expr} {dd : Tools.ShippingMachineAuto.MachineData}
    (h : CheckedStart lvl env₀ cref w X ty val dd) {ci : ConstantInfo} (hf : (envAt cref w).find? X = some ci) :
    ∃ d : DefinitionVal, ci = .defnInfo d ∧ d.levelParams = [] ∧ d.type = ty ∧ d.value = val :=
  quoteAt_of_readsAt h.link (quoteAt_of_rootInEnv h.env.root.choose_spec) ci hf

end Tools.ShippingFGCircuitS1iEnv

#print axioms Tools.ShippingFGCircuitS1iEnv.startFacts_of_checked
#print axioms Tools.ShippingFGCircuitS1iEnv.entryGatesB_of_rootInEnv
