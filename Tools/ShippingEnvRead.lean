import Tools.ShippingReflectCtx
import Tools.ShippingCallWidthsStructRes

/-! # `DeclTypeReadAt` / `FieldsAt` reduced to ONE environment-read agreement

BUILT (run er1 exit 0; axioms run axe: all three [propext, Classical.choice, Quot.sound]). Integrator, 2026-10-19 (reviewer: discharge DR/FA from captured-environment facts of the actual runs, not
from a global immutability assumption; no indefinite reformulation).

PROVED here: a successful `getConstInfo c` returns the constant `find?` gives in the environment a `getEnv` run
from the SAME world returns (`getConstInfo_find`). Hence, for an environment `envP`:

* `DeclTypeReadAt envP c` follows from `EnvAt envP`: every `getEnv` run (from any world, any contexts) returns
  `envP` (`declTypeRead_of_envAt`);
* `FieldsAt envP c` follows from `EnvAt envP` (`fieldsAt_of_envAt`).

`EnvAt envP` is NOT proved and is still GLOBAL over worlds — exactly the shape the reviewer rejects as a final
answer. What would discharge it for the ACTUAL runs (identified, not done): an environment frame law in the world
invariant — a field `env : World → Environment` of `RefLaws` with `getEnv` returning it and every operation of
the synthesis between the parent reader's `getEnv` and the child's `getConstInfo` leaving it unchanged (no
`addDecl`/`modifyEnv` on that path) — a NEW runtime law of the same kind as `RefLaws.frame`, to be carried by the
invariant `InvV` and restated per world (`EnvAtW L w`). The two premises DR and FA then collapse to that one
law plus "the parent's `envP` is the environment at the parent's start world". Not started: it changes
`RefLaws` (a trust-boundary change needing a ruling). -/
namespace Tools.ShippingEnvRead
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingReflectCtx Tools.ShippingChildInv
open Tools.ShippingCallWidthsStructRes

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A successful `getConstInfo` reads the environment**: some `getEnv` run from the same world returns an
environment in which `find?` gives the returned constant. -/
theorem getConstInfo_find (c : Name) {w ci w'}
    (h : RunsTo (Lean.getConstInfo c : MetaM ConstantInfo) mctx mref cctx cref w ci w') :
    ∃ env w1, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      env.find? c = some ci := by
  unfold Lean.getConstInfo at h
  obtain ⟨env, w1, he, hm⟩ := RunsTo.bind h
  refine ⟨env, w1, he, ?_⟩
  cases hf : env.find? c with
  | none => rw [hf] at hm; exact (throwUnknownConstant_not_runs c hm).elim
  | some i =>
    rw [hf] at hm
    obtain ⟨rfl, -⟩ := RunsTo.pure_world hm
    rfl

/-- Every `getEnv` run returns `envP` (GLOBAL over worlds and contexts; see the header). -/
def EnvAt (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (envP : Environment) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) (env : Environment)
    (w' : Void IO.RealWorld),
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w' → env = envP

theorem declTypeRead_of_envAt {envP : Environment} (c : Name) (hE : EnvAt mref cref envP) :
    DeclTypeReadAt mref cref envP c := by
  intro mctx cctx w1 ci w2 hg ci' hf
  obtain ⟨env, w3, he, hfind⟩ := getConstInfo_find c hg
  rw [hE mctx cctx w1 env w3 he, hf] at hfind
  cases hfind
  rfl

theorem fieldsAt_of_envAt {envP : Environment} (c : Name) (hE : EnvAt mref cref envP) :
    FieldsAt mref cref envP c := by
  intro mctx cctx w5 envR w6 he _ _ _ _ _ _
  rw [hE mctx cctx w5 envR w6 he]

end Tools.ShippingEnvRead
