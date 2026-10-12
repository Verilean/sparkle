import Tools.ShippingLegacySemTrace
import Tools.ShippingChildVC

/-! # Inversion steps for walking a large handler without normalising it

`split`, `dsimp only` and `simp` on an unfolded legacy handler run out of
steps (the join points of its early `return`s are duplicated when inlined —
observed on `Rec.handleDefinitionUnfold`). The lemmas here invert ONE
construct at the head of a program; applied to a hypothesis
`Returns P ctx s r t`, the unifier reduces the head of `P` as far as needed
(the `have __do_jp := …` of a join point, a beta-redex, a `match` on a
constructor) and nothing else.

* `returns_ite` — an `if`: its condition and the taken branch's run.
* `returns_trace_then` — `trace[cls] msg` followed by a continuation: the
  continuation's run from the same builder state. The shape matched is what
  the `trace[…]` macro leaves inside a `do` block (observed in the build log
  of `handleBitVecOps`): `isTracingEnabledFor cls >>= fun b => if b = true
  then addTrace cls msg >>= fun _ => P else P`.
* `profHandler_returns` — the profile wrapper around a handler call
  (`profHandler i k`, a PRIVATE definition of `Sparkle.Compiler.Elab`, named
  here with `privConst%`): a run of the wrapper is a run of `k`, same states,
  same result; the two clock reads and the two counter updates are lifted
  oracles.

Expected shape of `profHandler i k` (NOT observed):
`liftMetaM IO.monoMsNow >>= fun t0 => k >>= fun r => liftMetaM IO.monoMsNow
 >>= fun t1 => liftMetaM (calls.modify …) >>= fun _ => liftMetaM (ms.modify …)
 >>= fun _ => pure r`. -/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- An `if` at the head: the condition's truth and the taken branch's run. -/
theorem returns_ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : Returns (if c then a else b) ctx s r t) :
    (c ∧ Returns a ctx s r t) ∨ (¬c ∧ Returns b ctx s r t) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

/-- `trace[cls] msg` and then `P`: a run of `P` from the same builder state. -/
theorem returns_trace_then {α : Type} {cls : Name} {msg : MessageData} {P : CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : Returns ((Lean.isTracingEnabledFor cls : CompilerM Bool) >>= fun b =>
        if b = true then ((Lean.addTrace cls msg : CompilerM Unit) >>= fun _ => P) else P)
      ctx s r t) :
    Returns P ctx s r t := by
  obtain ⟨b, s1, hen, k1⟩ := Returns.bind h
  have hs1 : s1 = s := isTracingEnabledFor_frame cls b s1 hen
  rw [hs1] at k1
  rcases returns_ite k1 with ⟨_, k2⟩ | ⟨_, k2⟩
  · obtain ⟨u, s2, hadd, k3⟩ := Returns.bind k2
    have hs2 : s2 = s := addTrace_frame cls msg u s2 hadd
    rw [hs2] at k3
    exact k3
  · exact k2

/-- The profile wrapper adds nothing to the builder state or the result. -/
theorem profHandler_ensures {α : Type} (i : Nat) (k : CompilerM α) {ctx : CompilerState}
    {s : CircuitState} {Q : α → CircuitState → Prop} (h : Ensures k ctx s Q) :
    Ensures ((privConst% Sparkle.Compiler.Elab Sparkle.Compiler.Elab.profHandler) i k) ctx s Q := by
  unfoldPriv Sparkle.Compiler.Elab Sparkle.Compiler.Elab.profHandler
  refine Ensures.bindLift (fun t0 _ => ?_)
  refine Ensures.bindRun (fun r s1 hr => ?_)
  refine Ensures.bindLift (fun t1 _ => ?_)
  refine Ensures.bindLift (fun _ _ => ?_)
  refine Ensures.bindLift (fun _ _ => ?_)
  exact Ensures.pure (h r s1 hr)

/-- A run of the wrapper is a run of the wrapped handler. -/
theorem profHandler_returns {α : Type} {i : Nat} {k : CompilerM α} {ctx : CompilerState}
    {s t : CircuitState} {r : α}
    (h : Returns ((privConst% Sparkle.Compiler.Elab Sparkle.Compiler.Elab.profHandler) i k)
      ctx s r t) :
    Returns k ctx s r t :=
  profHandler_ensures i k (Q := fun r t => Returns k ctx s r t) (fun _ _ hr => hr) r t h

end Tools.ShippingLegacySem
