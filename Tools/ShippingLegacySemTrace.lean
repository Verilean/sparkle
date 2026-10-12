import Tools.ShippingLegacySemCalc

/-! # `trace[cls] …` in `CompilerM` leaves the builder state

Every arm of the legacy translator starts with a `trace[sparkle.compiler] …`.
The macro expands to
`do let cls := …; if (← Lean.isTracingEnabledFor cls) then Lean.addTrace cls msg`.
To walk past one with `Returns`, its two actions have to be shown to leave
the builder state. Both are generic programs instantiated at `CompilerM`,
whose `MonadTrace` / `MonadOptions` / `MonadRef` / `AddMessageContext`
instances are the lifted `MetaM` ones.

**Proved here**: `isTracingEnabledFor_frame`, `addTrace_frame`.

**Expected elaborated shapes** (NOT observed — this file is the first to
invert these two programs with `Returns`; `vc` walks them for `Keeps` in
`Tools/ShippingChildHelpers.lean`, matching their leaves as `liftM _`):

* `Lean.isTracingEnabledFor cls : CompilerM Bool` unfolds to
  `MonadTrace.getInheritedTraceOptions >>= fun a => getOptions >>= fun b =>
   pure (checkTraceOption a b cls)`, both actions being
  `liftM (… : MetaM _)` through the two `MonadLift` instances — the same term
  as `CompilerM.liftMetaM (… : MetaM _)` up to unfolding. The first inversion
  is `Ensures.bindLift`, which has to unify `CompilerM.liftMetaM ?x` with the
  lifted instance method.
* `Lean.addTrace cls msg : CompilerM Unit` unfolds to
  `getRef >>= fun ref => addMessageContext msg >>= fun msg =>
   modifyTraces (·.push …)`, `modifyTraces f` to `modifyTraceState …`; all
  three lifted likewise.

If the unifier does not see a lifted method as `CompilerM.liftMetaM _`, the
goal left by `lift_walk` shows the form it has. -/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- A lifted oracle leaves the builder state. -/
theorem Ensures.lift_frame {α : Type} {x : MetaM α} {ctx : CompilerState} {s : CircuitState} :
    Ensures (CompilerM.liftMetaM x) ctx s (fun _ t => t = s) := by
  intro a t hr
  exact Returns.liftMetaM hr

/-- Close `Ensures P ctx s (fun _ t => t = s)` for a program built from lifted
oracles, `pure`, `>>=` and `if` / `match`. -/
macro "lift_walk" : tactic =>
  `(tactic| repeat' (first
      | exact Ensures.pure rfl
      | exact Ensures.lift_frame
      | refine Ensures.bindLift (fun _ _ => ?_)
      | split))

theorem isTracingEnabledFor_frame (cls : Name) {ctx : CompilerState} {s : CircuitState} :
    Ensures (Lean.isTracingEnabledFor cls : CompilerM Bool) ctx s (fun _ t => t = s) := by
  unfold Lean.isTracingEnabledFor
  lift_walk

theorem addTrace_frame (cls : Name) (msg : MessageData) {ctx : CompilerState}
    {s : CircuitState} :
    Ensures (Lean.addTrace cls msg : CompilerM Unit) ctx s (fun _ t => t = s) := by
  unfold Lean.addTrace Lean.modifyTraces
  lift_walk

end Tools.ShippingLegacySem
