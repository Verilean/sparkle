import Sparkle

/-! # PROBE (not in `Tests.AllTests`): does a caller-supplied `canUnfold?` break the `Framed.whnf` laws?

`RefLaws.frame` (`Tools/ShippingChildInv.lean`, constructor `Framed.whnf`, about line 214) states that
`Lean.Meta.whnf e` leaves the three tracked refs (`sparkleChildCache`, `sparkleChildSynth`,
`sparkleSynthDepth`) unchanged on every outcome, in EVERY `Meta.Context`; `RefLaws.excOk` states that
an exception a `Framed` op throws from a quiet world is `OkExc` (its message in the class `OkMsg`,
which has no `ofLazy` leaf).

`Meta.Context.canUnfold? : Option (Config → ConstantInfo → CoreM Bool)` is a CALLBACK the context
carries; `whnf` reaches it through `getUnfoldableConst?` → `canUnfold`
(`Lean/Meta/GetUnfoldableConst.lean`, toolchain v4.32.1, line 33). This probe installs a callback
(`withCanUnfoldPred`) and runs `whnf` on an application of a user definition:

* case W (write): the callback sets `sparkleSynthDepth` to `before + 41` and records that it ran in a
  run-local ref. ASSERTS: the callback ran, and the depth read after `whnf` differs from before.
* case E (exception): the callback throws an error whose message is `MessageData.ofLazy …`.
  ASSERTS: `whnf` throws, and the caught exception's message is an `ofLazy` node (not in `OkMsg`'s
  constructors).

Everything is restored in `finally` (the depth ref is set back to its value before the probe).
Only the tracked depth ref and a probe-local ref are written; nothing re-typed, no file handles. -/

namespace Sparkle.Tests.Compiler.CanUnfoldProbe
open Lean Meta Elab

def probeTarget (n : Nat) : Nat := n + 1

/-- Is the message (under any context / tag wrappers) an `ofLazy` node? -/
partial def isLazy : MessageData → Bool
  | .ofLazy .. => true
  | .withContext _ m => isLazy m
  | .withNamingContext _ m => isLazy m
  | .tagged _ m => isLazy m
  | .nest _ m => isLazy m
  | .group m => isLazy m
  | _ => false

run_meta do
  let before ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
  try
    -- case W
    let called ← IO.mkRef false
    let e := mkApp (mkConst ``probeTarget) (mkNatLit 3)
    let pred : Config → ConstantInfo → CoreM Bool := fun _ info => do
      if info.name == ``probeTarget then
        called.set true
        Sparkle.Compiler.Elab.sparkleSynthDepth.set (before + 41)
      return true
    let r ← withCanUnfoldPred pred (whnf e)
    let after ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
    let ran ← called.get
    logInfo m!"CANUNFOLD W: callback ran = {ran}; depth before = {before}, after whnf = {after}; whnf result = {r}"
    unless ran do throwError "CANUNFOLD W: the callback was NOT called (probe inconclusive)"
    unless after != before do throwError "CANUNFOLD W: depth unchanged (no counterexample)"
    logInfo m!"CANUNFOLD W REPRODUCED: whnf in a context with canUnfold? changed sparkleSynthDepth ({before} -> {after})"
    Sparkle.Compiler.Elab.sparkleSynthDepth.set before
    -- case E
    let thrower : Config → ConstantInfo → CoreM Bool := fun _ info => do
      if info.name == ``probeTarget then
        throwError (MessageData.lazy (fun _ => pure (MessageData.ofFormat "probe")))
      return true
    let res ← try
        let r ← withCanUnfoldPred thrower (whnf e)
        pure (Sum.inl r)
      catch ex => pure (Sum.inr ex)
    match res with
    | .inl r =>
      logInfo m!"CANUNFOLD E: whnf returned {r} (the exception did not escape)"
      throwError "CANUNFOLD E: no exception escaped (not reproduced)"
    | .inr ex =>
      let lazy := isLazy ex.toMessageData
      logInfo m!"CANUNFOLD E: whnf threw; message is ofLazy = {lazy}"
      unless lazy do throwError "CANUNFOLD E: escaped message is not ofLazy (not reproduced)"
      logInfo m!"CANUNFOLD E REPRODUCED: whnf threw an exception whose message is an ofLazy node"
  finally
    Sparkle.Compiler.Elab.sparkleSynthDepth.set before
    let fin ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
    logInfo m!"CANUNFOLD restored depth = {fin} (before = {before})"

end Sparkle.Tests.Compiler.CanUnfoldProbe
