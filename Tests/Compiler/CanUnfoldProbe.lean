import Sparkle
import Tools.ShippingOkMsgGoal

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
* case E (exception, lazy): the callback throws an error whose message is `MessageData.lazy …`.
  ASSERTS: `whnf` throws, and the caught exception's message is an `ofLazy` node. This shows only that
  an ARBITRARY lazy exception from a callback propagates through `whnf`; it does NOT show the message is
  outside `OkMsg` (the class contains the lazy leaves `ofExpr` / `ofConstName`).
* case G (exception, goal): the callback throws `MessageData.ofGoal g`. ASSERTS: `whnf` throws and the
  escaped message satisfies `Tools.ShippingOkMsgGoal.hasGoal = true`; by the kernel lemma
  `not_okMsg_of_hasGoal` such a message is NOT in `OkMsg`, so the escaped exception is not `OkExc`.
  This is NOT an unconditional counterexample to `excOk`: `excOk` also requires the start world to be
  `quiet`, which the probe does not check.

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
      logInfo m!"CANUNFOLD E REPRODUCED (propagation only): an arbitrary lazy exception from the callback escaped whnf"
    -- case G
    let g := (← mkFreshExprMVar (mkConst ``Nat)).mvarId!
    let goalThrower : Config → ConstantInfo → CoreM Bool := fun _ info => do
      if info.name == ``probeTarget then
        throwError (MessageData.ofGoal g)
      return true
    let resG ← try
        let r ← withCanUnfoldPred goalThrower (whnf e)
        pure (Sum.inl r)
      catch ex => pure (Sum.inr ex)
    match resG with
    | .inl r =>
      logInfo m!"CANUNFOLD G: whnf returned {r} (the exception did not escape)"
      throwError "CANUNFOLD G: no exception escaped (not reproduced)"
    | .inr ex =>
      let hg := Tools.ShippingOkMsgGoal.hasGoal ex.toMessageData
      logInfo m!"CANUNFOLD G: whnf threw; hasGoal of the escaped message = {hg}"
      unless hg do throwError "CANUNFOLD G: escaped message has no ofGoal node (not reproduced)"
      logInfo m!"CANUNFOLD G REPRODUCED: the escaped exception's message has an ofGoal node, hence is not OkMsg (kernel lemma Tools.ShippingOkMsgGoal.not_okMsg_of_hasGoal); quiet of the start world NOT checked"
  finally
    Sparkle.Compiler.Elab.sparkleSynthDepth.set before
    let fin ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
    logInfo m!"CANUNFOLD restored depth = {fin} (before = {before})"

end Sparkle.Tests.Compiler.CanUnfoldProbe
