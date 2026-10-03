import Tools.ShippingMuxRecursionSoundness
import Tests.Compiler.ShippingMuxLoweringSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingMuxRecursionSoundnessTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMuxRecursionSoundness

def yes : Signal defaultDomain Bool := Signal.pure true
def no : Signal defaultDomain Bool := Signal.pure false
def high : Signal defaultDomain (BitVec 8) := Signal.pure 251#8
def low : Signal defaultDomain (BitVec 8) := Signal.pure 7#8
def nestedBranch : Signal defaultDomain (BitVec 8) := Signal.mux yes high low
def whole : Signal defaultDomain (BitVec 8) := Signal.mux no low nestedBranch

run_cmd liftTermElabM do
  -- Exercise the exact extracted sequence with the shipping recursive entry
  -- and the real type query. Record the order at its boundary, including the
  -- nested mux inside a child. Repeated branches allow existing-wire results.
  for (cond, branch, expected) in [( ``yes, ``low, 251), (``no, ``low, 7),
      (``no, ``high, 251), (``no, ``nestedBranch, 251)] do
    let order ← IO.mkRef ([] : List String)
    let translate : TranslateFn := fun e hint top named => do
      if top || named then throwError "mux child flags changed"
      CompilerM.liftMetaM (order.modify (· ++ [hint]))
      translateExprToWire e hint top named
    let query : CompilerM Sparkle.IR.Type.HWType := do
      unless (← CompilerM.liftMetaM order.get) == ["mux_cond", "mux_then", "mux_else"] do
        throwError "mux type query ran before all children"
      let exprType ← cachedInferType (mkConst ``whole)
      inferHWTypeFromSignal exprType
    let (w, final) ← ((translateMuxWith translate query (mkConst cond) (mkConst ``high)
      (mkConst branch) "mux_then" true) {}).run (CircuitM.init "RecursiveMux")
    let m := final.module.finalize
    let some result := evalAssigns (Sparkle.IR.RegDedup.declWidth m)
        (fun _ _ => 0) m.body (fun _ => 0) |
      throwError "recursive mux evaluation failed"
    unless result w == expected do
      throwError "recursive mux result mismatch: {result w}, expected {expected}"
  -- A mux translates both branches, even for a true constant condition.
  -- Extraction must not silently change compiler failure/strictness behavior.
  let failElse : TranslateFn := fun _ hint _ _ =>
    if hint == "mux_else" then throwError "expected else failure" else pure "existing"
  let queried ← IO.mkRef false
  let queryAfterFailure : CompilerM Sparkle.IR.Type.HWType := do
    CompilerM.liftMetaM (queried.set true)
    pure (.bitVector 8)
  let failed ← try
    let _ ← ((translateMuxWith failElse queryAfterFailure
      (mkConst ``yes) (mkConst ``high) (mkConst ``low) "out" false) {}).run
      (CircuitM.init "StrictMux")
    pure false
    catch _ => pure true
  unless failed do throwError "mux stopped translating its else branch"
  if ← queried.get then throwError "mux type query ran after child failure"

run_cmd do
  if (← get).messages.hasErrors then throwError "mux recursion regression failed"
  for name in [``translateMuxWith_returns, ``translateMuxWith_correct] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mux recursion axiom: {name}: {ax}"
  logInfo "SHIPPING MUX RECURSION OK: real recursive sequence, source mux value, reserved-wire frame and typed body; child contracts and type query remain explicit"

end Sparkle.Tests.Compiler.ShippingMuxRecursionSoundnessTest
