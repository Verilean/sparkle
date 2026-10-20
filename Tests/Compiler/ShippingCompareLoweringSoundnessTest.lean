import Tools.ShippingCompareLoweringSoundness
import Tests.Compiler.ShippingBoolSourceSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingCompareLoweringSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingCompareLoweringSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingEntrySoundness

def lt1 {dom : DomainConfig} (a b : Signal dom (BitVec 1)) := Signal.ult a b
def le1 {dom : DomainConfig} (a b : Signal dom (BitVec 1)) := Signal.ule a b
def lt65 {dom : DomainConfig} (a b : Signal dom (BitVec 65)) := Signal.ult a b
def le65 {dom : DomainConfig} (a b : Signal dom (BitVec 65)) := Signal.ule a b
def selfLt {dom : DomainConfig} (a : Signal dom (BitVec 8)) := Signal.ult a a
def selfLe {dom : DomainConfig} (a : Signal dom (BitVec 8)) := Signal.ule a a

run_cmd liftTermElabM do
  -- A legacy handler which always fails demonstrates that exact comparisons
  -- actually select the new total route, without invoking MetaM type inference.
  let legacy : TranslateFn := fun _ _ _ _ => throwError "comparison reached legacy handler"
  for n in [1, 8, 65] do
    for le in ([.ult, .ule, .slt, .sle, .eq] : List SignalCompareKind) do
      for named in [false, true] do
        for (x, y) in [(0, 0), (0, 2^n-1), (2^n-1, 0), (2^n-1, 2^n-1)] do
          let order ← IO.mkRef ([] : List String)
          let translate : TranslateFn := fun e hint top childNamed => do
            if top || childNamed then throwError "comparison child flags changed"
            CompilerM.liftMetaM (order.modify (· ++ [hint]))
            let value := if e.isConstOf `left then x else y
            let w ← CompilerM.makeWire "collision" (.bitVector n) (named := true)
            CompilerM.emitAssign w (.const (Int.ofNat value) n)
            return w
          let expr := compareE le (.const ``defaultDomain []) n (.const `left []) (.const `right [])
          let (w, final) ← ((translateBoolUncachedWith translate legacy expr "collision" false named) {}).run
            (CircuitM.init "CompareStep")
          unless (← order.get) == ["a", "b"] do throwError "comparison child order changed"
          let some p := final.module.wires.find? (·.name == w) | throwError "missing result wire"
          unless p.ty == .bit do throwError "comparison did not declare a Bool wire"
          let m := final.module.finalize
          let some result := evalAssigns (Sparkle.IR.RegDedup.declWidth m) (fun _ _ => 0) m.body (fun _ => 0) |
            throwError "comparison helper execution failed"
          let expected := encodeBool (compareValue le (BitVec.ofNat n x) (BitVec.ofNat n y))
          unless result w == expected do throwError "comparison helper value mismatch"
  for (decl, n, le) in [( ``lt1, 1, false), (``le1, 1, true), (``lt65, 65, false), (``le65, 65, true)] do
    let (m, _) ← synthesizeCombinational decl
    let ports := m.inputs.map (·.name)
    for x in [0, 1, 2^(n-1), 2^n-1] do
      for y in [0, 1, 2^(n-1), 2^n-1] do
        let expected := encodeBool (compareValue le (BitVec.ofNat n x) (BitVec.ofNat n y))
        unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut m
            [(ports[0]!, x), (ports[1]!, y)] == some expected do
          throwError "shipping comparison disagrees at width {n}: {x}, {y}"
  for (decl, expected) in [( ``selfLt, 0), (``selfLe, 1)] do
    let (m, _) ← synthesizeCombinational decl
    for x in [0, 1, 127, 255] do
      unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut m
          [(m.inputs[0]!.name, x)] == some expected do
        throwError "comparison with aliased operands disagrees"

run_cmd do
  if (← get).messages.hasErrors then throwError "comparison lowering regression failed"
  for name in [``compare_rhs_correct, ``emitCompareResult_returns, ``emitCompareResult_correct,
      ``translateSignalCompare_returns, ``translateSignalCompare_correct,
      ``translateBoolUncachedWith_compare, ``translateFallback_compare_correct] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected comparison axiom: {name}: {ax}"
  logInfo "SHIPPING COMPARISON LOWERING OK: actual comparison node and both cache branches proved from child contracts; no type oracle or opaque comparison-handler premise"

end Sparkle.Tests.Compiler.ShippingCompareLoweringSoundnessTest
