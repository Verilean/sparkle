import Tools.ShippingMuxTypeSoundness
import Tests.Compiler.ShippingMuxRecursionSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingMuxTypeSoundnessTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness
open Tools.ShippingMuxLoweringSoundness

def chooseBool {dom : DomainConfig} (c a b : Signal dom Bool) := Signal.mux c a b
abbrev Octet := BitVec 8
def chooseAlias {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom Octet) :=
  Signal.mux c a b
def symbolic {dom : DomainConfig} {n : Nat} (c : Signal dom Bool)
    (a b : Signal dom (BitVec n)) := Signal.mux c a b
@[implicit_reducible] def nineInstance : OfNat Nat 8 := ⟨9⟩
def chooseCustom {dom : DomainConfig} (c : Signal dom Bool)
    (a b : Signal dom (BitVec (@OfNat.ofNat Nat 8 nineInstance))) := Signal.mux c a b

run_cmd liftTermElabM do
  -- Verify the proof's quotation against the real elaborator, without reducing
  -- away type arguments or user instances before comparing the expressions.
  for (decl, n) in [( ``Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest.choose1, 1),
      (``Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest.choose8, 8),
      (``Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest.choose65, 65)] do
    let ci ← getConstInfo decl
    let some value := ci.value? | throwError "missing mux definition"
    lambdaTelescope value fun xs body => do
      let expected := muxE xs[0]! (bitVecE n) xs[1]! xs[2]! xs[3]!
      unless @decide (body = expected) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
        throwError "{decl}: source differs from proved mux quotation"
      unless canonicalMuxType? body == some (.bitVector n) do
        throwError "canonical mux width not selected"
      let (ty, _) ← ((muxResultType body) {}).run (CircuitM.init "MuxType")
      unless ty == .bitVector n do throwError "mux type action width mismatch"
  -- Reject nonstandard numeral instances, non-Nat numerals, inconsistent
  -- standard-instance indices, symbolic widths, partial and overapplications.
  let raw := fun n => Lean.Expr.lit (.natVal n)
  let numeral := fun ty inst => mkApp3 (.const ``OfNat.ofNat [.zero]) ty (raw 8) inst
  let bad := numeral (.const ``Nat []) (.const ``nineInstance [])
  for e in [bad, numeral (.const ``Bool []) (mkApp (.const ``instOfNatNat []) (raw 8)),
      numeral (.const ``Nat []) (mkApp (.const ``instOfNatNat []) (raw 9)), .bvar 0] do
    unless (canonicalNatLitValue? e).isNone do throwError "accepted noncanonical Nat literal"
    let source := muxE (.bvar 0) (mkApp (.const ``BitVec []) e) (.bvar 1) (.bvar 2) (.bvar 3)
    unless (canonicalMuxType? source).isNone do throwError "accepted noncanonical mux width"
  let muxExpr := muxE (.bvar 0) (bitVecE 8) (.bvar 1) (.bvar 2) (.bvar 3)
  for e in [muxExpr.appFn!, mkApp muxExpr (.bvar 4),
      mkApp5 (.const `User.mux []) (.bvar 0) (bitVecE 8) (.bvar 1) (.bvar 2) (.bvar 3)] do
    unless (canonicalMuxType? e).isNone do throwError "accepted non-library/unsaturated mux"
  for (decl, n) in [( ``chooseBool, 1), (``chooseAlias, 8), (``chooseCustom, 9)] do
    let ci ← getConstInfo decl
    let some value := ci.value? | throwError "missing fallback test definition"
    lambdaTelescope value fun _ body => do
      if decl == ``chooseCustom then
        unless (canonicalMuxType? body).isNone do
          throwError "custom instance was mistaken for the standard literal"
      let (ty, _) ← ((muxResultType body) {}).run (CircuitM.init "MuxTypeFallback")
      unless ty.bitWidth == n do throwError "mux inferred the wrong width: {ty.bitWidth}"
    let (m, _) ← synthesizeCombinational decl
    let ports := m.inputs.map (·.name)
    unless ports.length == 3 && m.outputs.all (·.ty.bitWidth == n) do
      throwError "mux synthesis type regression"
    for c in [false, true] do
      for a in [0, 1, 2 ^ n - 1] do
        for b in [0, 1, 2 ^ n - 1] do
          unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut m
              [(ports[0]!, encodeBool c), (ports[1]!, a), (ports[2]!, b)] ==
              some (if c then a else b) do
            throwError "mux synthesis semantics regression"
  let ci ← getConstInfo ``symbolic
  let some value := ci.value? | throwError "missing symbolic mux"
  lambdaTelescope value fun _ body => do
    unless (canonicalMuxType? body).isNone do throwError "symbolic width treated as literal"

run_cmd do
  if (← get).messages.hasErrors then throwError "mux type regression failed"
  for name in [``library_nat_literal, ``canonicalNatLitValue?_natE,
      ``canonicalMuxType?_bitVec, ``canonicalMuxType?_bool, ``muxResultType_returns,
      ``translateQuotedMux_correct] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mux type axiom: {name}: {ax}"
  logInfo "SHIPPING MUX TYPE OK: exact source quotation; no result-type oracle for literal-width library mux; custom numeral instance preserves width 9"

end Sparkle.Tests.Compiler.ShippingMuxTypeSoundnessTest
