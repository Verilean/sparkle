import Tools.ShippingMixedGateSoundness
import Tests.Compiler.ShippingMixedRecursionTest

namespace Sparkle.Tests.Compiler.ShippingMixedEntryTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedGateSoundness
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingEntrySoundness

def passthrough {dom : DomainConfig} (c : Signal dom Bool) := c
def constant {dom : DomainConfig} : Signal dom Bool := Signal.pure false
def oneBit {dom : DomainConfig} (c : Signal dom Bool) (a : Signal dom (BitVec 1)) :=
  Signal.mux c (Signal.ult a (Signal.pure 1)) (Signal.pure false)
/-- BitVec-result mux remains outside both quoted entry gates. -/
def fallback {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :=
  Signal.mux (Signal.ult a b) a b

run_cmd liftTermElabM do
  for name in [``ShippingMixedRecursionTest.source, ``passthrough, ``constant, ``oneBit] do
    let ci ← getConstInfo name
    unless (certifiedShape? false [] ci).isNone do throwError "old gate unexpectedly accepts Bool result"
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "mixed gate missed {name}"
    unless (mixedCertifiedShape? true [] ci).isNone &&
        (mixedCertifiedShape? false [("WIDTH", 8)] ci).isNone do
      throwError "mixed gate incorrectly accepts symbolic/parameter mode"
  let fallbackInfo ← getConstInfo ``fallback
  unless (mixedCertifiedShape? false [] fallbackInfo).isNone do throwError "fallback gate too broad"
  -- Run each entry independently; the core clears synthesis caches on entry.
  -- Evaluation compares outputs through each run's own actual input names.
  for name in [``ShippingMixedRecursionTest.source, ``passthrough, ``constant, ``oneBit, ``fallback] do
    let (proved, _) ← synthesizeCombinationalCoreWith
      (fun e h t n => translateExprToWire e h t n) name [] false true
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (fun e h t n => translateExprToWire e h t n) name [] false false
    unless proved.inputs.map (·.ty.bitWidth) == legacy.inputs.map (·.ty.bitWidth) do
      throwError "input widths changed at mixed entry: {name}"
    for c in [false, true] do
      for a in [0, 1, 127, 128, 255] do
        for b in [0, 1, 127, 128, 255] do
          let values := if name == ``ShippingMixedRecursionTest.source then [encodeBool c, a, b]
            else if name == ``passthrough then [encodeBool c]
            else if name == ``oneBit then [encodeBool c, a % 2]
            else if name == ``fallback then [a, b] else []
          let run := fun (m : Sparkle.IR.AST.Module) =>
            let ports := m.inputs.map (·.name)
            let initial := fun w => ((ports.zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
            (evalAssigns (moduleWidths m) (fun _ _ => 0) m.body initial).map (· "out")
          let actual := run proved
          unless actual.isSome && actual == run legacy do throwError "mixed/legacy mismatch: {name}"
          let expected := if name == ``ShippingMixedRecursionTest.source then
              encodeBool (evalB 8 (fun _ => c) (fun j => BitVec.ofNat 8 (if j = 0 then a else b))
                ShippingMixedRecursionTest.term)
            else if name == ``passthrough then encodeBool c
            else if name == ``oneBit then encodeBool (c && a % 2 == 0)
            else if name == ``fallback then min a b else 0
          unless actual == some expected do throwError "mixed/source mismatch: {name}"
  -- The two scalar representations must never be conflated.
  unless mixedGateBinderKind? (sigT (.bvar 0) 1) == some (.bits 1) do
    throwError "BitVec 1 binder was not recognized distinctly"
  unless (mixedGateBinderKind? (sigT (.bvar 0) 0)).isNone do throwError "accepted zero-width mixed binder"
  let noncanonical := mkApp3 (.const ``OfNat.ofNat []) (.const ``Nat [])
    (.lit (.natVal 8)) (.const `customNatInstance [])
  let ty := mkApp2 (.const ``Signal []) (.bvar 0) (mkApp (.const ``BitVec []) noncanonical)
  unless (mixedGateBinderKind? ty).isNone do throwError "accepted noncanonical binder width"

run_cmd do
  if (← get).messages.hasErrors then throwError "mixed entry regression failed"
  for name in [``instFVars_quoteB, ``quoteB_congr, ``instantiated_quoteB, ``restrict_ports, ``extend_layout, ``prepare_layout, ``prepare_returns,
      ``bindMixed_emitLeaves_sound, ``moduleWidths_finish, ``synthesizeMixedCertified_returns,
      ``synthesizeMixedCertified_sound, ``synthesizeFromConst_mixed_sound,
      ``synthesizeCombinationalCore_mixed_sound, ``gateBody_inputs, ``mixed_compare_gate,
      ``mixedGateBool_quote, ``mixed_binder_bool, ``mixed_binder_bits, ``mixedCertifiedShape_of_quote] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed entry axiom: {name}: {ax}"
  logInfo "SHIPPING MIXED ENTRY: actual input walk, dispatcher and same-read entry proved; 250 source/legacy comparisons; postprocessing is covered by ShippingMixedPostTest; text/settling remains open"

end Sparkle.Tests.Compiler.ShippingMixedEntryTest
