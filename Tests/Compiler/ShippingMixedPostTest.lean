import Tools.ShippingMixedPostSoundness
import Tests.Compiler.ShippingMixedEntryTest

namespace Sparkle.Tests.Compiler.ShippingMixedPostTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.OptCheck Sparkle.IR.RegDedup Sparkle.IR.ZeroWidth
open Tools.ShippingEntrySoundness Tools.ShippingMixedEntrySoundness Tools.ShippingMixedPostSoundness
open Tools.ShippingMixedBinarySoundness Tools.ShippingMixedRecursion
open Tools.ShippingMuxLoweringSoundness

def unusedWide {dom : DomainConfig} (c : Signal dom Bool) (_unused : Signal dom (BitVec 17)) :=
  Signal.mux c (Signal.pure true) (Signal.pure false)

/-- Regression on the public theorem type: compilation success and the actual
source gate lead to preservation through cleanup and optimization. No
TypedPostReady, shape, width, optimizer-success or child-correctness premise. -/
theorem shipping_endpoint {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        MixedSourcePreserves declName bs body fun initial mems expected =>
          ∃ result, evalAssigns (weOf (checkedOptimize m)) mems (checkedOptimize m).body initial = some result ∧
            result "out" = expected ∧ "out" ∈ (checkedOptimize m).outputs.map (·.name) :=
  synthesizeCombinational_mixed_checked hr

run_cmd liftTermElabM do
  let mut accepted := 0
  let mut retained := 0
  let mut cases := 0
  for name in [``ShippingMixedRecursionTest.source, ``ShippingMixedEntryTest.passthrough,
      ``ShippingMixedEntryTest.constant, ``ShippingMixedEntryTest.oneBit, ``unusedWide] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "post test source missed gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      unless simpleBody post do throwError "mixed postprocessing escaped checked shape gate"
      let optimized := checkedOptimize post
      if optCheck post (Sparkle.IR.Optimize.optimizeModule post) &&
          assignmentOrderCheck (Sparkle.IR.Optimize.optimizeModule post).body then
        accepted := accepted + 1
      else
        retained := retained + 1
      unless raw.inputs == post.inputs && raw.outputs == post.outputs &&
          raw.inputs == optimized.inputs && raw.outputs == optimized.outputs do
        throwError "mixed postprocessing changed interface"
      for c in [false, true] do
        for a in [0, 1, 127, 128, 255] do
          for b in [0, 1, 127, 128, 255] do
            let values := if name == ``ShippingMixedRecursionTest.source then [encodeBool c, a, b]
              else if name == ``ShippingMixedEntryTest.passthrough then [encodeBool c]
              else if name == ``ShippingMixedEntryTest.oneBit then [encodeBool c, a % 2]
              else if name == ``unusedWide then [encodeBool c, 131071] else []
            let initial := fun w => (((raw.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
            let run := fun (m : Sparkle.IR.AST.Module) =>
              (evalAssigns (weOf m) (fun _ _ => 0) m.body initial).map (· "out")
            let expected := run raw
            unless expected.isSome && run post == expected && run optimized == expected do
              throwError "mixed postprocessing value mismatch: {name}"
            cases := cases + 1
  unless accepted > 0 && retained > 0 do throwError "did not exercise both checked optimizer branches"
  unless cases == 750 do throwError "unexpected case count"
  logInfo m!"MIXED POST RTL: {cases} value cases; {accepted} accepted and {retained} retained module selections"

run_cmd do
  if (← get).messages.hasErrors then throwError "mixed post regression failed"
  for name in [``Frame.refl, ``Frame.trans, ``Frame.makeWire, ``Frame.emitAssign, ``Frame.record_new,
      ``bits_fuel_contract, ``bool_fuel_contract, ``input_scalar, ``input_outputs, ``prepare_shape,
      ``input_bounds, ``prepare_inputBounds, ``weOf_eq_moduleWidths, ``emitLeaves_postReady,
      ``MixedSourcePreserves.map, ``synthesizeMixedCertified_sound, ``synthesizeFromConst_mixed_sound,
      ``synthesizeCombinationalCore_mixed_sound, ``checkedOptimize_flat_sound,
      ``typed_postprocess_widths, ``mixed_postprocess_checked, ``synthesizeCombinational_mixed_checked,
      ``shipping_endpoint] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed post axiom: {name}: {ax}"
  logInfo "SHIPPING MIXED POST: actual entry, cleanup and checked optimizer composed; readiness, shape and bounds derived; text/settling still open"

end Sparkle.Tests.Compiler.ShippingMixedPostTest
