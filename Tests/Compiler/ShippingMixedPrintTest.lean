import Tools.ShippingMixedPrintSoundness
import Tests.Compiler.ShippingMixedEntryTest
import Tests.Compiler.ShippingMixedSourceBridgeTest

namespace Sparkle.Tests.Compiler.ShippingMixedPrintTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingEntrySoundness Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.SVParser.EmitAst

/-- The public endpoint asks for no printable-declaration certificate. -/
theorem shipping_rendered {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        MixedSourcePreserves declName bs body (RenderedValue m) :=
  synthesizeCombinational_mixed_rendered hr

open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness
open Sparkle.Tests.Compiler.ShippingMixedSourceBridgeTest

theorem nested_rendered {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``ShippingMixedRecursionTest.source)
      mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``ShippingMixedRecursionTest.source sourceValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``ShippingMixedRecursionTest.source binders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      RenderedValue m initial mems (encodeBool
        ((ShippingMixedRecursionTest.source (bools 1) (bits 2 8) (bits 3 8)).val tick)) :=
  rendered_source_of_env hr env (by rfl) source_peel (by decide)
    ShippingMixedRecursionTest.term_wf bool_position bits_position

run_cmd liftTermElabM do
  let mut count := 0
  for name in [``ShippingMixedRecursionTest.source, ``ShippingMixedEntryTest.passthrough,
      ``ShippingMixedEntryTest.constant, ``ShippingMixedEntryTest.oneBit,
      ``ShippingMixedSourceBridgeTest.reordered] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "print source missed gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless printDeclsCheck m do throwError "mixed printing declarations invalid"
      let some sv := emitAstModule m | throwError "mixed SV AST emission failed"
      let countWires := (m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name).length
      unless renderModule m.name countWires sv == some (verilogOf post) do
        throwError "mixed full-module rendering mismatch: {name}"
      count := count + 1
  unless count == 15 do throwError "wrong rendering case count"
  logInfo "MIXED FULL MODULE RENDERING: 15 shipping/postprocessing paths; scalar Bool, BitVec 1, nested mux/comparison and unused mixed-width inputs"

run_cmd do
  if (← get).messages.hasErrors then throwError "mixed printing regression failed"
  for name in [``input_print, ``prepare_print, ``emitLeaves_postReady,
      ``synthesizeMixedCertified_sound, ``synthesizeFromConst_mixed_sound,
      ``printBase_concrete, ``printBase_cleanup, ``mixed_post_printDecls,
      ``mixedBinder_positive, ``mixedPeel_positive, ``mixedShape_positive,
      ``mixed_rendered, ``synthesizeCombinational_mixed_rendered, ``rendered_source_of_env, ``shipping_rendered, ``nested_rendered] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed printing axiom: {name}: {ax}"
  logInfo "MIXED PRINT ENDPOINT: actual entry to complete module rendering; grammar/binding and concurrent settling remain open"

end Sparkle.Tests.Compiler.ShippingMixedPrintTest
