import Tools.ShippingBoolLiteralSoundness
import Tests.Compiler.ShippingCompareLoweringSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingBoolLiteralSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingBoolLiteralSoundness Tools.ShippingMuxLoweringSoundness

def alwaysTrue : Signal defaultDomain Bool := Signal.pure true
def alwaysFalse : Signal defaultDomain Bool := Signal.pure false

run_cmd liftTermElabM do
  let dom := mkConst ``defaultDomain
  for (decl, b) in [( ``alwaysTrue, true), (``alwaysFalse, false)] do
    let ci ← getConstInfo decl
    let some value := ci.value? | throwError "missing Bool literal definition"
    unless @decide (value = literalE dom b) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "Bool literal quotation differs from elaboration"
  let bomb : TranslateFn := fun _ _ _ _ => throwError "literal called a recursive/legacy handler"
  for b in [false, true] do
    let e := literalE dom b
    let (_, direct) ← ((translateBoolUncachedWith bomb bomb e "direct" false false) {}).run
      (CircuitM.init "DirectBool")
    unless direct.module.body.length == 1 do throwError "literal direct path emitted extra logic"
    for enabled in [false, true] do
      for named in [false, true] do
        for top in [false, true] do
          let cache ← IO.mkRef ({} : ExprStructMap String)
          let ctx : CompilerState := {exprCache := if enabled then some cache else none}
          let s := (CircuitM.addInput "_collision" .bit (CircuitM.init "LiteralCache")).2
          let s := {s with module := {s.module with wires := s.module.inputs}}
          cache.modify (·.insert ⟨e⟩ "_collision")
          let (w, s1) ← ((translateExprToWire e "collision" top named) ctx).run s
          let (w2, s2) ← ((translateExprToWire e "collision" top named) ctx).run s1
          unless w != "_collision" && w2 != "_collision" do
            throwError "literal trusted unrecorded cache or overwrote a live input"
          if enabled && !named && !top then
            unless w == w2 && s1.module.body.length == s2.module.body.length do
              throwError "literal cache hit re-emitted a constant"
            let (wf, sf) ← ((translateFallback bomb e "fallback_hit" false false) ctx).run s2
            unless wf == w2 && sf.module.body.length == s2.module.body.length do
              throwError "fallback cache hit re-emitted a constant"
          else
            unless w != w2 do throwError "named/top-level/disabled-cache call reused a wire"
          let (width, _) ← ((CompilerM.getWireWidth w2) ctx).run s2
          unless width == 1 do throwError "literal result width is not one"
          let some recorded := s2.translateRecord.get? w2 | throwError "literal was not recorded"
          unless @decide (recorded = e) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
            throwError "literal record has the wrong source"
          for input in [0, 1] do
            let m := s2.module.finalize
            let some result := evalAssigns (Sparkle.IR.RegDedup.declWidth m)
                (fun _ _ => 0) m.body (fun _ => input) | throwError "literal evaluation failed"
            unless result w == encodeBool b && result w2 == encodeBool b && result "_collision" == input do
              throwError "literal result/frame mismatch"
  -- A computed Bool payload is not silently treated as a constructor literal.
  let computed := mkApp3 (.const ``Signal.pure [.zero]) dom (.const ``Bool [])
    (mkApp (.const ``Bool.not []) (.const ``Bool.false []))
  let (tag, _) ← ((translateBoolUncachedWith bomb (fun _ _ _ _ => pure "legacy")
    computed "computed" false false) {}).run (CircuitM.init "ComputedBool")
  unless tag == "legacy" do throwError "nonliteral payload bypassed its existing handler"
  let (mt, _) ← synthesizeCombinational ``alwaysTrue
  let (mf, _) ← synthesizeCombinational ``alwaysFalse
  unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut mt [] == some 1 &&
      Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut mf [] == some 0 do
    throwError "whole-entry Bool literal mismatch"
  IO.FS.writeFile "/tmp/sparkle_bool_literals.sv"
    (Sparkle.Backend.Verilog.toVerilog mt ++ Sparkle.Backend.Verilog.toVerilog mf ++
      s!"\nmodule tb; wire t,f; {Sparkle.Backend.Verilog.sanitizeName mt.name} a(.out(t)); {Sparkle.Backend.Verilog.sanitizeName mf.name} b(.out(f));\n" ++
      "initial begin #1; if(t !== 1'b1 || f !== 1'b0) $fatal(1, \"Bool literals mismatch\"); $display(\"BOOL LITERAL RTL OK\"); $finish; end endmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "Bool literal regression failed"
  for name in [``literal_core, ``literal_uncached, ``emitBoolLiteral_correct,
      ``literal_hit, ``translateFallback_literal_correct, ``translateStep_literal_correct,
      ``translateExprToWire_literal_correct] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected Bool literal axiom: {name}: {ax}"
  logInfo "SHIPPING BOOL LITERAL OK: actual translateExprToWire, both cache layers, no recursive/legacy/type-query hypothesis; initial invariants and final widths remain explicit"

end Sparkle.Tests.Compiler.ShippingBoolLiteralSoundnessTest
