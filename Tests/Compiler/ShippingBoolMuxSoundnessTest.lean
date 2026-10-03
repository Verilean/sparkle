import Tools.ShippingBoolMuxSoundness
import Tests.Compiler.ShippingBoolLiteralSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingBoolMuxSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingBoolMuxSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMuxLoweringSoundness

def choose {dom : DomainConfig} (c a b : Signal dom Bool) := Signal.mux c a b
def nested {dom : DomainConfig} (c a b : Signal dom Bool) :=
  Signal.mux (Signal.mux c a b) (Signal.mux a (Signal.pure false) b)
    (Signal.mux b c (Signal.pure true))

run_cmd liftTermElabM do
  let dom := mkConst ``defaultDomain
  let legacy : TranslateFn := fun _ _ _ _ => throwError "Bool mux reached legacy handler"
  for c in [false, true] do
    for a in [false, true] do
      for b in [false, true] do
        for named in [false, true] do
          let order ← IO.mkRef ([] : List String)
          let translate : TranslateFn := fun e hint top childNamed => do
            if top || childNamed then throwError "Bool mux child flags changed"
            CompilerM.liftMetaM (order.modify (· ++ [hint]))
            -- Reuse the real literal translator, including its core/fallback cache logic.
            translateExprToWire e hint top childNamed
          let e := boolMuxE dom (literalE dom c) (literalE dom a) (literalE dom b)
          let cache ← IO.mkRef ({} : ExprStructMap String)
          let ctx : CompilerState := {exprCache := some cache}
          let s := (CircuitM.addInput "_mux_cond" .bit (CircuitM.init "BoolMuxStep")).2
          let s := {s with module := {s.module with wires := s.module.inputs}}
          let (w, final) ← ((translateBoolUncachedWith translate legacy e "mux_cond" false named) ctx).run s
          unless (← order.get) == ["mux_cond", "mux_then", "mux_else"] do
            throwError "Bool mux child order changed"
          unless w != "_mux_cond" do throwError "Bool mux overwrote a reserved input"
          let some p := final.module.wires.find? (·.name == w) | throwError "Bool mux result undeclared"
          unless p.ty == .bit do throwError "Bool mux did not emit a scalar Bool wire"
          let m := final.module.finalize
          let some result := evalAssigns (Sparkle.IR.RegDedup.declWidth m) (fun _ _ => 0) m.body (fun _ => 1) |
            throwError "Bool mux evaluation failed"
          unless result w == encodeBool (if c then a else b) && result "_mux_cond" == 1 do
            throwError "Bool mux truth table/frame mismatch"
  -- Neither constant selection nor the new direct route may skip a failing branch.
  let order ← IO.mkRef ([] : List String)
  let failing : TranslateFn := fun _ hint _ _ => do
    CompilerM.liftMetaM (order.modify (· ++ [hint]))
    if hint == "mux_else" then throwError "expected else failure"
    pure "operand"
  let failed ← try
    let _ ← ((translateBoolUncachedWith failing legacy
      (boolMuxE dom (literalE dom true) (literalE dom true) (literalE dom false))
      "out" false false) {}).run (CircuitM.init "StrictBoolMux")
    pure false
    catch _ => pure true
  unless failed && (← order.get) == ["mux_cond", "mux_then", "mux_else"] do
    throwError "Bool mux failed to translate both branches"
  let mut text := ""
  for decl in [``choose, ``nested] do
    let (m, _) ← synthesizeCombinational decl
    let ports := m.inputs.map (·.name)
    for c in [false, true] do
      for a in [false, true] do
        for b in [false, true] do
          let expected := if decl == ``choose then (if c then a else b) else
            (if (if c then a else b) then (if a then false else b) else (if b then c else true))
          unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut m
              [(ports[0]!, encodeBool c), (ports[1]!, encodeBool a), (ports[2]!, encodeBool b)] ==
              some (encodeBool expected) do throwError "nested Bool mux differs from source"
    text := text ++ Sparkle.Backend.Verilog.toVerilog m
    if decl == ``nested then
      text := text ++ s!"\nmodule tb; reg c,a,b; wire out; integer i,j,k; {Sparkle.Backend.Verilog.sanitizeName m.name} dut(.{ports[0]!}(c), .{ports[1]!}(a), .{ports[2]!}(b), .out(out));\n" ++
        "initial begin for(i=0;i<2;i=i+1) for(j=0;j<2;j=j+1) for(k=0;k<2;k=k+1) begin c=i; a=j; b=k; #1; if(out !== ((c ? a : b) ? (a ? 1'b0 : b) : (b ? c : 1'b1))) $fatal(1, \"Bool mux mismatch\"); end $display(\"NESTED BOOL MUX RTL OK: 8 inputs\"); $finish; end endmodule\n"
  IO.FS.writeFile "/tmp/sparkle_bool_mux.sv" text

run_cmd do
  if (← get).messages.hasErrors then throwError "Bool mux regression failed"
  for name in [``boolMux_uncached, ``boolMux_step, ``bool_mux_rhs, ``emitBoolMux_correct,
      ``translateBoolMux_correct, ``translateFallback_boolMux_correct, ``translateExprToWire_boolMux_correct] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected Bool mux axiom: {name}: {ax}"
  logInfo "SHIPPING BOOL MUX OK: actual translator and validated cache, no legacy/type-query premise; recursive child contracts and mixed invariant remain open"

end Sparkle.Tests.Compiler.ShippingBoolMuxSoundnessTest
