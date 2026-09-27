import Tools.ShippingMixedInputSoundness

namespace Sparkle.Tests.Compiler.ShippingMixedRecursionTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedRecursion Tools.ShippingMixedOutputSoundness Tools.ShippingMixedInputSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness Tools.ShippingEntrySoundness

def source {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux (Signal.ult (a + b) b)
    (Signal.mux c (Signal.pure true) (Signal.ule (a - b) b)) (Signal.ult (a * b) a)

def term : BExpr := .mux (.compare false (.bin .add (.inp 0) (.inp 1)) (.inp 1))
  (.mux (.inp 0) (.lit true) (.compare true (.bin .sub (.inp 0) (.inp 1)) (.inp 1)))
  (.compare false (.bin .mul (.inp 0) (.inp 1)) (.inp 0))

theorem term_wf : term.WF 1 2 8 := by simp [term, BExpr.WF, FExpr.WF]
theorem source_denote {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    source c a b = denoteB 8 (fun _ => c) (fun j => if j = 0 then a else b) term := rfl

/-- Regression on the theorem's statement: no child contract, width oracle,
separation premise or initial MixedInv appears at this output boundary. -/
theorem closed_output {ctx ρ β mems initial s t dom cache logProf returned}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec 8}
    (hb : ∀ j, j < 1 → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < 2 → β (vinp j) = some ⟨8, bits j⟩)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (wires : WiresOk s) (ports : PortInputs ctx ρ β s initial)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", quoteB dom 8 (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) term)] none 0)
      ctx s returned t) :
    ∃ result, Runs (declaredWidths t) mems initial t result ∧
      result "out" = encodeBool (evalB 8 bools bits term) := by
  obtain ⟨_, result, run, value, _⟩ :=
    emitLeaves_bool_from_ports (by decide) hb hv term term_wf body record wires ports hr
  exact ⟨result, run, value⟩

run_cmd liftTermElabM do
  let ci ← getConstInfo ``source
  let some value := ci.value? | throwError "missing recursive source"
  lambdaTelescope value fun xs body => do
    let quoted := quoteB xs[0]! 8 (fun _ => xs[1]!) (fun j => if j = 0 then xs[2]! else xs[3]!) term
    unless @decide (body = quoted) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "recursive source quotation differs from elaborated source"
    for enabled in [false, true] do
      for named in [false, true] do
        for top in [false, true] do
          let cache ← IO.mkRef ({} : ExprStructMap String)
          let ctx : CompilerState := {
            exprCache := if enabled then some cache else none
            varMap := [(xs[1]!.fvarId!, "_op_a"), (xs[2]!.fvarId!, "_mux_then"), (xs[3]!.fvarId!, "_mux_cond")] }
          let s := (CircuitM.addInput "_op_a" .bit (CircuitM.init "RecursiveMixed")).2
          let s := (CircuitM.addInput "_mux_then" (.bitVector 8) s).2
          let s := (CircuitM.addInput "_mux_cond" (.bitVector 8) s).2
          let s := {s with module := {s.module with wires := s.module.inputs}}
          let (w, final) ← ((translateExprToWire quoted "mux_cond" top named) ctx).run s
          let m := final.module.finalize
          for c in [false, true] do
            for a in [0, 1, 127, 128, 255] do
              for b in [0, 1, 127, 128, 255] do
                let initial := fun x => if x == "_op_a" then encodeBool c else if x == "_mux_then" then a else b
                let some result := evalAssigns (declaredWidths final) (fun _ _ => 0) m.body initial |
                  throwError "recursive mixed execution failed"
                let expected := encodeBool (evalB 8 (fun _ => c)
                  (fun j => BitVec.ofNat 8 (if j = 0 then a else b)) term)
                unless result w == expected && result "_op_a" == encodeBool c &&
                    result "_mux_then" == a && result "_mux_cond" == b do
                  throwError "recursive mixed value/frame mismatch"
    for fuel in [0, 1] do
      let failed ← try
        let _ ← ((translateFuelFix translateStep fuel quoted "out" false false) {}).run (CircuitM.init "NoFuel")
        pure false
        catch _ => pure true
      unless failed do throwError "insufficient fuel unexpectedly succeeded"
  let (m, _) ← synthesizeCombinational ``source
  let ports := m.inputs.map (·.name)
  IO.FS.writeFile "/tmp/sparkle_mixed_recursive.sv" (Sparkle.Backend.Verilog.toVerilog m ++
    s!"\nmodule tb; reg c; reg [7:0] a,b; wire out; reg [7:0] sum,sub,prod; integer i,j,k;\n{Sparkle.Backend.Verilog.sanitizeName m.name} dut(.{ports[0]!}(c), .{ports[1]!}(a), .{ports[2]!}(b), .out(out));\n" ++
    "initial begin for(i=0;i<256;i=i+1) for(j=0;j<256;j=j+1) for(k=0;k<2;k=k+1) begin a=i; b=j; c=k; sum=a+b; sub=a-b; prod=a*b; #1; if(out !== ((sum < b) ? (c ? 1'b1 : (sub <= b)) : (prod < a))) $fatal(1, \"recursive mixed mismatch\"); end $display(\"MIXED RECURSIVE RTL OK: 131072 inputs\"); $finish; end endmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "recursive mixed regression failed"
  for name in [``Contract.child, ``bits_input_contract, ``bool_input_contract,
      ``bits_core_frame, ``bits_recorded_frame, ``bits_literal_contract, ``bits_fuel_contract,
      ``emit_bool_frame, ``cached_action, ``literal_fresh, ``bool_literal_contract,
      ``compare_shape, ``compare_fresh, ``compare_step, ``compare_contract,
      ``mux_shape, ``mux_fresh, ``mux_contract, ``bool_fuel_contract, ``translateExprToWire_bool_contract,
      ``initial_mixed, ``emitLeaves_bool_correct, ``emitLeaves_bool_from_inputs,
      ``declaredWidths_agree, ``PortInputs.lookup, ``PortInputs.separate, ``PortInputs.inputs,
      ``emitLeaves_structure, ``emitLeaves_bool_from_ports, ``emitLeaves_bool_signal,
      ``input_wires, ``input_bindings, ``input_body, ``input_record, ``input_wiresOk,
      ``visible_new, ``visible_old, ``bind_bool_layout, ``bind_bits_layout,
      ``bindInputPort_bool_correct, ``bindInputPort_bits_correct, ``empty_layout,
      ``closed_output, ``source_denote] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected recursive mixed axiom: {name}: {ax}"
  logInfo "SHIPPING MIXED RECURSION CLOSED: no child contracts; actual input binder and output emitter; final widths and separation derived; entry/postprocessing are covered by ShippingMixedPostTest; text/settling remains open"

end Sparkle.Tests.Compiler.ShippingMixedRecursionTest
