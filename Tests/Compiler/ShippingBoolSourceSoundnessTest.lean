import Tools.ShippingBoolSourceSoundness
import Tests.Compiler.ShippingMuxTypeSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingBoolSourceSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness

def source {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux c (Signal.ult (a + b) b) (Signal.ule a b)

def term : BExpr := .mux (.inp 0)
  (.compare false (.bin .add (.inp 0) (.inp 1)) (.inp 1))
  (.compare true (.inp 0) (.inp 1))

theorem term_wf : term.WF 1 2 8 := by
  simp [term, BExpr.WF, Tools.ShippingEntrySoundness.FExpr.WF]
theorem source_denote {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    source c a b = denoteB 8 (fun _ => c) (fun j => if j = 0 then a else b) term := rfl

run_cmd liftTermElabM do
  let ci ← getConstInfo ``source
  let some value := ci.value? | throwError "missing Bool source"
  lambdaTelescope value fun xs body => do
    let quoted := quoteB xs[0]! 8 (fun _ => xs[1]!) (fun j => if j = 0 then xs[2]! else xs[3]!) term
    unless @decide (body = quoted) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "Bool quotation differs from actual elaboration"
    unless isBoolControl body do throwError "Bool mux bypasses validated fallback"
    let cache ← IO.mkRef ({} : ExprStructMap String)
    let ctx : CompilerState := {
      exprCache := some cache
      varMap := [(xs[1]!.fvarId!, "_c"), (xs[2]!.fvarId!, "_a"), (xs[3]!.fvarId!, "_b")] }
    let s := (CircuitM.addInput "_c" .bit (CircuitM.init "BoolCache")).2
    let s := (CircuitM.addInput "_a" (.bitVector 8) s).2
    let s := (CircuitM.addInput "_b" (.bitVector 8) s).2
    -- bindInputPort normally makes each input wire before adding the port.
    let s := {s with module := {s.module with wires := s.module.inputs}}
    let (w, s1) ← ((translateExprToWire body "bool_result") ctx).run s
    let some recorded := s1.translateRecord.get? w | throwError "Bool result was not recorded"
    unless @decide (recorded = body) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "Bool record holds a different source"
    let (w2, s2) ← ((translateExprToWire body "another_hint") ctx).run s1
    unless w == w2 && s1.module.body.length == s2.module.body.length do
      throwError "valid Bool cache hit recompiled the source"
    -- Poison the raw cache with an input wire lacking a matching record.
    -- The shipping entry must reject it and execute the real lowering path.
    cache.modify (·.insert ⟨body⟩ "_c")
    let (w3, s3) ← ((translateExprToWire body "after_poison") ctx).run s2
    unless w3 != "_c" && s3.module.body.length > s2.module.body.length do
      throwError "shipping Bool fallback trusted an unrecorded cache entry"
    -- A record for a DIFFERENT expression must not validate the poisoned hit.
    cache.modify (·.insert ⟨body⟩ "_c")
    let stale := {s3 with translateRecord := s3.translateRecord.insert "_c" (.const ``Bool.true [])}
    let (w4, s4) ← ((translateExprToWire body "after_stale") ctx).run stale
    unless w4 != "_c" do throwError "shipping Bool fallback trusted a mismatched record"
    for c in [false, true] do
      for a in [0, 1, 127, 255] do
        for b in [0, 1, 128, 255] do
          let initial := fun x => if x == "_c" then encodeBool c else if x == "_a" then a else b
          let m := s4.module.finalize
          let some result := evalAssigns (Sparkle.IR.RegDedup.declWidth m) (fun _ _ => 0) m.body initial |
            throwError "Bool cache circuit failed to evaluate"
          let expected := encodeBool ((source (Signal.pure c) (Signal.pure (BitVec.ofNat 8 a))
            (Signal.pure (BitVec.ofNat 8 b)) : Signal defaultDomain Bool).val 0)
          unless [w, w2, w3, w4].all (fun wire => result wire == expected) do
            throwError "Bool cache result differs from source for {c}, {a}, {b}: expected {expected}, got {[w, w2, w3, w4].map result}"
  let (m, _) ← synthesizeCombinational ``source
  let ports := m.inputs.map (·.name)
  let name := Sparkle.Backend.Verilog.sanitizeName m.name
  IO.FS.writeFile "/tmp/sparkle_bool_source.sv" (Sparkle.Backend.Verilog.toVerilog m ++
    s!"\nmodule tb; reg c; reg [7:0] a,b; wire out; reg [7:0] sum; integer i,j,k;\n{name} dut(.{ports[0]!}(c), .{ports[1]!}(a), .{ports[2]!}(b), .out(out));\n" ++
    "initial begin for(i=0;i<256;i=i+1) for(j=0;j<256;j=j+1) for(k=0;k<2;k=k+1) begin a=i; b=j; c=k; sum=a+b; #1; if(out !== (c ? (sum < b) : (a <= b))) $fatal(1, \"Bool source mismatch\");\n" ++
    "end $display(\"BOOL SOURCE RTL OK: 131072 inputs\"); $finish; end endmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "Bool source regression failed"
  for name in [``BoolDenotes.det, ``denoteB_val, ``denotesF_inputs, ``denotesB_quote,
      ``quotedBool_control, ``translateFallback_bool, ``BoolRecordOk.insert,
      ``BoolRecordOk.transfer, ``recordTranslation_bool, ``validatedBoolHit_correct,
      ``validatedQuotedBoolHit, ``translateControlCachedWith_returns,
      ``translateControlCachedWith_correct, ``source_denote] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected Bool source axiom: {name}: {ax}"
  logInfo "SHIPPING BOOL SOURCE OK: library source meaning, deterministic Bool records, validated shipping cache hits/misses; uncached lowering and joint entry invariant remain open"

end Sparkle.Tests.Compiler.ShippingBoolSourceSoundnessTest
