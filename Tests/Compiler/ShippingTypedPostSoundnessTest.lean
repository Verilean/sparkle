import Tools.ShippingTypedPostSoundness
import Tests.Compiler.ShippingTypedExprSoundnessTest
import Tests.Compiler.ShippingMuxLoweringSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingTypedPostSoundnessTest
open Lean Elab Command Meta
open Sparkle.IR.Semantics Sparkle.IR.Type
open Sparkle.IR.RegDedup Sparkle.IR.ZeroWidth
open Tools.ShippingEntrySoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingTypedPostSoundness
open Sparkle.Compiler.Elab

/-- Two duplicate one-bit comparisons feed duplicate wide muxes. An unused
zero-width declaration forces the cleanup path to remove a real declaration. -/
def circuit (n : Nat) : Sparkle.IR.AST.Module :=
  { name := "MixedPost"
    inputs := [⟨"_a", .bitVector n⟩, ⟨"_b", .bitVector n⟩]
    outputs := [⟨"out", .bitVector n⟩]
    wires := [⟨"_a", .bitVector n⟩, ⟨"_b", .bitVector n⟩,
      ⟨"_c", .bit⟩, ⟨"_d", .bitVector 1⟩, ⟨"_x", .bitVector n⟩, ⟨"_y", .bitVector n⟩,
      ⟨"_unused_zero", .bitVector 0⟩]
    body := [.assign "_c" (.op .lt_u [.ref "_a", .ref "_b"]),
      .assign "_d" (.op .lt_u [.ref "_a", .ref "_b"]),
      .assign "_x" (.op .mux [.ref "_c", .ref "_a", .ref "_b"]),
      .assign "_y" (.op .mux [.ref "_d", .ref "_a", .ref "_b"]),
      .assign "out" (.ref "_y")] }

example (n : Nat) : declWidth (circuit n) "_c" = 1 := rfl
example (n : Nat) : weOf (circuit n) "_c" = 1 := rfl

set_option maxRecDepth 2048 in
theorem circuit_ready {n : Nat} (hn : 0 < n) : TypedPostReady (circuit n) := by
  have ha : TypedExpr (weOf (circuit n)) (.ref "_a") n := .ref _ hn
  have hb : TypedExpr (weOf (circuit n)) (.ref "_b") n := .ref _ hn
  have hc : TypedExpr (weOf (circuit n)) (.ref "_c") 1 := .ref _ (by change 0 < 1; decide)
  have hd : TypedExpr (weOf (circuit n)) (.ref "_d") 1 := .ref _ (by change 0 < 1; decide)
  have hy : TypedExpr (weOf (circuit n)) (.ref "_y") n := .ref _ hn
  refine ⟨by simp [circuit], rfl, ?_, ?_⟩
  · simp only [Sparkle.IR.Optimize.buildWidthMap, circuit, List.foldl,
      Std.HashMap.get?_insert, HWType.bitWidth]
    simp [Nat.ne_of_gt hn]
  · intro st hst
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl
    · exact ⟨"_c", _, 1, rfl, .compare rfl ha hb, Or.inl rfl⟩
    · exact ⟨"_d", _, 1, rfl, .compare rfl ha hb, Or.inl rfl⟩
    · exact ⟨"_x", _, n, rfl, .mux hc ha hb, Or.inl rfl⟩
    · exact ⟨"_y", _, n, rfl, .mux hd ha hb, Or.inl rfl⟩
    · exact ⟨"out", _, n, rfl, hy, Or.inr rfl⟩

/-- Instantiation of the general post-processing theorem at every positive
width, for every initial environment and successful original evaluation. -/
theorem circuit_post {n : Nat} (hn : 0 < n) (mems : MEnv) (initial result : Env)
    (he : evalAssigns (weOf (circuit n)) mems (circuit n).body initial = some result) :
    let m := mergeDuplicates (dropZeroWidthModule (circuit n))
    evalAssigns (weOf m) mems m.body initial = some result ∧
    TypedStmts (weOf m) m.body ∧ m.inputs = (circuit n).inputs ∧ m.outputs = (circuit n).outputs :=
  typed_postprocess_sound (circuit_ready hn) (Or.inr rfl) mems initial result he

run_cmd liftTermElabM do
  for n in [1, 8, 65] do
    let original := circuit n
    let clean := dropZeroWidthModule original
    let merged := mergeDuplicates clean
    unless clean.wires.length + 1 == original.wires.length do
      throwError "zero-width cleanup was not exercised"
    unless merged.body != clean.body && validateMerge (declWidth clean) clean.body merged.body do
      throwError "typed merge was not accepted or did not change the body"
    for a in [0, 1, 2 ^ (n-1), 2 ^ n - 1] do
      for b in [0, 1, 2 ^ (n-1), 2 ^ n - 1] do
        let env := fun x => if x == "_a" then a else if x == "_b" then b else 0
        let some before := evalAssigns (weOf original) (fun _ _ => 0) original.body env |
          throwError "original typed fixture did not evaluate"
        for m in [clean, merged] do
          let some after := evalAssigns (weOf m) (fun _ _ => 0) m.body env |
            throwError "postprocessed fixture did not evaluate"
          for x in ["_a", "_b", "_c", "_d", "_x", "_y", "out"] do
            unless before x == after x do throwError "postprocessing changed {x}"
        unless before "out" == min a b do throwError "wrong mux result"
    if n == 8 then
      IO.FS.writeFile "/tmp/sparkle_typed_post.sv" (Sparkle.Backend.Verilog.toVerilog merged ++
        "\nmodule tb; reg [7:0] a,b; wire [7:0] out; integer i,j; MixedPost dut(._a(a), ._b(b), .out(out));\n" ++
        "initial begin for(i=0;i<256;i=i+1) for(j=0;j<256;j=j+1) begin a=i; b=j; #1; if(out !== (a < b ? a : b)) $fatal(1, \"post mismatch\");\n" ++
        "end $display(\"TYPED POST RTL OK: 65536 inputs\"); $finish; end endmodule\n")
  -- Actual source declarations contain scalar `bit` declarations. Ensure the
  -- revised width environment and printing checker agree for those names.
  for decl in [``Sparkle.Tests.Compiler.ShippingTypedExprSoundnessTest.sourceChoice,
      ``Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest.choose8] do
    let (m, _) ← synthesizeCombinational decl
    let mut sawBit := false
    for p in m.wires do
      if p.ty == .bit then
        sawBit := true
        unless declWidth m p.name == 1 && weOf m p.name == 1 &&
            Sparkle.IR.PrintCheck.widths m p.name == some 1 do
          throwError "shipping Bool width disagreement"
    unless sawBit do throwError "expected actual Bool wire missing"
    unless Tools.ShippingSVBridge.forwardCheck m do
      throwError "actual mixed-width source module failed the RTL forward check"

run_cmd do
  if (← get).messages.hasErrors then throwError "typed post-processing regression failed"
  for name in [``circuit_post, ``typed_postprocess_sound, ``validateMerge_typed,
      ``Tools.ShippingExecutionSoundness.compiledFragment_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected typed post-processing axiom: {name}: {ax}"
  logInfo "SHIPPING TYPED POST OK: mixed bit/BitVec cleanup and checked merge preserve values and widths; standard axioms"

end Sparkle.Tests.Compiler.ShippingTypedPostSoundnessTest
