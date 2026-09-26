import Tools.ShippingTypedExprSoundness
import Tools.ShippingExecutionSoundness
import Tests.Compiler.ShippingEntrySoundnessTest

namespace Sparkle.Tests.Compiler.ShippingTypedExprSoundnessTest
open Lean Elab Command Meta
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingTypedExprSoundness Tools.ShippingPrintSoundness
open Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Compiler.Elab

/-- A comparison drives a mux with arithmetic and nested shift branches;
a one-bit external condition drives another mux. -/
def choice (op : Operator) : Sparkle.IR.AST.Expr :=
  .op .mux [.op op [.ref "_a", .ref "_b"],
    .op .add [.ref "_a", .ref "_b"],
    .op .mux [.ref "_s", .op .shr [.op .shl [.ref "_a", .ref "_b"], .ref "_b"],
      .ref "_b"]]

def widths (n : Nat) : WEnv := fun x => if x = "_s" then 1 else n

theorem choice_typed {n op} (hn : 0 < n) (hop : isCompareOp op = true) :
    TypedExpr (widths n) (choice op) n := by
  have ha : TypedExpr (widths n) (.ref "_a") n := by
    simpa [widths] using TypedExpr.ref (we := widths n) "_a" (by simpa [widths] using hn)
  have hb : TypedExpr (widths n) (.ref "_b") n := by
    simpa [widths] using TypedExpr.ref (we := widths n) "_b" (by simpa [widths] using hn)
  have hs : TypedExpr (widths n) (.ref "_s") 1 := by
    simpa [widths] using TypedExpr.ref (we := widths n) "_s" (by simp [widths])
  exact .mux (.compare hop ha hb) (.bin .add ha hb rfl)
    (.mux hs (.bin .shr (.bin .shl ha hb rfl) hb rfl) hb)

theorem choice_printed {n op} (hn : 0 < n) (hop : isCompareOp op = true) :
    ∃ sv, emitAstExpr (fun x => some (widths n x)) (choice op) = some sv ∧
      Tools.SVParser.ConcreteSyntax.Expression sv
        (Sparkle.Backend.Verilog.emitExpr (fun x => some (widths n x)) (choice op)) ∧
      ∀ env, Bounded (widths n) env →
        Tools.SVParser.SVSemantics.evalSV (fun x => some (widths n x)) env n sv =
          evalExpr (widths n) env (choice op) := by
  obtain ⟨sv, he, hs, hv⟩ := typedExpr_printed (choice_typed hn hop)
    (wof := fun x => some (widths n x)) (by
      intro x hx
      simp [choice, Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals refine ⟨by simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq], rfl, ?_⟩
      all_goals exact Tools.ShippingSyntaxSoundness.dataName_identifier (Or.inl ⟨by simp [Sparkle.IR.NameHints.Clean, Sparkle.IR.NameHints.charOk], rfl⟩))
  exact ⟨sv, he, hs, fun env hb => hv env hb (by intro x w h; cases h; exact hb x)⟩

def circuit (op : Operator) : Sparkle.IR.AST.Module :=
  { name := "TypedChoice"
    inputs := [⟨"_a", .bitVector 8⟩, ⟨"_b", .bitVector 8⟩, ⟨"_s", .bitVector 1⟩]
    outputs := [⟨"out", .bitVector 8⟩]
    wires := []
    body := [.assign "out" (choice op)] }

-- An actual source declaration exercises the still-unproved synthesis path.
-- This is a regression, not an application of compiledFragment_execution.
def sourceChoice {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux (Signal.ult a b) (a + b) ((a <<< b) >>> b)

run_cmd liftTermElabM do
  for n in [1, 8, 65] do
    for op in [Operator.eq, .lt_u, .le_u, .gt_u, .ge_u] do
      let wof := fun x => some (widths n x)
      let e := choice op
      unless sf4Check wof (widths n) e do throwError "typed choice escaped forward checker"
      let some sv := emitAstExpr wof e | throwError "typed choice AST failed"
      unless renderExpr sv == some (Sparkle.Backend.Verilog.emitExpr wof e) do
        throwError "typed choice rendering differs"
      for a in [0, 1, 2 ^ (n - 1), 2 ^ n - 1] do
        for b in [0, 1, n - 1, n, n + 1, 255] do
          for s in [0, 1] do
            let x := BitVec.ofNat n a
            let y := BitVec.ofNat n b
            let condition := match op with
              | .eq => x == y | .lt_u => x.ult y | .le_u => x.ule y
              | .gt_u => y.ult x | .ge_u => y.ule x | _ => false
            let expected := if condition then x + y else if s == 1 then
                (x <<< y.toNat).ushiftRight y.toNat else y
            let env := fun name => if name == "_a" then x.toNat else
              if name == "_b" then y.toNat else if name == "_s" then s else 0
            unless evalExpr (widths n) env e == some expected.toNat &&
                Tools.SVParser.SVSemantics.evalSV wof env n sv == some expected.toNat do
              throwError "typed comparison/mux value mismatch: width {n}, {a}, {b}, {s}"
  let (m, _) ← synthesizeCombinational ``sourceChoice
  let ports := m.inputs.map (·.name)
  unless ports.length == 2 do throwError "source choice input count"
  for a in [0, 1, 127, 128, 255] do
    for b in [0, 1, 7, 8, 9, 255] do
      let x := BitVec.ofNat 8 a
      let y := BitVec.ofNat 8 b
      let expected := if x.ult y then x + y else (x <<< y.toNat).ushiftRight y.toNat
      unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut m
          [(ports[0]!, a), (ports[1]!, b)] == some expected.toNat do
        throwError "shipping source choice mismatch"
  let mut text := ""
  let mut instances := ""
  let mut checks := ""
  for (op, tok, suffix) in [(Operator.eq, "==", "eq"), (.lt_u, "<", "lt"),
      (.le_u, "<=", "le"), (.gt_u, ">", "gt"), (.ge_u, ">=", "ge")] do
    let m := { circuit op with name := "TypedChoice_" ++ suffix }
    text := text ++ Sparkle.Backend.Verilog.toVerilog m ++ "\n"
    instances := instances ++ s!"wire [7:0] o_{suffix}; {m.name} d_{suffix}(._a(a), ._b(b), ._s(s), .out(o_{suffix}));\n"
    checks := checks ++ s!"expected = (i {tok} j) ? ((i+j)&255) : (k ? (((i<<j)&255)>>j) : j); if(o_{suffix} !== expected) $fatal(1, \"{suffix} mismatch\");\n"
  text := text ++ "module tb; reg [7:0] a,b; reg s; reg [7:0] expected; integer i,j,k;\n" ++ instances ++
    "initial begin for(i=0;i<256;i=i+1) for(j=0;j<256;j=j+1) for(k=0;k<2;k=k+1) begin a=i; b=j; s=k; #1;\n" ++
    checks ++ "end $display(\"TYPED RTL OK: 5 comparisons, 131072 inputs each\"); $finish; end endmodule\n"
  IO.FS.writeFile "/tmp/sparkle_typed_choice.sv" text

run_cmd do
  if (← get).messages.hasErrors then throwError "typed backend regression failed"
  for name in [``choice_printed, ``typedExpr_printed, ``typedBody_assignsCheck,
      ``Tools.ShippingExecutionSoundness.compiledFragment_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected typed backend axiom: {name}: {ax}"
  logInfo "SHIPPING TYPED BACKEND OK: comparison/mux expression syntax and semantics; source synthesis remains a regression only; standard axioms"

end Sparkle.Tests.Compiler.ShippingTypedExprSoundnessTest
