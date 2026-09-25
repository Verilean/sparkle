import Tools.ShippingPrintSoundness

namespace Sparkle.Tests.Compiler.ShippingPrintSoundnessTest

open Lean Elab Command
open Sparkle.IR.AST Tools.SVParser.AST Tools.SVParser.EmitAst
open Tools.ShippingPrintSoundness Tools.ShippingOptSoundness

def sample : Sparkle.IR.AST.Expr :=
  .op .and [.op .xor [.op .add [.ref "a", .ref "b"], .const 3 8], .const 255 8]

theorem sample_shape : Shape sample := by
  exact .bin rfl (.bin rfl (.bin rfl (.ref _) (.ref _)) (.const (by decide) (by decide)))
    (.const (by decide) (by decide))

/-- The bridge applies to a nested expression with the optimizer's mask. -/
example (wof : String → Option Nat) :
    ∃ sv, emitAstExpr wof sample = some sv ∧
      renderExpr sv = some (Sparkle.Backend.Verilog.emitExpr wof sample) :=
  emitExpr_render sample_shape wof

#guard ((emitAstExpr (fun _ => some 8) sample).bind renderExpr) ==
  some "(((a + b) ^ 8'd3) & 8'd255)"
#guard renderExpr (.unary .bitNot (.ident "a")) == none
#guard renderItem "    " (.contAssign (.ident "out") (.ident "a")) ==
  some "    assign out = a;"

-- Sanitize stability alone is NOT lexical validity. These names must not
-- silently be certified as ordinary SV identifiers by a future module gate.
#guard Sparkle.Backend.Verilog.sanitizeName "1bad" == "1bad"
#guard Sparkle.Backend.Verilog.sanitizeName "module" == "module"

run_cmd do
  if (← get).messages.hasErrors then throwError "printer regression failed"
  for name in [``normE_input_shape, ``normBody_input_shape, ``emitExpr_render,
      ``printedExpr_semantics, ``emitStmt_render, ``emitBody_render,
      ``acceptedOptimizer_body_render] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected printer axiom: {name}: {ax}"
  logInfo "SHIPPING PRINT OK: expression and assignment text equal SV AST rendering; standard axioms only; module/lexical bridge still open"

end Sparkle.Tests.Compiler.ShippingPrintSoundnessTest
