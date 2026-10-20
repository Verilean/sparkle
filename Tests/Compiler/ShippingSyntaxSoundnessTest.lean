import Tools.ShippingSyntaxSoundness

namespace Sparkle.Tests.Compiler.ShippingSyntaxSoundnessTest
open Lean Elab Command
open Tools.SVParser.AST Tools.SVParser.ConcreteSyntax
open Tools.ShippingSyntaxSoundness Tools.ShippingPrintSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingNameBinding

/-- Includes negative hexadecimal constants and the emitter's zero-width
normalization, for all widths and values rather than selected examples. -/
theorem emitted_constant (v : Int) (w : Nat) (wof : String → Option Nat) :
    ∃ sv, Tools.SVParser.EmitAst.emitAstExpr wof (.const v w) = some sv ∧
      Expression sv (Sparkle.Backend.Verilog.emitExpr wof (.const v w)) := by
  obtain ⟨sv, he, hr⟩ := emitExpr_render_all (PrintShape.const v w) wof
  exact ⟨sv, he, renderExpr_syntax hr
    (emitExpr_bound (.const v w) (by simp [Sparkle.IR.Reorder.refsOf]) he)⟩

/-- Empty port/body layout and arbitrary source labels (including CR/LF)
are covered by the full-string theorem. -/
theorem empty_module (label : String) :
    Tools.SVParser.ConcreteSyntax.Module {name := "out", ports := [], items := []}
      ((renderModule label 0 {name := "out", ports := [], items := []}).getD "") := by
  apply renderModule_syntax (name := label) (count := 0) (pairs := []) (by rfl)
    (dataName_identifier (Or.inr rfl))
  · simp [Tools.ShippingDeclWidths.declarationTable]
  · rfl
  · simp [AssignmentsBound]

-- The auxiliary renderer and the independent grammar both exclude size zero.
example : renderExpr (.lit (.decimal (some 0) 7)) = none := rfl
example : renderExpr (.lit (.hex (some 0) 7)) = none := rfl
example (text : String) : ¬ Expression (.lit (.decimal (some 0) 7)) text := by
  intro h; cases h; omega
example (text : String) : ¬ Expression (.lit (.hex (some 0) 7)) text := by
  intro h; cases h; omega

-- Rendering equality alone used to accept identifiers that break tokenization.
example : renderExpr (.ident "a; assign out = 1'b1;") =
    some "a; assign out = 1'b1;" := rfl
example (text : String) : ¬ Expression (.ident "a; assign out = 1'b1;") text := by
  intro h; cases h with
  | ident hn =>
    have hclean := (Sparkle.IR.ModuleNames.legal_spec hn).2.1
    have hh := hclean ';' (by decide)
    contradiction

run_cmd do
  if (← get).messages.hasErrors then throwError "concrete syntax regression failed"
  for name in [``emitted_constant, ``empty_module, ``numeral_toDigits,
      ``dataName_identifier, ``renderExpr_syntax, ``renderPort_syntax,
      ``renderModule_syntax] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected concrete-syntax axiom: {name}: {ax}"
  logInfo "SHIPPING SYNTAX OK: complete emitted text derives the same AST; numeral values, identifiers, comments and whitespace checked; standard axioms only"

end Sparkle.Tests.Compiler.ShippingSyntaxSoundnessTest
