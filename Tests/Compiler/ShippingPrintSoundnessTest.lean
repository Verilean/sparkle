import Tools.ShippingModulePrintSoundness

namespace Sparkle.Tests.Compiler.ShippingPrintSoundnessTest

open Lean Elab Command
open Sparkle.IR.AST Tools.SVParser.AST Tools.SVParser.EmitAst
open Tools.ShippingPrintSoundness Tools.ShippingOptSoundness
open Tools.ShippingModulePrintSoundness

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

def identityModule (n : Nat) : Sparkle.IR.AST.Module :=
  { name := "identity.with.comment"
    inputs := [{name := "a", ty := .bitVector n}]
    outputs := [{name := "out", ty := .bitVector n}]
    wires := [{name := "a", ty := .bitVector n}]
    body := [.assign "out" (.ref "a")] }

/-- A single application covers all positive widths, including width one. -/
theorem identityModule_prints (n : Nat) (hn : 0 < n) :
    ∃ sv, emitAstModule (identityModule n) = some sv ∧
      renderModule (identityModule n).name 0 sv =
        some (Sparkle.Backend.Verilog.toVerilog (identityModule n)) := by
  have ht : ∀ p ∈ (identityModule n).inputs ++ (identityModule n).outputs ++
      (identityModule n).wires, PrintableType p.ty := by
    intro p hp
    simp only [identityModule, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact .bits n hn
  have hb : ∀ st ∈ (identityModule n).body, ∃ l r, st = .assign l r ∧ Shape r := by
    intro st hs
    simp only [identityModule, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst st
    exact ⟨_, _, rfl, .ref _⟩
  simpa [identityModule] using emitModule_render (identityModule n) rfl rfl ht hb

run_cmd do
  let internal : Sparkle.IR.AST.Module :=
    { (identityModule 8) with
      wires := [{name := "a", ty := .bitVector 8}, {name := "tmp", ty := .bitVector 8}]
      body := [.assign "tmp" sample, .assign "out" (.ref "tmp")] }
  let bitOnly : Sparkle.IR.AST.Module :=
    { name := "bits", inputs := [{name := "a", ty := .bit}], outputs := [], wires := [], body := [] }
  for m in [Sparkle.IR.AST.Module.empty "empty", identityModule 1, identityModule 8, internal, bitOnly] do
    let some sv := emitAstModule m | throwError "module AST emission failed"
    let count := (m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name).length
    unless renderModule m.name count sv == some (Sparkle.Backend.Verilog.toVerilog m) do
      throwError "module byte equality failed: {m.name}"
  let some sv := emitAstModule (identityModule 8) | throwError "identity AST failed"
  unless (renderModule (identityModule 8).name 1 sv).isNone do
    throwError "wrong declaration/body split must fail"
  -- The existing emitters disagree at width zero; the positive-width
  -- hypothesis is material, not a cosmetic restriction of the theorem.
  let some zero := emitAstModule (identityModule 0) | throwError "zero-width AST failed"
  if renderModule (identityModule 0).name 0 zero == some (Sparkle.Backend.Verilog.toVerilog (identityModule 0)) then
    throwError "expected documented zero-width type-rendering discrepancy"

run_cmd do
  if (← get).messages.hasErrors then throwError "printer regression failed"
  for name in [``normE_input_shape, ``normBody_input_shape, ``emitExpr_render,
      ``printedExpr_semantics, ``emitStmt_render, ``emitBody_render,
      ``acceptedOptimizer_body_render, ``type_render, ``port_render, ``ports_render,
      ``wires_render, ``body_lines, ``filterMap_assigns, ``emitModule_render,
      ``acceptedOptimizer_module_render, ``identityModule_prints] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected printer axiom: {name}: {ax}"
  logInfo "SHIPPING PRINT OK: full module text equals SV AST rendering on the positive-width fragment; standard axioms only; lexical and entry-to-SV bridges still open"

end Sparkle.Tests.Compiler.ShippingPrintSoundnessTest
