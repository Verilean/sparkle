import Tools.ShippingPendingSoundness
import Tools.ShippingSettledSoundness

namespace Sparkle.Tests.Compiler.ShippingSettledSoundnessTest
open Lean Elab Command
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder Sparkle.IR.OptCheck
open Tools.ShippingSettledSoundness Tools.SVParser.EmitSem
open Tools.SVParser.AST

def ordered : List Stmt := [.assign "x" (.ref "input"), .assign "out" (.ref "x")]

theorem ordered_acyclic : Acyclic ordered := by
  apply Acyclic.cons
  · simp [writesOf, stmtWrites]
  · simp [refsOf, writesOf, stmtWrites]
  · apply Acyclic.cons
    · simp [writesOf]
    · simp [refsOf, writesOf]
    · exact .nil

/-- No concrete width or input valuation is fixed in this application. -/
theorem ordered_solution (we : WEnv) (initial : Env) :
    ∃ env, IREquations we ordered env ∧ ExternalValues ordered initial env ∧
      ∀ other, IREquations we ordered other → ExternalValues ordered initial other → other = env := by
  let env : Env := fun n => if n = "out" then initial "input" else
    if n = "x" then initial "input" else initial n
  have he : evalAssigns we (fun _ _ => 0) ordered initial = some env := by
    simp [ordered, evalAssigns, evalExpr, env]
  have hq := assign_equations ordered_acyclic he
  have hx := assign_frame ordered_acyclic he
  exact ⟨env, hq, hx, fun other hq' hx' => equations_unique ordered_acyclic hq' hx' hq hx⟩

example : ¬ Acyclic [.assign "x" (.ref "x")] := by
  intro h; cases h with
  | cons _ hr _ => exact (hr "x" (by simp [refsOf])).1 rfl

example : ¬ Acyclic [.assign "x" (.const 0 8), .assign "x" (.const 1 8)] := by
  intro h; cases h with
  | cons ht _ _ => simp [writesOf, stmtWrites] at ht

/-- Both modules compute the same output, but the candidate contains an
unused forward dependency. The existing optimizer checker does not rule it out. -/
def original : Sparkle.IR.AST.Module :=
  {name := "order_probe", inputs := [], outputs := [⟨"out", .bitVector 8⟩],
    wires := [⟨"x", .bitVector 8⟩, ⟨"y", .bitVector 8⟩],
    body := [.assign "out" (.const 0 8)]}
def candidate : Sparkle.IR.AST.Module :=
  {original with body := [.assign "out" (.const 0 8),
    .assign "x" (.ref "y"), .assign "y" (.const 1 8)]}

#guard optCheck original candidate

theorem candidate_not_acyclic : ¬ Acyclic candidate.body := by
  intro h
  cases h with
  | cons _ _ htail =>
    cases htail with
    | cons _ hr _ => exact (hr "y" (by simp [refsOf])).2 (by simp [writesOf, stmtWrites])

/-- A successful sequential run alone is NOT a solution of all equations. -/
theorem candidate_not_settled :
    ∃ env, evalAssigns (fun _ => 8) (fun _ _ => 0) candidate.body (fun _ => 0) = some env ∧
      ¬ IREquations (fun _ => 8) candidate.body env := by
  let env : Env := fun n => if n = "y" then 1 else 0
  refine ⟨env, ?_, ?_⟩
  · simp [candidate, evalAssigns, evalExpr, env, mask]
  · intro h
    have he := h "x" (.ref "y") (by simp [candidate])
    simp [evalExpr, env] at he

-- Equation satisfaction is order independent, unlike one pass of evaluation.
example {wof env} {a b : CombStep} :
    SVEquations wof [a, b] env ↔ SVEquations wof [b, a] env :=
  svEquations_perm (List.Perm.swap _ _ [])


open Tools.ShippingTranslationOrder Tools.ShippingTranslateSoundness
open Sparkle.IR.Builder Sparkle.Compiler.Elab

private def literalExpr : Lean.Expr :=
  Tools.ShippingEntrySoundness.quoteF (.const ``Sparkle.Core.Domain.defaultDomain [])
    8 (fun _ => .bvar 0) (.lit 7)

theorem literal_entry_acyclic {ctx : CompilerState} {t : CircuitState} {name : String}
    (h : Returns (translateExprToWire literalExpr "result" false false)
      ctx (CircuitM.init "literal") name t) : Acyclic t.module.finalize.body := by
  have hd : Denotes (fun _ => none) literalExpr 8 (7#8) :=
    Denotes.pureLit rfl rfl rfl
  have hl : Leaf literalExpr := Or.inr ⟨[.zero], rfl⟩
  have hb : BoundLookup ctx (fun _ => none) (CircuitM.init "literal") := by
    intro id n x hx; cases hx
  exact (translateExprToWire_leaf_order hd hl hb h (OrderInv.empty rfl)).1

-- Reservation must not be mistaken for a value already assigned by the body.
private def reservedOnly : CircuitState :=
  {CircuitM.init "pending" with usedNames := ({} : Std.HashSet String).insert "result"}
example : OrderInv reservedOnly := OrderInv.empty rfl
example : Pending reservedOnly "result" := by simp [Pending, reservedOnly, CircuitM.init, footprint, Module.empty]
example : reservedOnly.usedNames.contains "result" = true := by simp [reservedOnly]
example : ¬ Acyclic ((CircuitM.emitAssign "result" (.ref "result") reservedOnly).2.module.finalize.body) := by
  intro h
  cases h with
  | cons _ hr _ => exact (hr "result" (by simp [refsOf])).1 rfl

open Tools.ShippingPendingSoundness

private def nestedExpr : Lean.Expr :=
  Tools.ShippingEntrySoundness.quoteF (.const ``Sparkle.Core.Domain.defaultDomain [])
    8 (fun _ => .bvar 0) (.bin .add (.lit 3) (.bin .mul (.lit 2) (.lit 4)))

private theorem nested_denotes : Denotes (fun _ => none) nestedExpr 8 (11#8) := by
  apply Denotes.binary (bop := .add) (x := 3#8) (y := 8#8) rfl rfl rfl rfl
  · exact Denotes.pureLit rfl rfl rfl
  · apply Denotes.binary (bop := .mul) (x := 2#8) (y := 4#8) rfl rfl rfl rfl
    · exact Denotes.pureLit rfl rfl rfl
    · exact Denotes.pureLit rfl rfl rfl

theorem nested_entry_acyclic {ctx : CompilerState} {t : CircuitState} {name : String}
    {we : WEnv}
    (h : Returns (translateExprToWire nestedExpr "result" false false)
      ctx (CircuitM.init "nested") name t) (hw : WidthsAgree we t) :
    Acyclic t.module.finalize.body := by
  have hi : Inv ctx (fun _ => none) we (fun _ _ => 0) (fun _ => 0)
      (CircuitM.init "nested") (fun _ => 0) := by
    constructor
    · rfl
    · intro id n x hx; cases hx
    · intro id n x w hx; cases hx
    · intro w e he
      simp [CircuitM.init] at he
    · intro l r hm; cases hm
  exact (translateExprToWire_orders _ _ _ _ _ _ _ _ _ nested_denotes h hi hw
    (OrderInv.empty rfl)).1

-- A body-empty, reserved name may still be an observable cache result.
-- Pending + reserved alone is insufficient; Protected must exclude this case.
private def cachedParent : CircuitState :=
  {reservedOnly with translateRecord := ({} : Std.HashMap String Lean.Expr).insert "result" literalExpr}
example (ctx : CompilerState) : ¬ Protected ctx (fun _ => none) cachedParent "result" := by
  intro hp
  exact hp.unrecorded literalExpr 8 (7#8)
    (by simp [cachedParent]) (Denotes.pureLit rfl rfl rfl)

run_cmd do
  if (← get).messages.hasErrors then throwError "settled semantics regression failed"
  for name in [``assign_frame, ``assign_equations, ``equations_eval, ``equations_unique,
      ``equations_perm, ``equations_emitted_iff, ``emitted_targets, ``svEquations_perm,
      ``module_settled, ``compiledFragment_settled, ``ordered_solution,
      ``candidate_not_acyclic, ``candidate_not_settled,
      ``acyclic_snoc, ``makeWire_order, ``emitAssign_order, ``translateSignalPureLiteral_order,
      ``core_leaf_order, ``step_leaf_order, ``translateFuelFix_leaf_order,
      ``translateExprToWire_leaf_order, ``translateExprToWire_leaf_settled, ``literal_entry_acyclic,
      ``Protected.transfer, ``Protected.makeWire, ``literal_protects, ``binary_protects,
      ``core_protects, ``step_protects, ``fuel_protects, ``translateExprToWire_protects,
      ``binary_orders, ``core_orders, ``step_orders, ``fuel_orders,
      ``translateExprToWire_orders, ``translateExprToWire_settled, ``nested_entry_acyclic] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected settled-semantics axiom: {name}: {ax}"
  logInfo "SHIPPING TRANSLATOR ORDER OK: arbitrary nested canonical operators, inputs and literals preserve order at the real entry; recursion and pending-parent/cache protection proved; core entry and output ordering connected; merging/optimizer ordering remain open"
  logInfo "SHIPPING SETTLED OK: ordered emitted assignments have a unique bounded simultaneous solution; shipping acyclicity remains an explicit obligation; standard axioms only"
end Sparkle.Tests.Compiler.ShippingSettledSoundnessTest
