import Tools.ShippingExecutionSoundness
import Tests.Compiler.ShippingEntrySoundnessTest

namespace Sparkle.Tests.Compiler.ShippingExecutionSoundnessTest
open Lean Elab Command
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingSettledSoundness Tools.ShippingDeltaSemantics
open Tools.ShippingExecutionSoundness

private def chain : List Stmt :=
  [.assign "_a" (.ref "_in"), .assign "out" (.ref "_a")]
private def pairs : List CombStep :=
  [.assign "_a" (.ident "_in"), .assign "out" (.ident "_a")]
private def widths : String → Option Nat := fun _ => some 8
private def seed : Env := fun x => if x = "_in" then 7 else if x = "_a" then 1 else 0

private theorem chain_order : Acyclic chain := by
  apply Acyclic.cons
  · simp [writesOf, stmtWrites]
  · simp [refsOf, writesOf, stmtWrites]
  · apply Acyclic.cons
    · simp [writesOf]
    · simp [refsOf, writesOf]
    · exact .nil

private theorem chain_check : assignsCheck widths (fun _ => 8) chain = true := by
  simp [assignsCheck, widths, chain, sf4Check, widthOf, Sparkle.Backend.Verilog.sanitizeName,
    String.all_bool_eq]
private theorem chain_emit : emitAssigns widths chain = some pairs := by
  simp [emitAssigns, emitAstExpr, chain, pairs, Sparkle.Backend.Verilog.sanitizeName,
    String.all_bool_eq]
private theorem widths_agree : ∀ x w, widths x = some w → (8 : Nat) = w := by
  intro x w hw; exact Option.some.inj hw
private theorem seed_bounded : Bounded (fun _ => 8) seed := by
  intro x
  dsimp [seed]
  split <;> (try split) <;> decide

/-- One parallel round sees the OLD intermediate value, unlike the old
ordered-fold evaluator. The second round propagates the actual input. -/
example : irTrace (fun _ => 8) chain seed 1 "out" = 1 := rfl
example : irTrace (fun _ => 8) chain seed 2 "out" = 7 := rfl

private theorem first_round :
    DeltaStep widths pairs seed (irTrace (fun _ => 8) chain seed 1) := by
  apply (step_emitted_iff chain_order chain_check chain_emit seed_bounded ?_).mpr
    (irRound_spec chain_order chain_check seed_bounded).1
  intro x w hw
  have he := widths_agree x w hw
  simpa [← he] using seed_bounded x

/-- Stopping before the proven bound really can observe an unsettled state. -/
theorem first_round_not_stable :
    ¬ SVEquations widths pairs (irTrace (fun _ => 8) chain seed 1) := by
  intro hs
  have hb := (irRound_spec chain_order chain_check seed_bounded).2
  have hir := (step_emitted_iff chain_order chain_check chain_emit hb (by
    intro x w hw; simpa [← widths_agree x w hw] using hb x)).mp (delta_fixed_iff.mpr hs)
  have he := hir.1 "out" (.ref "_a") (by simp [chain])
  simp [evalExpr, irRound, chain, seed] at he

/-- No fixed initialization is baked into the existence theorem. -/
theorem arbitrary_seed_trace (initial : Env) (hb : Bounded (fun _ => 8) initial) :
    ∃ trace, DeltaTrace widths pairs initial trace :=
  deltaTrace_exists chain_order chain_check chain_emit widths_agree hb

-- Swapping textual order leaves the operational relation unchanged.
example (old next : Env) :
    DeltaStep widths pairs old next ↔ DeltaStep widths pairs.reverse old next := by
  exact delta_perm (List.Perm.swap _ _ [])

-- An empty design is already stable; undriven values cannot change.
example (wof : String → Option Nat) (old next : Env) :
    DeltaStep wof [] old next ↔ next = old := by
  constructor
  · intro h; exact funext (fun x => h.2 x (by simp [svTargets]))
  · intro he; subst next; exact ⟨by simp, fun _ _ => rfl⟩

open Sparkle.Tests.Compiler.ShippingEntrySoundnessTest
open Tools.ShippingEntrySoundness Tools.ShippingTranslateSoundness
open Sparkle.Compiler.Elab Sparkle.IR.OptCheck

/-- The real source entry supplies syntax and finite operational convergence
at every source observation time; no circuit-specific execution certificate. -/
theorem fragA_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue) :
    ∃ sv port pairs,
      emitAstModule (checkedOptimize m) = some sv ∧
      Tools.SVParser.ConcreteSyntax.Module sv (verilogOf m) ∧
      Tools.ShippingSVBridge.combItems sv.items = some pairs ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (a b : Sparkle.Core.Signal.Signal dom (BitVec 8)) (t : Nat),
        let initial := Tools.ShippingSVBridge.inputEnv 2 port (fun j => (sigsOf [a, b] j).val t)
        Bounded (fun x => (Tools.ShippingDeclWidths.astWidths sv x).getD 0) initial ∧
        SettlesTo sv pairs initial ((fragA a b).val t).toNat := by
  rw [fragAValue_eq] at henv
  obtain ⟨sv, port, pairs, he, hsyntax, hi, _, _, _, _, _, hs⟩ :=
    compiledFragment_execution h henv feA_wf (by decide)
  exact ⟨sv, port, pairs, he, hsyntax, hi, fun a b t => hs (sigsOf [a, b]) t⟩

run_cmd do
  if (← get).messages.hasErrors then throwError "delta execution regression failed"
  for name in [``first_round, ``first_round_not_stable, ``arbitrary_seed_trace,
      ``fragA_execution, ``compiledFragment_execution, ``irRound_spec,
      ``step_emitted_iff, ``ir_converges, ``deltaTrace_exists, ``deltaTrace_bounded,
      ``deltaTrace_converges, ``delta_fixed_iff, ``delta_perm, ``solution_bounded] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected delta-execution axiom: {name}: {ax}"
  logInfo "SHIPPING EXECUTION OK: real source to emitted syntax and finite delta settling; arbitrary bounded internal initialization; all traces, standard axioms only"

end Sparkle.Tests.Compiler.ShippingExecutionSoundnessTest
