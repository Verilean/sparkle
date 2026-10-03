import Sparkle.IR.Builder
import Tools.ConeFoldMem

/-! A general simulation step for the ACTUAL builder used by the shipping
compiler. The input state stores statements in reverse emission order;
Module.finalize restores execution order. This is a local combinational
preservation theorem, not a proof of fresh-name allocation or scalar lowering. -/

namespace Tools.ShippingBuilderSoundness

open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics

theorem emitAssign_body (s : CircuitState) (lhs : String) (rhs : Expr) :
    (CircuitM.emitAssign lhs rhs s).2.module.finalize.body =
      s.module.finalize.body ++ [.assign lhs rhs] := by
  change (.assign lhs rhs :: s.module.body).reverse = s.module.body.reverse ++ _
  exact List.reverse_cons

/-- For any builder state and any values produced by its existing prefix,
emitting an assignment extends execution by exactly the RHS evaluation.
The whole environment is specified, including preservation of other wires. -/
theorem emitAssign_sound (s : CircuitState) (we : WEnv) (mems : MEnv)
    (initial prior : Env) (lhs : String) (rhs : Expr) (value : Nat)
    (hprefix : evalAssigns we mems s.module.finalize.body initial = some prior)
    (hrhs : evalExpr we prior rhs = some value) :
    evalAssigns we mems (CircuitM.emitAssign lhs rhs s).2.module.finalize.body initial =
      some (fun n => if n = lhs then value else prior n) := by
  rw [emitAssign_body, Tools.ConeFold.evalAssigns_append, hprefix]
  simp [evalAssigns, hrhs]

/-- The frame condition required when allocating a fresh output name. The
allocator must separately prove disjointness from the live source bindings. -/
theorem emitAssign_preserves_live (s : CircuitState) (we : WEnv) (mems : MEnv)
    (initial prior : Env) (lhs : String) (rhs : Expr) (value : Nat)
    (hprefix : evalAssigns we mems s.module.finalize.body initial = some prior)
    (hrhs : evalExpr we prior rhs = some value)
    (live : String → Prop) (fresh : ∀ n, live n → n ≠ lhs) :
    ∃ result,
      evalAssigns we mems (CircuitM.emitAssign lhs rhs s).2.module.finalize.body initial = some result ∧
      result lhs = value ∧ ∀ n, live n → result n = prior n := by
  refine ⟨_, emitAssign_sound s we mems initial prior lhs rhs value hprefix hrhs, ?_, ?_⟩
  · simp
  · intro n hn
    simp [fresh n hn]

end Tools.ShippingBuilderSoundness
