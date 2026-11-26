/-
  `ved_unfold_helpers d` — unfold, in the goal, the helper circuits the declaration `d` calls.

  The names are resolved from the environment as constants (a private helper has no spelling in
  another file), so a generated script need not write them.  Used by the hierarchical checker on
  the argument terms of a call, which keep a nested circuit folded while the exported state
  theorem has it unfolded.
-/
import Tools.DeepHelpers
import Lean
open Lean Elab Tactic

namespace Tools.DeepHelpers

syntax (name := vedUnfoldHelpers) "ved_unfold_helpers " ident : tactic

@[tactic vedUnfoldHelpers] def evalVedUnfoldHelpers : Tactic := fun stx => do
  let d ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let names := helperConsts (← getEnv) d
  if names.isEmpty then return
  let ids : Array (TSyntax `ident) := names.map fun n =>
    ⟨mkCIdentFrom Syntax.missing n (canonical := true)⟩
  evalTactic (← `(tactic| try simp only [$[$ids:ident],*]))

end Tools.DeepHelpers
