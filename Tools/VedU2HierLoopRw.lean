import Lean
import Sparkle.Core.Signal

/-!
# `ved_rw_loops`: rewrite the loops of a goal with state facts, up to definitional unfolding

H2e (R228).  The open parent's exported state theorems say `(Signal.loop F).val t = pack` for the loop `F` the deep
elaborator built (`loopFOf …`).  The declaration's own term (the argument of a child call, after the checker's simp)
holds the same loop with the nested circuits unfolded by `simp`, which is not the syntactic form of the theorem, and
`simp [hst]` finds no match.  The two are definitionally equal (the terms are the unfoldings of one definition), so this
tactic matches by `isDefEq` instead: every closed subterm `(Signal.loop _).val t` of the goal that is definitionally
the left side of a hypothesis `h : (Signal.loop F).val t = r` is rewritten to `r` (the proof term is `h` with the type
`e = r`; the kernel checks `e ≡ L`).  A hypothesis none of whose instances is found is skipped, not an error.
-/

open Lean Meta Elab Tactic

namespace Tools.VedU2HierLoopRw

/-- The closed subterms `Signal.val _ _ (Signal.loop _) _` of `e`, outermost first. -/
partial def loopInstances (e : Lean.Expr) : Array Lean.Expr :=
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    if e.hasLooseBVars then
      match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b | .proj _ _ b => go b acc
      | _ => acc
    else if e.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal.val && e.getAppNumArgs == 4
        && (e.getArg! 2).getAppFn.isConstOf ``Sparkle.Core.Signal.Signal.loop then
      if acc.contains e then acc else acc.push e
    else
      match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b | .proj _ _ b => go b acc
      | _ => acc
  go e #[]

end Tools.VedU2HierLoopRw

/-- `ved_rw_loops h₁ h₂ …`: see the module doc. -/
elab "ved_rw_loops " hs:(ppSpace colGt ident)+ : tactic => withMainContext do
  for h in hs do
    let hv ← elabTerm h none
    let ht ← instantiateMVars (← inferType hv)
    let some (_, lhs, rhs) := ht.eq? | throwError "ved_rw_loops: {h} is not an equation"
    let tgt ← instantiateMVars (← getMainTarget)
    for e in Tools.VedU2HierLoopRw.loopInstances tgt do
      -- the loop's pack type and the time argument must agree before the (expensive) unfolding check
      unless e.getArg! 3 == lhs.getArg! 3 do continue
      if (← withDefault <| isDefEq e lhs) then
        let tgt ← instantiateMVars (← getMainTarget)
        let pf ← mkExpectedTypeHint hv (← mkEq e rhs)
        let r ← (← getMainGoal).rewrite tgt pf
        let g ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
        replaceMainGoal (g :: r.mvarIds)
