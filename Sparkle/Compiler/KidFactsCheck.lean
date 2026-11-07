import Lean
import Sparkle.Compiler.EnvTableCheck

/-! # A decidable check of the finite environment facts about a callee

`kidRowOkB env inl ip peel X T V Vi` asks, of the environment `env` and the three functions the compiler itself uses (`inl` = `userInliner env`,
`ip` = `instancePredicate env`, `peel` = the gate-peeled body), the finitely many queries `KidGateFacts` states for the callee `X` of closed type `T` and value `V`
(and inlined value `Vi`): `X` is the closed definition `T`/`V`; the inliner sends `V` to `Vi` and fixes `T`; the instance predicate is false at the peeled body of `V` and of `Vi`.
`Expr` equality is `ExprDecEq.exprDecEq` (structural, binder names included; core's `==`/`Expr.eqv` ignore binder names). The functions are PARAMETERS: this file does not
import the compiler, the guard in `Elab.lean` instantiates them with the real ones. Nothing here is trusted: no `sorry`, `axiom`, `native_decide`. -/
namespace Sparkle.Compiler.KidFactsCheck
open Lean Sparkle.Compiler.EnvTableCheck

def kidRowOkB (env : Environment) (inl : Expr → Expr) (ip : Expr → Bool) (peel : Expr → Expr) (X : Name) (T V Vi : Expr) : Bool :=
  (match env.find? X with
   | some (.defnInfo d) => decide (d.levelParams = []) && exprEqB d.type T && exprEqB d.value V
   | _ => false)
  && exprEqB (inl V) Vi && exprEqB (inl T) T && !(ip (peel V)) && !(ip (peel Vi))

theorem kidRowOkB_sound {env : Environment} {inl : Expr → Expr} {ip : Expr → Bool} {peel : Expr → Expr} {X : Name} {T V Vi : Expr}
    (h : kidRowOkB env inl ip peel X T V Vi = true) :
    (∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V) ∧
    inl V = Vi ∧ inl T = T ∧ ip (peel V) = false ∧ ip (peel Vi) = false := by
  unfold kidRowOkB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, exprEqB_iff.1 h2, exprEqB_iff.1 h3, h4, h5⟩
  split at h1
  · rename_i d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨d, hd, h1.1.1, exprEqB_iff.1 h1.1.2, exprEqB_iff.1 h1.2⟩
  · cases h1

end Sparkle.Compiler.KidFactsCheck
