import Sparkle.Core.Signal

/-! The semantic rule for the shipping elaborator's applicative lowering.
An arbitrary heterogeneous application spine evaluates its actual function
body at the argument values, not a fold of the body's outer operator.
This proves the source-side rule for every spine and every cycle. Recognition
of Lean.Expr spines and preservation by scalar-to-wire lowering remain separate
obligations; this is not a theorem about all successful syntheses. -/

namespace Tools.ApplicativeLowering

open Sparkle.Core.Domain Sparkle.Core.Signal

universe u

inductive Arguments (dom : DomainConfig) : Type u → Type u → Type (u + 1) where
  | nil : Arguments dom α α
  | cons (input : Signal dom α) (rest : Arguments dom β γ) :
      Arguments dom (α → β) γ

def Arguments.signal {dom α β} : Arguments dom α β → Signal dom α → Signal dom β
  | .nil, f => f
  | .cons x rest, f => rest.signal (Signal.ap f x)

def Arguments.scalar {dom α β} : Arguments dom α β → Nat → α → β
  | .nil, _, f => f
  | .cons x rest, t, f => rest.scalar t (f (x.val t))

/-- General source-side preservation, with no arity, width, operator,
argument-order or commutativity assumption. -/
theorem Arguments.correct {dom α β} (args : Arguments dom α β)
    (f : Signal dom α) (t : Nat) :
    (args.signal f).val t = args.scalar t (f.val t) := by
  induction args with
  | nil => rfl
  | cons x rest ih => exact ih (Signal.ap f x)

theorem map_start {dom α β γ} (f : α → β) (a : Signal dom α)
    (rest : Arguments dom β γ) (t : Nat) :
    (rest.signal (Signal.map f a)).val t = rest.scalar t (f (a.val t)) :=
  rest.correct (Signal.map f a) t

end Tools.ApplicativeLowering
