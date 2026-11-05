import Tools.ShippingGen5ConstValueESound
set_option autoImplicit false
-- D.D-4 B, DCF-4: structural check of the soundness-side results (proved helpers) and of the obligations (types only, never assumed).

namespace Tests.Gen5.DCF4Check
open Lean Tools.ShippingGen5ConstValueE

/-! ## Structural match of the proved lemmas -/
example : ∀ e : Expr, instForall e [] = e := fun e => instForall_nil e
example : ∀ (n : Name) (A B : Expr) (bi : BinderInfo) (a : Expr) (as : List Expr),
    instForall (.forallE n A B bi) (a :: as) = instForall (B.instantiate1 a) as := instForall_cons_forallE
example : ∀ (e : Expr), e.isForall = false → ∀ as : List Expr, instForall e as = e := instForall_of_not_forallE
example : ∀ (e : Expr) (as bs : List Expr), instForall e (as ++ bs) = instForall (instForall e as) bs := instForall_append

/-! ## Negative controls -/
/-- Non-vacuous: a non-forall head is stuck whatever the arguments. -/
example (a b : Expr) : instForall (.const `c []) [a, b] = .const `c [] := rfl
/-- The hypothesis of `instForall_of_not_forallE` is needed: a Pi head does satisfy `isForall = true`. -/
example (e : Expr) : (Expr.forallE `x e e .default).isForall = true := rfl

/-! ## The obligations are plain `Prop`s (types), not theorems and not assumed anywhere in the results above. -/
example : Prop := OblLiftClosed
example (Ty : Environment → List Expr → Expr → Expr → Prop) : Prop := OblBvar Ty ∧ OblApp Ty ∧ OblLam Ty ∧ OblConst Ty
example (PT : PrimTable) (env : Environment) : Prop := OblRowTyped PT env
example (erase : Expr → Expr) : Prop := OblLevelErase erase

end Tests.Gen5.DCF4Check

#print axioms Tools.ShippingGen5ConstValueE.instForall_nil
#print axioms Tools.ShippingGen5ConstValueE.instForall_cons_forallE
#print axioms Tools.ShippingGen5ConstValueE.instForall_of_not_forallE
#print axioms Tools.ShippingGen5ConstValueE.instForall_append
#print axioms Tools.ShippingGen5ConstValueE.instForall_length_zero
-- the two opaque kernel functions the obligations are about (they have no unfolding in the logic):
#print Lean.Expr.instantiate1
#print Lean.Expr.liftLooseBVars
