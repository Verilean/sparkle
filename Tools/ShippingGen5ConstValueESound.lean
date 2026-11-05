import Tools.ShippingGen5ConstValueE
set_option autoImplicit false
/-! # `ConstValueE` soundness — what is provable, and the NAMED OBLIGATIONS (DCF-4; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §DCF-4)

Proved here: the syntactic helper `instForall` is well behaved (pure structural recursion, no kernel function).
NOT proved, written as `def ... : Prop` (a type only: never assumed, no `sorry`, no axiom, no TRUSTED): the facts about
`Expr.instantiate1` / `Expr.liftLooseBVars`, which are `opaque` (extern C) in Lean, so no theorem about them exists in the logic. -/
namespace Tools.ShippingGen5ConstValueE
open Lean

theorem instForall_nil (e : Expr) : instForall e [] = e := by
  cases e <;> rfl

theorem instForall_cons_forallE (n : Name) (A B : Expr) (bi : BinderInfo) (a : Expr) (as : List Expr) :
    instForall (.forallE n A B bi) (a :: as) = instForall (B.instantiate1 a) as := rfl

theorem instForall_of_not_forallE (e : Expr) (h : e.isForall = false) (as : List Expr) : instForall e as = e := by
  cases e <;> simp [Expr.isForall] at h <;> cases as <;> simp [instForall]

/-- A stuck `instForall` stays stuck: appending arguments after the result is the identity. -/
theorem instForall_append (e : Expr) (as bs : List Expr) :
    instForall e (as ++ bs) = instForall (instForall e as) bs := by
  induction as generalizing e with
  | nil => simp [instForall_nil]
  | cons a as ih =>
    cases e with
    | forallE n A B bi => simp only [List.cons_append, instForall_cons_forallE, ih]
    | _ => simp [instForall]

theorem instForall_length_zero (e : Expr) {as : List Expr} (h : as.length = 0) : instForall e as = e := by
  have : as = [] := List.length_eq_zero_iff.mp h
  subst this; exact instForall_nil e

/-! ## Named obligations (types only). `Ty env Γ e τ` is the kernel typing judgment, a PARAMETER (core has no `Prop`-valued one). -/

/-- O-lift-closed (bvar): lifting a closed type is the identity. Opaque `liftLooseBVars`: unprovable in the logic. -/
def OblLiftClosed : Prop := ∀ (e : Expr) (s n : Nat), e.looseBVarRange = 0 → e.liftLooseBVars s n = e

/-- O-bvar (bvar rule): the kernel type of `bvar i` in context `Γ` is `Γ[i]` lifted by `i+1`. -/
def OblBvar (Ty : Environment → List Expr → Expr → Expr → Prop) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (i : Nat) (T : Expr), Γ[i]? = some T →
    Ty env Γ (.bvar i) (T.liftLooseBVars 0 (i + 1))

/-- O-app (app rule): `instantiate1` of the codomain by the argument. -/
def OblApp (Ty : Environment → List Expr → Expr → Expr → Prop) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (f x A B : Expr) (n : Name) (bi : BinderInfo),
    Ty env Γ f (.forallE n A B bi) → Ty env Γ x A → Ty env Γ (.app f x) (B.instantiate1 x)

/-- O-lam (lam rule): the body's type `B` (with `A` pushed) becomes the codomain. -/
def OblLam (Ty : Environment → List Expr → Expr → Expr → Prop) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (A b B : Expr) (n : Name) (bi : BinderInfo),
    Ty env (A :: Γ) b B → Ty env Γ (.lam n A b bi) (.forallE n A B bi)

/-- O-const (prim/unfold head): a constant has its declared type with the levels instantiated. -/
def OblConst (Ty : Environment → List Expr → Expr → Expr → Prop) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (c : Name) (ls : List Level) (ci : ConstantInfo), env.find? c = some ci →
    Ty env Γ (.const c ls) (ci.type.instantiateLevelParams ci.levelParams ls)

/-- O-row-typing (`hty`, one per table row, provable per row): the row's value has the Lean type that the `env` type denotes. -/
def OblRowTyped (PT : PrimTable) (env : Environment) : Prop :=
  ∀ (c : Name) (ls : List Level) (args : List Expr) (ci : ConstantInfo) (row : TmRow) (ρ : Val) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c = some row → ArgsDen PT env ρ row.kinds args as → row.den as = some d →
    TDen PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty

/-- O-level-erasure (`∃ ls` functionality): `instantiateLevelParams` / `instantiate1` / `beta` commute with erasing levels.
Both sides involve an `opaque` function, so this is unprovable here (see the draft). -/
def OblLevelErase (erase : Expr → Expr) : Prop :=
  (∀ (e : Expr) (ps : List Name) (ls : List Level), erase (e.instantiateLevelParams ps ls) = erase e) ∧
  (∀ (b x : Expr), erase (b.instantiate1 x) = (erase b).instantiate1 (erase x))

end Tools.ShippingGen5ConstValueE
