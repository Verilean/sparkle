import Lean
set_option autoImplicit false
/-! # `ConstValueE` — SKELETON OF TYPES ONLY (D.D-4, option B; freeze draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md)

Definitions and inductive types only. No theorem, no `sorry`, no axiom. NOT part of any ledger row: it checks that the rule list of the
draft is a well-formed (strictly positive, universe-correct) inductive family, nothing more. Not adopted. -/
namespace Tools.ShippingGen5ConstValueE
open Lean

/-- A Lean value with its Lean type (`Type 0` only). -/
structure Dyn where
  ty : Type
  val : ty

/-- A valuation entry: the SYNTACTIC type (an `Expr`) of a bound variable and its denotation. -/
structure Entry where
  τ : Expr
  d : Dyn

abbrev Val := List Entry

/-- An argument of a type former: a term (a value) or a type. -/
inductive Arg
  | tm (d : Dyn)
  | ty (T : Type)

/-- Row of a type former (`Signal`, `BitVec`, `Prod`, `Bool`, `Nat`, `DomainConfig`, inductives …):
`kinds` says for each argument whether it is a term (`true`) or a type (`false`); `den` is the Lean type it denotes. -/
structure TyRow where
  kinds : List Bool
  den : List Arg → Option Type

/-- Row of a term constant that is not a `defnInfo`: a Lean constant with its Lean type (`Dyn`) and its syntactic type. -/
structure TmRow where
  τ : Expr
  d : Dyn

/-- The primitive table (one row per `Name`, by construction of `Option`). Plain `def`s; no axiom. -/
structure PrimTable where
  tys : Name → Option TyRow
  tms : Name → Option TmRow

/-- The kind test of the exclusivity condition: unfold applies exactly to `defnInfo`, prim exactly to the rest. -/
def IsDefn (env : Environment) (c : Name) : Prop := ∃ d : DefinitionVal, env.find? c = some (.defnInfo d)

mutual

/-- Type denotation, syntax-directed. `TDen env ρ τ T`: the type expression `τ` denotes the Lean type `T` under the valuation `ρ`. -/
inductive TDen (PT : PrimTable) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDen PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDen PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDen PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDen PT env ρ row.kinds args as) (hT : row.den as = some T) :
      TDen PT env ρ (mkAppN (.const c ls) args.toArray) T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDen PT env ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) T) :
      TDen PT env ρ (mkAppN (.const c ls) args.toArray) T

/-- Arguments of a type former, by the row's kinds. -/
inductive ArgsDen (PT : PrimTable) (env : Environment) : Val → List Bool → List Expr → List Arg → Prop
  | nil {ρ : Val} : ArgsDen PT env ρ [] [] []
  | ty {ρ : Val} {ks : List Bool} {e : Expr} {es : List Expr} {as : List Arg} {T : Type}
      (hT : TDen PT env ρ e T) (hs : ArgsDen PT env ρ ks es as) :
      ArgsDen PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : Val} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List Arg} {α : Type} {v : α}
      (hv : CVE PT env ρ e τ α v) (hs : ArgsDen PT env ρ ks es as) :
      ArgsDen PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

/-- Term denotation. `CVE env ρ e τ α v`: the term `e`, of syntactic type `τ`, denotes `v : α`, where `TDen … τ α`. -/
inductive CVE (PT : PrimTable) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | natLit {ρ : Val} {n : Nat} {ls : List Level} : CVE PT env ρ (.lit (.natVal n)) (.const `Nat ls) Nat n
  | strLit {ρ : Val} {s : String} {ls : List Level} : CVE PT env ρ (.lit (.strVal s)) (.const `String ls) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVE PT env ρ (.bvar i) (en.τ.liftLooseBVars 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDen PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      (hb : ∀ a : TA, CVE PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVE PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDen PT env ρ A TA) (hB : ∀ a : TA, TDen PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVE PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVE PT env ρ x A TA av)
      -- exclusive with `unfold` on a defn-headed spine (otherwise a spine has an `app` derivation and an `unfold` derivation)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls ∧ IsDefn env c) :
      CVE PT env ρ (.app fe x) (B.instantiate1 x) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDen PT env ρ A TA) (hv : CVE PT env ρ v A TA av)
      (hb : CVE PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVE PT env ρ (.letE n A v b nd) (B.instantiate1 v) TB bv
  /-- unfold: the head is a `defnInfo`; the body is instantiated with the spine (syntactic beta). -/
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVE PT env ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) τ α v) :
      CVE PT env ρ (mkAppN (.const c ls) args.toArray) τ α v
  /-- prim: the head is NOT a `defnInfo` (exclusive with `unfold`) and has a row. -/
  | prim {ρ : Val} {c : Name} {ls : List Level} {row : TmRow}
      (hrow : PT.tms c = some row) (hnd : ¬ IsDefn env c) :
      CVE PT env ρ (.const c ls) row.τ row.d.ty row.d.val

end

/-- The relation `CV` that `ConstValueRel` asks for (`Tools.ShippingGen5DeclConnect`): `X` at the empty valuation, some levels, some syntactic type. -/
def ConstValueE (PT : PrimTable) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ∃ (ls : List Level) (τ : Expr), CVE PT env [] (.const X ls) τ α v

end Tools.ShippingGen5ConstValueE
