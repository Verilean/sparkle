import Lean
set_option autoImplicit false
/-! # `ConstValueE` — exploratory skeleton + functionality (D.D-4, option B; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md)

DCF-1: the rule list (a well-formed, strictly positive, universe-correct mutual inductive family over an ARBITRARY `PrimTable`).
DCF-2/3: functionality of `TDen`/`ArgsDen`/`CVE` (one joint induction, since `ArgsDen.tm` contains a `CVE`), for every `PT` and `env`,
with no hypothesis beyond the two derivations (exclusivity is in the rule premises). No `sorry`, no axiom, no TRUSTED.
NOT a ledger row and NOT a final carrier: soundness (the syntactic type `τ` agrees with `ConstantInfo.type`) is unproved. -/
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

/-- Row of a term constant that is not a `defnInfo` (constructor, recursor, quot, opaque, axiom). Polymorphic constants take
type arguments, so a row is a function of the argument list of the FULL spine (a `Dyn` would be `Type 1`): `kinds` as in `TyRow`. -/
structure TmRow where
  kinds : List Bool
  den : List Arg → Option Dyn

/-- The primitive table (one row per `Name`, by construction of `Option`). Plain `def`s; no axiom. -/
structure PrimTable where
  tys : Name → Option TyRow
  tms : Name → Option TmRow

/-- The kernel's `instantiateForall` on an explicit argument list (the syntactic result type of a spine). -/
def instForall : Expr → List Expr → Expr
  | .forallE _ _ b _, a :: as => instForall (b.instantiate1 a) as
  | e, _ => e

/-- The kind test of the exclusivity condition: unfold applies exactly to `defnInfo`, prim exactly to the rest. -/
def IsDefn (env : Environment) (c : Name) : Prop := ∃ d : DefinitionVal, env.find? c = some (.defnInfo d)

/-! ### Spine lemmas (DCF-2 helper): `mkAppN (.const c ls) args` determines `c`, `ls`, `args` -/

theorem foldl_app_fn (as : List Expr) : ∀ f : Expr, (as.foldl Expr.app f).getAppFn = f.getAppFn := by
  induction as with
  | nil => intro f; rfl
  | cons a as ih => intro f; simp [List.foldl, ih, Expr.getAppFn]

theorem mkAppN_toList (f : Expr) (as : List Expr) : mkAppN f as.toArray = as.foldl Expr.app f := by
  simp only [mkAppN, ← Array.foldl_toList]
  rfl

theorem spine_fn (c : Name) (ls : List Level) (as : List Expr) : (mkAppN (.const c ls) as.toArray).getAppFn = .const c ls := by
  rw [mkAppN_toList, foldl_app_fn]; rfl

theorem foldl_app_inj : ∀ (n : Nat) (as bs : List Expr) (f g : Expr), as.length = n → f.isApp = false → g.isApp = false →
    as.foldl Expr.app f = bs.foldl Expr.app g → f = g ∧ as = bs := by
  intro n
  induction n with
  | zero =>
    intro as bs f g hn hf hg h
    have has : as = [] := List.length_eq_zero_iff.mp hn
    subst has
    rcases List.eq_nil_or_concat bs with hb | ⟨bs, b, hb⟩
    · subst hb; exact ⟨h, rfl⟩
    · subst hb
      simp [List.foldl_append] at h
      subst h; simp [Expr.isApp] at hf
  | succ n ih =>
    intro as bs f g hn hf hg h
    rcases List.eq_nil_or_concat as with ha | ⟨as, a, ha⟩
    · subst ha; simp at hn
    · subst ha
      rcases List.eq_nil_or_concat bs with hb | ⟨bs, b, hb⟩
      · subst hb
        simp [List.foldl_append] at h
        subst h; simp [Expr.isApp] at hg
      · subst hb
        simp [List.foldl_append] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨h3, h4⟩ := ih as bs f g (by simpa using hn) hf hg h1
        exact ⟨h3, by rw [h4, h2]⟩

theorem spine_inj {c c' : Name} {ls ls' : List Level} {as as' : List Expr}
    (h : mkAppN (.const c ls) as.toArray = mkAppN (.const c' ls') as'.toArray) : c = c' ∧ ls = ls' ∧ as = as' := by
  rw [mkAppN_toList, mkAppN_toList] at h
  obtain ⟨h1, h2⟩ := foldl_app_inj _ as as' _ _ rfl rfl rfl h
  injection h1 with h1 h3
  exact ⟨h1, h3, h2⟩

mutual

/-- Type denotation, syntax-directed. `TDen env ρ τ T`: the type expression `τ` denotes the Lean type `T` under the valuation `ρ`. -/
inductive TDen (PT : PrimTable) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDen PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDen PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDen PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDen PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDen PT env ρ τ T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDen PT env ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDen PT env ρ τ T

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
  | natLit {ρ : Val} {n : Nat} : CVE PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n
  | strLit {ρ : Val} {s : String} : CVE PT env ρ (.lit (.strVal s)) (.const `String []) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVE PT env ρ (.bvar i) (en.τ.liftLooseBVars 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDen PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      -- `a0`: the result type `B` is determined by the body only at some argument; an empty domain is not derived (a limitation)
      (a0 : TA) (hb : ∀ a : TA, CVE PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVE PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDen PT env ρ A TA) (hB : ∀ a : TA, TDen PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVE PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVE PT env ρ x A TA av)
      -- exclusive with `unfold`/`prim`: a const-headed spine is derived ONLY by `unfold`/`prim` on the whole spine
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVE PT env ρ (.app fe x) (B.instantiate1 x) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDen PT env ρ A TA) (hv : CVE PT env ρ v A TA av)
      (hb : CVE PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVE PT env ρ (.letE n A v b nd) (B.instantiate1 v) TB bv
  /-- unfold: the head is a `defnInfo`; the body is instantiated with the spine (syntactic beta). -/
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVE PT env ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVE PT env ρ e τ α v
  /-- prim: the head is NOT a `defnInfo` (exclusive with `unfold`), has a row, and the FULL spine is given. The syntactic type is the
  kernel's `instantiateForall` of the declared type from `env` (not from the table). `hty` is the row-typing obligation (provable per row). -/
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDen PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDen PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVE PT env ρ e (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty d.val

end

/-- The relation `CV` that `ConstValueRel` asks for (`Tools.ShippingGen5DeclConnect`): `X` at the empty valuation, some levels, some syntactic type. -/
def ConstValueE (PT : PrimTable) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ∃ (ls : List Level) (τ : Expr), CVE PT env [] (.const X ls) τ α v

end Tools.ShippingGen5ConstValueE
