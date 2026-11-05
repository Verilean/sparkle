import Tools.ShippingGen5ConstValueEV
set_option autoImplicit false
/-! # Prototype (U): `Dyn` made universe polymorphic (issue sparkle-ledger-dd4-final, Q-A (ii); draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Compare)

Types and the smallest lemmas only; NOT a carrier proposal and NOT connected to `PTcorpus`. Everything is a COPY of the `CVEKV` calculus (`Tools.ShippingGen5ConstValueEV`: rules, `conv`, functionality) with `Type` replaced by `Type u`
(`DynU.{u}`, `ArgU.{u}`, `TyRowU.{u}`, `TmRowU.{u}`, `PrimTableU.{u}`). The only rules that mention a concrete type are the literal rules, which now denote `ULift.{u} Nat` / `ULift.{u} String`.
Axioms: only those the original uses; no TRUSTED. Existing files are unchanged.

* `cvu_fun` / `cvub_fun` / `tdenu_fun` / `argsdenu_fun`: the simultaneous induction of `cvekv_fun` goes through at every universe `u` with the same proof text (see the instances `funct_u0` / `funct_u1`).
* Section `Cost`: what the move to `Type 1` does to rows (`ULift`), and what it does NOT solve (mixing a `Type 0` type with a `Type 1` type former, `Functor.map`-style rows). -/
namespace Tools.ShippingGen5CarrierU
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES

universe u

/-- A Lean value with its Lean type, the type in `Type u`. -/
structure DynU where
  ty : Type u
  val : ty

structure EntryU where
  τ : Expr
  d : DynU.{u}

abbrev ValU := List EntryU.{u}

inductive ArgU
  | tm (d : DynU.{u})
  | ty (T : Type u)

structure TyRowU where
  kinds : List Bool
  den : List ArgU.{u} → Option (Type u)

structure TmRowU where
  kinds : List Bool
  den : List ArgU.{u} → Option DynU.{u}

structure PrimTableU where
  tys : Name → List Level → Option TyRowU.{u}
  tms : Name → List Level → Option TmRowU.{u}

/-- the universe-polymorphic `pi_inj_fun` -/
theorem pi_inj_funU {A : Type u} {TB TB' : A → Type u} (h : ∀ a, TB a = TB' a) :
    ((a : A) → TB a) = ((a : A) → TB' a) := by
  have : TB = TB' := funext h
  subst this; rfl

mutual

inductive TDenU (PT : PrimTableU.{u}) (env : Environment) : ValU.{u} → Expr → Type u → Prop
  | pi {ρ : ValU.{u}} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type u}
      (hA : TDenU PT env ρ A TA) (TB : TA → Type u)
      (hB : ∀ a : TA, TDenU PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDenU PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : ValU.{u}} {c : Name} {ls : List Level} {args : List Expr} {row : TyRowU.{u}} {as : List ArgU.{u}} {T : Type u}
      (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenU PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenU PT env ρ τ T
  | tunfold {ρ : ValU.{u}} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type u}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDenU PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenU PT env ρ τ T
  /-- Q1: a `let` label denotes by EVALUATING the bound term and extending the valuation (no substitution). -/
  | tlet {ρ : ValU.{u}} {n : Name} {A v B : Expr} {nd : Bool} {TA : Type u} {av : TA} {T : Type u}
      (hA : TDenU PT env ρ A TA) (hv : CVU PT env ρ v A TA av)
      (hB : TDenU PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T) :
      TDenU PT env ρ (.letE n A v B nd) T

inductive ArgsDenU (PT : PrimTableU.{u}) (env : Environment) : ValU.{u} → List Bool → List Expr → List ArgU.{u} → Prop
  | nil {ρ : ValU.{u}} : ArgsDenU PT env ρ [] [] []
  | ty {ρ : ValU.{u}} {ks : List Bool} {e : Expr} {es : List Expr} {as : List ArgU.{u}} {T : Type u}
      (hT : TDenU PT env ρ e T) (hs : ArgsDenU PT env ρ ks es as) :
      ArgsDenU PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : ValU.{u}} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List ArgU.{u}} {α : Type u} {v : α}
      (hv : CVU PT env ρ e τ α v) (hs : ArgsDenU PT env ρ ks es as) :
      ArgsDenU PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

/-- The derivations seen from outside: a rule derivation, or one rule derivation whose label is converted with evidence (Q2). -/
inductive CVU (PT : PrimTableU.{u}) (env : Environment) : ValU.{u} → Expr → Expr → (α : Type u) → α → Prop
  | core {ρ : ValU.{u}} {e τ : Expr} {α : Type u} {v : α} (h : CVUB PT env ρ e τ α v) : CVU PT env ρ e τ α v
  /-- Q2: the label changes from `τ0` to `τ` only when BOTH denote the same Lean type `α` (`TDenU` evidence). -/
  | conv {ρ : ValU.{u}} {e τ0 τ : Expr} {α : Type u} {v : α} (h : CVUB PT env ρ e τ0 α v)
      (h0 : TDenU PT env ρ τ0 α) (h1 : TDenU PT env ρ τ α) : CVU PT env ρ e τ α v

/-- The rules. Label-determining positions (`lam` body, `app` function, `letE` body, `unfold` body) hold a `CVUB`; value positions hold a `CVU`. -/
inductive CVUB (PT : PrimTableU.{u}) (env : Environment) : ValU.{u} → Expr → Expr → (α : Type u) → α → Prop
  | natLit {ρ : ValU.{u}} {n : Nat} : CVUB PT env ρ (.lit (.natVal n)) (.const `Nat []) (ULift.{u} Nat) ⟨n⟩
  | strLit {ρ : ValU.{u}} {s : String} : CVUB PT env ρ (.lit (.strVal s)) (.const `String []) (ULift.{u} String) ⟨s⟩
  | bvar {ρ : ValU.{u}} {i : Nat} {en : EntryU.{u}} (h : ρ[i]? = some en) :
      CVUB PT env ρ (.bvar i) (liftS en.τ 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : ValU.{u}} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type u}
      (hA : TDenU PT env ρ A TA) (TB : TA → Type u) (f : (a : TA) → TB a)
      (a0 : TA) (hb : ∀ a : TA, CVUB PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVUB PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  /-- Q1: the label of the result is the `let`-binding of the argument, evaluated by `hx`; no `substS`. -/
  | app {ρ : ValU.{u}} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type u} (TB : TA → Type u)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDenU PT env ρ A TA) (hB : ∀ a : TA, TDenU PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVUB PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVU PT env ρ x A TA av)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVUB PT env ρ (.app fe x) (.letE n A x B false) (TB av) (fv av)
  | letE {ρ : ValU.{u}} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type u} {TB : Type u} {av : TA} {bv : TB}
      (hA : TDenU PT env ρ A TA) (hv : CVU PT env ρ v A TA av)
      (hb : CVUB PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVUB PT env ρ (.letE n A v b nd) (.letE n A v B nd) TB bv
  | unfold {ρ : ValU.{u}} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type u} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVUB PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVUB PT env ρ e τ α v
  | prim {ρ : ValU.{u}} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRowU.{u}} {as : List ArgU.{u}} {d : DynU.{u}}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenU PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenU PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVUB PT env ρ e (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty d.val

end

/-- A converted label with evidence for the new label only is as good as one with evidence for both (the old label's evidence is the rule's own). -/
theorem cvu_conv {PT : PrimTableU.{u}} {env : Environment} {ρ : ValU.{u}} {e τ τ' : Expr} {α : Type u} {v : α}
    (h : CVU PT env ρ e τ α v) (h0 : TDenU PT env ρ τ α) (h1 : TDenU PT env ρ τ' α) : CVU PT env ρ e τ' α v :=
  match h with
  | .core b => .conv b h0 h1
  | .conv b h0' _ => .conv b h0' h1

/-! ### Functionality (simultaneous induction, conversion included)

`cvub_fun` also gives the label (rules determine it); `cvu_fun` gives only `(α, v)`, which is all a converted derivation determines. -/

mutual

theorem tdenu_fun {PT : PrimTableU.{u}} {env : Environment} {ρ : ValU.{u}} {τ : Expr} {T : Type u}
    (h : TDenU PT env ρ τ T) {T' : Type u} (h' : TDenU PT env ρ τ T') : T = T' :=
  match h with
  | .pi hA TB hB =>
    match h' with
    | .pi hA' TB' hB' => by
        have e1 := tdenu_fun hA hA'
        subst e1
        exact pi_inj_funU fun a => tdenu_fun (hB a) (hB' a)
    | .tcon _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tcon hrow hnd hargs hT he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon hrow' hnd' hargs' hT' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
        have := argsdenu_fun hargs hargs'
        subst this
        rw [hT] at hT'; cases hT'; rfl
    | .tunfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .tlet .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tunfold hd hb he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon _ hnd' _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .tunfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact tdenu_fun hb hb'
    | .tlet .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tlet hA hv hB =>
    match h' with
    | .tlet hA' hv' hB' => by
        have e1 := tdenu_fun hA hA'
        subst e1
        obtain ⟨-, hav⟩ := cvu_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        exact tdenu_fun hB hB'
    | .tcon _ _ _ _ he' => (spine_ne he' (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he' => (spine_ne he' (by intros; simp [Expr.getAppFn])).elim
termination_by structural h

theorem argsdenu_fun {PT : PrimTableU.{u}} {env : Environment} {ρ : ValU.{u}} {ks : List Bool} {es : List Expr} {as : List ArgU.{u}}
    (h : ArgsDenU PT env ρ ks es as) {as' : List ArgU.{u}} (h' : ArgsDenU PT env ρ ks es as') : as = as' :=
  match h, h' with
  | .nil, .nil => rfl
  | .ty hT hs, .ty hT' hs' => by
      have e1 := tdenu_fun hT hT'
      subst e1
      rw [argsdenu_fun hs hs']
  | .tm hv hs, .tm hv' hs' => by
      obtain ⟨rfl, hw⟩ := cvu_fun hv hv'
      have := eq_of_heq hw
      subst this
      rw [argsdenu_fun hs hs']
termination_by structural h

theorem cvu_fun {PT : PrimTableU.{u}} {env : Environment} {ρ : ValU.{u}} {e τ : Expr} {α : Type u} {v : α}
    (h : CVU PT env ρ e τ α v) {τ' : Expr} {β : Type u} {w : β} (h' : CVU PT env ρ e τ' β w) :
    α = β ∧ HEq v w :=
  match h with
  | .core b =>
    match h' with
    | .core b' => (cvub_fun b b').2
    | .conv b' _ _ => (cvub_fun b b').2
  | .conv b _ _ =>
    match h' with
    | .core b' => (cvub_fun b b').2
    | .conv b' _ _ => (cvub_fun b b').2
termination_by structural h

theorem cvub_fun {PT : PrimTableU.{u}} {env : Environment} {ρ : ValU.{u}} {e τ : Expr} {α : Type u} {v : α}
    (h : CVUB PT env ρ e τ α v) {τ' : Expr} {β : Type u} {w : β} (h' : CVUB PT env ρ e τ' β w) :
    τ = τ' ∧ α = β ∧ HEq v w :=
  match h with
  | .natLit =>
    match h' with
    | .natLit => ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .strLit =>
    match h' with
    | .strLit => ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .bvar h1 =>
    match h' with
    | .bvar h2 => by
        have := Option.some.inj (h1.symm.trans h2)
        subst this
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .lam hA TB f a0 hb =>
    match h' with
    | .lam hA' TB' f' a0' hb' => by
        have e1 := tdenu_fun hA hA'
        subst e1
        obtain ⟨hB1, -, -⟩ := cvub_fun (hb a0) (hb' a0)
        subst hB1
        have hTB : TB = TB' := funext fun a => (cvub_fun (hb a) (hb' a)).2.1
        subst hTB
        have hf : f = f' := funext fun a => eq_of_heq (cvub_fun (hb a) (hb' a)).2.2
        subst hf
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | CVUB.app TB hA hB hf hx hnh =>
    match h' with
    | CVUB.app TB' hA' hB' hf' hx' hnh' => by
        obtain ⟨ht, -, hfv⟩ := cvub_fun hf hf'
        injection ht with h2 h3 h4 h5
        subst h2 h3 h4 h5
        have e1 := tdenu_fun hA hA'
        subst e1
        have hTB : TB = TB' := funext fun a => tdenu_fun (hB a) (hB' a)
        subst hTB
        have hfv := eq_of_heq hfv
        subst hfv
        obtain ⟨-, hav⟩ := cvu_fun hx hx'
        have hav := eq_of_heq hav
        subst hav
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_app he hnh).elim
    | .prim _ _ _ _ _ _ he => (spine_app he hnh).elim
  | .letE hA hv hb =>
    match h' with
    | .letE hA' hv' hb' => by
        have e1 := tdenu_fun hA hA'
        subst e1
        obtain ⟨-, hav⟩ := cvu_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        obtain ⟨hB, hTB, hbv⟩ := cvub_fun hb hb'
        subst hB hTB
        exact ⟨rfl, rfl, hbv⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .unfold hd hb he =>
    match h' with
    | .unfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact cvub_fun hb hb'
    | .prim _ _ hnd' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVUB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .prim hci hrow hnd hargs hd hty he =>
    match h' with
    | .prim hci' hrow' _ hargs' hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        rw [hrow] at hrow'; cases hrow'
        have := argsdenu_fun hargs hargs'
        subst this
        rw [hd] at hd'; cases hd'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVUB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
termination_by structural h

end

/-- `ConstValueE` for the valuation carrier, at a fixed level list. -/
def ConstValueUAt (PT : PrimTableU.{u}) (env : Environment) (X : Name) (ls : List Level) (α : Type u) (v : α) : Prop :=
  ∃ τ : Expr, CVU PT env [] (.const X ls) τ α v

theorem constValueUAt_functional (PT : PrimTableU.{u}) (env : Environment) (X : Name) (ls : List Level)
    {α β : Type u} {v : α} {w : β} (h : ConstValueUAt PT env X ls α v) (h' : ConstValueUAt PT env X ls β w) :
    α = β ∧ HEq v w :=
  let ⟨_, hv⟩ := h
  let ⟨_, hw⟩ := h'
  cvu_fun hv hw

/-- The `LS` choice (zero levels, fixed `X`-env) with the valuation carrier. -/
def CVLSKU (PT : PrimTableU.{u}) (env : Environment) (X : Name) (α : Type u) (v : α) : Prop :=
  ConstValueUAt PT env X (Tools.ShippingGen5ConstValueE.LS env X) α v

theorem cvlsku_functional (PT : PrimTableU.{u}) (env : Environment) (X : Name) {α β : Type u} {v : α} {w : β}
    (h : CVLSKU PT env X α v) (h' : CVLSKU PT env X β w) : α = β ∧ HEq v w :=
  constValueUAt_functional PT env X _ h h'

/-! ### the same theorems at two fixed universes (they are theorems in `u`, so any instance is immediate) -/
#check @cvu_fun.{0}
#check @cvu_fun.{1}
#check @cvu_fun.{2}
#check @tdenu_fun.{1}

/-! ## Cost: what `Type 1` does to the rows

(1) With the carrier at `u = 1` every `Type 0` denotation is lifted: `Nat` is denoted by `ULift.{1} Nat` (the literal rule above; `natRow1` below). Every existing row (`PTcorpus`: 51 value rows, 50 type rows) would need the lift,
and `ULift.up` / `ULift.down` appear in every `den`.
(2) The lift does NOT let a `Type 1`-valued carrier apply a `Type 0 → Type 0` function to the lifted types (`must_fail` below), and a lifted type has no inverse as a TYPE (`ULift A` does not give back `A`),
so the rows that motivated the move (`Functor.map`: `f : Type → Type` applied to `α β : Type`) cannot be written with one universe.
(3) Two strata can: an argument is `tm0` / `ty0` (the present `Dyn` / `Type`) or `tm1` / `ty1` (`Dyn.{1}` / `Type 1`). `functorMapRow2` is the `Functor.map` row; `functorMapRow2_spec` shows it computes `Functor.map`. -/

def natRow1 : TyRowU.{1} := ⟨[], fun _ => some (ULift.{1} Nat)⟩

open Lean Elab Command in
elab "#must_fail " c:command : command => do
  let saved ← get
  elabCommand c
  let hadErr := (← get).messages.hasErrors
  set saved
  unless hadErr do throwError "#must_fail: the command elaborated without error"

-- one universe: a `Type 0 → Type 0` function cannot take a lifted (`Type 1`) type
#must_fail example (f : Type → Type) (α : Type 1) : Type := f α
-- and `ULift A` is not `A`
#must_fail example (A : Type) : ULift.{1} A = A := rfl
-- control: the same application with a `Type 0` argument elaborates
example (f : Type → Type) (α : Type) : Type := f α

/-- two strata of arguments -/
inductive Arg2
  | tm0 (d : Tools.ShippingGen5ConstValueE.Dyn)
  | ty0 (T : Type)
  | tm1 (d : DynU.{1})
  | ty1 (T : Type 1)

open Classical in
/-- the `Functor.map.{0,0}` row on two strata: `f`, the `Functor f` instance are `Type 1`-typed terms; `α β` are `Type 0` types; `g`, `x` are `Type 0` terms -/
noncomputable def functorMapRow2 : List Arg2 → Option Tools.ShippingGen5ConstValueE.Dyn
  | [.tm1 ⟨t1, f⟩, .tm1 ⟨t2, i⟩, .ty0 α, .ty0 β, .tm0 ⟨t3, g⟩, .tm0 ⟨t4, x⟩] =>
    if h1 : t1 = (Type → Type) then
      let f' : Type → Type := cast h1 f
      if h2 : t2 = Functor f' then
        if h3 : t3 = (α → β) then
          if h4 : t4 = f' α then
            some ⟨f' β, @Functor.map f' (cast h2 i) α β (cast h3 g) (cast h4 x)⟩
          else none
        else none
      else none
    else none
  | _ => none

theorem functorMapRow2_spec (f : Type → Type) [i : Functor f] (α β : Type) (g : α → β) (x : f α) :
    functorMapRow2 [.tm1 ⟨_, f⟩, .tm1 ⟨_, i⟩, .ty0 α, .ty0 β, .tm0 ⟨_, g⟩, .tm0 ⟨_, x⟩] = some ⟨f β, Functor.map g x⟩ := by
  simp [functorMapRow2]
  rfl

/-- the row is not a function of the lifted types: feeding the right shape with a wrong `g` type gives `none` -/
theorem functorMapRow2_wrong (f : Type → Type) [i : Functor f] (α β γ : Type) (g : α → β) (x : f γ) (h : (f γ = f α) → False) :
    functorMapRow2 [.tm1 ⟨_, f⟩, .tm1 ⟨_, i⟩, .ty0 α, .ty0 β, .tm0 ⟨_, g⟩, .tm0 ⟨_, x⟩] = none := by
  simp [functorMapRow2]
  exact h

end Tools.ShippingGen5CarrierU
