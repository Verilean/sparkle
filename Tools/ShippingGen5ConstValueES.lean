import Tools.ShippingGen5ConstValueESoundK
set_option autoImplicit false
/-! # `ConstValueE` with a SYNTACTIC carrier `CVEKS` (issue sparkle-ledger-dd4-sound, reviewer decision D1 = a; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §SoundS)

`CVEKS` is `CVEK` (`Tools.ShippingGen5ConstValueEKey`) with the opaque operations replaced by the structural ones of `ShippingGen5ConstValueESoundK`:
bvar's type label uses `liftS`, app / letE use `substS`, the unfold step uses `betaS` (defined here), and prim's type uses `instForallS` (through `substS`).
Existing files are unchanged. `PT` stays an arbitrary parameter; no axiom, no `sorry`, no `native_decide`, no TRUSTED.

What is STILL an operation of Lean's `Expr` API in the carrier: `Expr.instantiateLevelParams` (unfold body, prim declared type), the kernel's `ConstantInfo`/`env.find?`,
and `Expr.getAppFn` (a structural function). `Expr.beta`, `Expr.instantiate1`, `Expr.liftLooseBVars` no longer occur. -/
namespace Tools.ShippingGen5ConstValueES
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK

/-- Structural beta of a head against an argument list: a `lam` head consumes one argument by `substS`; otherwise the spine is rebuilt. -/
def betaS : Expr → List Expr → Expr
  | .lam _ _ b _, a :: as => betaS (substS b 0 a) as
  | f, as => as.foldl Expr.app f

/-- `instForall` with the structural substitution. -/
def instForallS : Expr → List Expr → Expr
  | .forallE _ _ b _, a :: as => instForallS (substS b 0 a) as
  | e, _ => e

theorem betaS_nil (f : Expr) : betaS f [] = f := by cases f <;> rfl
theorem instForallS_nil (e : Expr) : instForallS e [] = e := by cases e <;> rfl
theorem instForallS_cons_forallE (n : Name) (A B : Expr) (bi : BinderInfo) (a : Expr) (as : List Expr) :
    instForallS (.forallE n A B bi) (a :: as) = instForallS (substS B 0 a) as := rfl

mutual

inductive TDenS (PT : PrimTableK) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDenS PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDenS PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDenS PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenS PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenS PT env ρ τ T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDenS PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenS PT env ρ τ T

inductive ArgsDenS (PT : PrimTableK) (env : Environment) : Val → List Bool → List Expr → List Arg → Prop
  | nil {ρ : Val} : ArgsDenS PT env ρ [] [] []
  | ty {ρ : Val} {ks : List Bool} {e : Expr} {es : List Expr} {as : List Arg} {T : Type}
      (hT : TDenS PT env ρ e T) (hs : ArgsDenS PT env ρ ks es as) :
      ArgsDenS PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : Val} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List Arg} {α : Type} {v : α}
      (hv : CVEKS PT env ρ e τ α v) (hs : ArgsDenS PT env ρ ks es as) :
      ArgsDenS PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

inductive CVEKS (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | natLit {ρ : Val} {n : Nat} : CVEKS PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n
  | strLit {ρ : Val} {s : String} : CVEKS PT env ρ (.lit (.strVal s)) (.const `String []) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVEKS PT env ρ (.bvar i) (liftS en.τ 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDenS PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      (a0 : TA) (hb : ∀ a : TA, CVEKS PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVEKS PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDenS PT env ρ A TA) (hB : ∀ a : TA, TDenS PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVEKS PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEKS PT env ρ x A TA av)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVEKS PT env ρ (.app fe x) (substS B 0 x) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDenS PT env ρ A TA) (hv : CVEKS PT env ρ v A TA av)
      (hb : CVEKS PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVEKS PT env ρ (.letE n A v b nd) (substS B 0 v) TB bv
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVEKS PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEKS PT env ρ e τ α v
  /-- prim: the ONLY change from `CVE.prim` is the lookup `PT.tms c ls` (the key includes the spine's level list). -/
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenS PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenS PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEKS PT env ρ e (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty d.val

end

/-! ### Functionality with the level-indexed key (same proof as `cve_fun`; `spine_inj` already yields `ls = ls'`) -/

mutual

theorem tdens_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDenS PT env ρ τ T) {T' : Type} (h' : TDenS PT env ρ τ T') : T = T' :=
  match h with
  | .pi hA TB hB =>
    match h' with
    | .pi hA' TB' hB' => by
        have e1 := tdens_fun hA hA'
        subst e1
        exact pi_inj_fun fun a => tdens_fun (hB a) (hB' a)
    | .tcon _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tcon hrow hnd hargs hT he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon hrow' hnd' hargs' hT' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
        have := argsdens_fun hargs hargs'
        subst this
        rw [hT] at hT'; cases hT'; rfl
    | .tunfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
  | .tunfold hd hb he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon _ hnd' _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .tunfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact tdens_fun hb hb'

theorem argsdens_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenS PT env ρ ks es as) {as' : List Arg} (h' : ArgsDenS PT env ρ ks es as') : as = as' :=
  match h, h' with
  | .nil, .nil => rfl
  | .ty hT hs, .ty hT' hs' => by
      have e1 := tdens_fun hT hT'
      subst e1
      rw [argsdens_fun hs hs']
  | .tm hv hs, .tm hv' hs' => by
      obtain ⟨_, rfl, hw⟩ := cveks_fun hv hv'
      have := eq_of_heq hw
      subst this
      rw [argsdens_fun hs hs']

theorem cveks_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEKS PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVEKS PT env ρ e τ' β w) :
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
        have e1 := tdens_fun hA hA'
        subst e1
        obtain ⟨hB1, -, -⟩ := cveks_fun (hb a0) (hb' a0)
        subst hB1
        have hTB : TB = TB' := funext fun a => (cveks_fun (hb a) (hb' a)).2.1
        subst hTB
        have hf : f = f' := funext fun a => eq_of_heq (cveks_fun (hb a) (hb' a)).2.2
        subst hf
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | CVEKS.app TB hA hB hf hx hnh =>
    match h' with
    | CVEKS.app TB' hA' hB' hf' hx' hnh' => by
        obtain ⟨ht, -, hfv⟩ := cveks_fun hf hf'
        injection ht with h2 h3 h4 h5
        subst h3 h4 h5
        have e1 := tdens_fun hA hA'
        subst e1
        have hTB : TB = TB' := funext fun a => tdens_fun (hB a) (hB' a)
        subst hTB
        have hfv := eq_of_heq hfv
        subst hfv
        obtain ⟨-, -, hav⟩ := cveks_fun hx hx'
        have hav := eq_of_heq hav
        subst hav
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_app he hnh).elim
    | .prim _ _ _ _ _ _ he => (spine_app he hnh).elim
  | .letE hA hv hb =>
    match h' with
    | .letE hA' hv' hb' => by
        have e1 := tdens_fun hA hA'
        subst e1
        obtain ⟨-, -, hav⟩ := cveks_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        obtain ⟨hB, hTB, hbv⟩ := cveks_fun hb hb'
        subst hB hTB
        exact ⟨rfl, rfl, hbv⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .unfold hd hb he =>
    match h' with
    | .unfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact cveks_fun hb hb'
    | .prim _ _ hnd' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEKS.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .prim hci hrow hnd hargs hd hty he =>
    match h' with
    | .prim hci' hrow' _ hargs' hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        rw [hrow] at hrow'; cases hrow'
        have := argsdens_fun hargs hargs'
        subst this
        rw [hd] at hd'; cases hd'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEKS.app _ _ _ _ _ hnh' => (spine_app he hnh').elim

end


/-- `ConstValueE` for the syntactic carrier, at a fixed level list. -/
def ConstValueEAtS (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α : Type) (v : α) : Prop :=
  ∃ τ : Expr, CVEKS PT env [] (.const X ls) τ α v

theorem constValueEAtS_functional (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level)
    {α β : Type} {v : α} {w : β} (h : ConstValueEAtS PT env X ls α v) (h' : ConstValueEAtS PT env X ls β w) :
    α = β ∧ HEq v w :=
  let ⟨_, hv⟩ := h
  let ⟨_, hw⟩ := h'
  (cveks_fun hv hw).2

/-- The `LS` choice (zero levels, fixed `X`-env) with the syntactic carrier: the final carrier shape. Claims are per root, at the zero-level instance only. -/
def CVLSKS (PT : PrimTableK) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ConstValueEAtS PT env X (Tools.ShippingGen5ConstValueE.LS env X) α v

theorem cvlsks_functional (PT : PrimTableK) (env : Environment) (X : Name) {α β : Type} {v : α} {w : β}
    (h : CVLSKS PT env X α v) (h' : CVLSKS PT env X β w) : α = β ∧ HEq v w :=
  constValueEAtS_functional PT env X _ h h'

end Tools.ShippingGen5ConstValueES
