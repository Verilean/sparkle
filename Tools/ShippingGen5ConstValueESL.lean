import Tools.ShippingGen5ConstValueES
set_option autoImplicit false
/-! # `EnvClosedS` over a SYNTACTIC level instantiation (issue sparkle-ledger-dd4-sound; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §SoundS2)

`CVEKS` still contains `Expr.instantiateLevelParams` (unfold body, prim declared type). Here: `instantiateLevelParamsS` (structural recursion on `Level` and `Expr`), the carrier `CVEKL`
(= `CVEKS` with that one function replaced; nothing else changed) and its functionality. `instantiateLevelParamsS` is NOT claimed equal to Lean's opaque `Expr.instantiateLevelParams`.
`EnvClosedS` over the syntactic version reduces to a plain closedness fact about the stored declarations (`EnvDeclClosed`): level instantiation preserves `lbr` (proved).
No TRUSTED, axiom, `sorry`, `native_decide`. `PT` is an arbitrary parameter. -/
namespace Tools.ShippingGen5ConstValueESL
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES

/-! ## Syntactic level instantiation -/

/-- Lookup of a level parameter in parallel name / level lists (first match; unchanged when absent or the lists run out, as in Lean). -/
def lookupLP : List Name → List Level → Name → Option Level
  | p :: ps, l :: ls, n => if p == n then some l else lookupLP ps ls n
  | _, _, _ => none

def instLevelS (ps : List Name) (ls : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (instLevelS ps ls l)
  | .max a b => .max (instLevelS ps ls a) (instLevelS ps ls b)
  | .imax a b => .imax (instLevelS ps ls a) (instLevelS ps ls b)
  | .param n => (lookupLP ps ls n).getD (.param n)
  | .mvar m => .mvar m

/-- Structural `instantiateLevelParams`: substitutes in `sort` and `const` levels and recurses through every `Expr` constructor. -/
def instantiateLevelParamsS (ps : List Name) (ls : List Level) : Expr → Expr
  | .sort u => .sort (instLevelS ps ls u)
  | .const c us => .const c (us.map (instLevelS ps ls))
  | .app f a => .app (instantiateLevelParamsS ps ls f) (instantiateLevelParamsS ps ls a)
  | .lam n A b bi => .lam n (instantiateLevelParamsS ps ls A) (instantiateLevelParamsS ps ls b) bi
  | .forallE n A b bi => .forallE n (instantiateLevelParamsS ps ls A) (instantiateLevelParamsS ps ls b) bi
  | .letE n A v b nd => .letE n (instantiateLevelParamsS ps ls A) (instantiateLevelParamsS ps ls v) (instantiateLevelParamsS ps ls b) nd
  | .mdata d e => .mdata d (instantiateLevelParamsS ps ls e)
  | .proj c i e => .proj c i (instantiateLevelParamsS ps ls e)
  | e => e

/-- Level instantiation does not touch loose bound variables. -/
theorem lbr_instantiateLevelParamsS (ps : List Name) (ls : List Level) : ∀ e : Expr, lbr (instantiateLevelParamsS ps ls e) = lbr e
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => rfl
  | .sort _ | .const .. => rfl
  | .app f a => by simp [instantiateLevelParamsS, lbr, lbr_instantiateLevelParamsS ps ls f, lbr_instantiateLevelParamsS ps ls a]
  | .lam _ A b _ => by simp [instantiateLevelParamsS, lbr, lbr_instantiateLevelParamsS ps ls A, lbr_instantiateLevelParamsS ps ls b]
  | .forallE _ A b _ => by simp [instantiateLevelParamsS, lbr, lbr_instantiateLevelParamsS ps ls A, lbr_instantiateLevelParamsS ps ls b]
  | .letE _ A v b _ => by
      simp [instantiateLevelParamsS, lbr, lbr_instantiateLevelParamsS ps ls A, lbr_instantiateLevelParamsS ps ls v, lbr_instantiateLevelParamsS ps ls b]
  | .mdata _ e => by simp [instantiateLevelParamsS, lbr, lbr_instantiateLevelParamsS ps ls e]
  | .proj _ _ e => by simp [instantiateLevelParamsS, lbr, lbr_instantiateLevelParamsS ps ls e]

/-- Level instantiation is the identity when there are no level parameters. -/
theorem instLevelS_nil (l : Level) : instLevelS [] [] l = l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [instLevelS, ih]
  | max a b iha ihb => simp [instLevelS, iha, ihb]
  | imax a b iha ihb => simp [instLevelS, iha, ihb]
  | param n => simp [instLevelS, lookupLP]
  | mvar m => rfl

theorem instantiateLevelParamsS_nil : ∀ e : Expr, instantiateLevelParamsS [] [] e = e
  | .bvar _ | .fvar _ | .mvar _ | .lit _ | .sort _ => by simp [instantiateLevelParamsS, instLevelS_nil]
  | .const c us => by
      have : us.map (instLevelS [] []) = us := by
        induction us with
        | nil => rfl
        | cons u us ih => simp only [List.map_cons, instLevelS_nil u, ih]
      simp only [instantiateLevelParamsS, this]
  | .app f a => by simp [instantiateLevelParamsS, instantiateLevelParamsS_nil f, instantiateLevelParamsS_nil a]
  | .lam _ A b _ => by simp [instantiateLevelParamsS, instantiateLevelParamsS_nil A, instantiateLevelParamsS_nil b]
  | .forallE _ A b _ => by simp [instantiateLevelParamsS, instantiateLevelParamsS_nil A, instantiateLevelParamsS_nil b]
  | .letE _ A v b _ => by simp [instantiateLevelParamsS, instantiateLevelParamsS_nil A, instantiateLevelParamsS_nil v, instantiateLevelParamsS_nil b]
  | .mdata _ e => by simp [instantiateLevelParamsS, instantiateLevelParamsS_nil e]
  | .proj _ _ e => by simp [instantiateLevelParamsS, instantiateLevelParamsS_nil e]

/-! ## `EnvClosedS` over the syntactic version -/

/-- The kernel-side fact the bridge reduces to: every stored declaration type / definition body has no loose bound variable. A fact about `env`, stated for the stored terms themselves
(no level instantiation). Named, assumed nowhere. -/
def EnvDeclClosed (env : Environment) : Prop :=
  (∀ (c : Name) (ci : ConstantInfo), env.find? c = some ci → lbr ci.type = 0) ∧
  (∀ (c : Name) (d : DefinitionVal), env.find? c = some (.defnInfo d) → lbr d.value = 0)

/-- `EnvClosedS` over `instantiateLevelParamsS`: closedness after instantiation, at every level list. -/
def EnvClosedL (env : Environment) : Prop :=
  (∀ (c : Name) (ls : List Level) (ci : ConstantInfo), env.find? c = some ci → lbr (instantiateLevelParamsS ci.levelParams ls ci.type) = 0) ∧
  (∀ (c : Name) (ls : List Level) (d : DefinitionVal), env.find? c = some (.defnInfo d) → lbr (instantiateLevelParamsS d.levelParams ls d.value) = 0)

/-- PROVED: the level-instantiation bridge of `EnvClosedS` disappears on the syntactic version; only plain declaration closedness remains. -/
theorem envClosedL_of_declClosed {env : Environment} (h : EnvDeclClosed env) : EnvClosedL env :=
  ⟨fun c ls ci hci => by rw [lbr_instantiateLevelParamsS]; exact h.1 c ci hci,
   fun c ls d hd => by rw [lbr_instantiateLevelParamsS]; exact h.2 c d hd⟩

/-- Converse: `lbr` is level-independent, so `EnvClosedL` and `EnvDeclClosed` are equivalent (instantiate at the empty level list). -/
theorem envDeclClosed_of_closedL {env : Environment} (h : EnvClosedL env) : EnvDeclClosed env :=
  ⟨fun c ci hci => by have := h.1 c [] ci hci; rwa [lbr_instantiateLevelParamsS] at this,
   fun c d hd => by have := h.2 c [] d hd; rwa [lbr_instantiateLevelParamsS] at this⟩

/-! ## The carrier `CVEKL` (copy of `CVEKS`, only `Expr.instantiateLevelParams` replaced) -/

mutual

inductive TDenL (PT : PrimTableK) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDenL PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDenL PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDenL PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenL PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenL PT env ρ τ T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDenL PT env ρ (betaS (instantiateLevelParamsS d.levelParams ls d.value) args) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenL PT env ρ τ T

inductive ArgsDenL (PT : PrimTableK) (env : Environment) : Val → List Bool → List Expr → List Arg → Prop
  | nil {ρ : Val} : ArgsDenL PT env ρ [] [] []
  | ty {ρ : Val} {ks : List Bool} {e : Expr} {es : List Expr} {as : List Arg} {T : Type}
      (hT : TDenL PT env ρ e T) (hs : ArgsDenL PT env ρ ks es as) :
      ArgsDenL PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : Val} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List Arg} {α : Type} {v : α}
      (hv : CVEKL PT env ρ e τ α v) (hs : ArgsDenL PT env ρ ks es as) :
      ArgsDenL PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

inductive CVEKL (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | natLit {ρ : Val} {n : Nat} : CVEKL PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n
  | strLit {ρ : Val} {s : String} : CVEKL PT env ρ (.lit (.strVal s)) (.const `String []) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVEKL PT env ρ (.bvar i) (liftS en.τ 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDenL PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      (a0 : TA) (hb : ∀ a : TA, CVEKL PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVEKL PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDenL PT env ρ A TA) (hB : ∀ a : TA, TDenL PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVEKL PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEKL PT env ρ x A TA av)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVEKL PT env ρ (.app fe x) (substS B 0 x) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDenL PT env ρ A TA) (hv : CVEKL PT env ρ v A TA av)
      (hb : CVEKL PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVEKL PT env ρ (.letE n A v b nd) (substS B 0 v) TB bv
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVEKL PT env ρ (betaS (instantiateLevelParamsS d.levelParams ls d.value) args) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEKL PT env ρ e τ α v
  /-- prim: the ONLY change from `CVE.prim` is the lookup `PT.tms c ls` (the key includes the spine's level list). -/
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenL PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenL PT env ρ (instForallS (instantiateLevelParamsS ci.levelParams ls ci.type) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEKL PT env ρ e (instForallS (instantiateLevelParamsS ci.levelParams ls ci.type) args) d.ty d.val

end

/-! ### Functionality with the level-indexed key (same proof as `cve_fun`; `spine_inj` already yields `ls = ls'`) -/

mutual

theorem tdenl_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDenL PT env ρ τ T) {T' : Type} (h' : TDenL PT env ρ τ T') : T = T' :=
  match h with
  | .pi hA TB hB =>
    match h' with
    | .pi hA' TB' hB' => by
        have e1 := tdenl_fun hA hA'
        subst e1
        exact pi_inj_fun fun a => tdenl_fun (hB a) (hB' a)
    | .tcon _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tcon hrow hnd hargs hT he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon hrow' hnd' hargs' hT' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
        have := argsdenl_fun hargs hargs'
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
        exact tdenl_fun hb hb'

theorem argsdenl_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenL PT env ρ ks es as) {as' : List Arg} (h' : ArgsDenL PT env ρ ks es as') : as = as' :=
  match h, h' with
  | .nil, .nil => rfl
  | .ty hT hs, .ty hT' hs' => by
      have e1 := tdenl_fun hT hT'
      subst e1
      rw [argsdenl_fun hs hs']
  | .tm hv hs, .tm hv' hs' => by
      obtain ⟨_, rfl, hw⟩ := cvekl_fun hv hv'
      have := eq_of_heq hw
      subst this
      rw [argsdenl_fun hs hs']

theorem cvekl_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEKL PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVEKL PT env ρ e τ' β w) :
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
        have e1 := tdenl_fun hA hA'
        subst e1
        obtain ⟨hB1, -, -⟩ := cvekl_fun (hb a0) (hb' a0)
        subst hB1
        have hTB : TB = TB' := funext fun a => (cvekl_fun (hb a) (hb' a)).2.1
        subst hTB
        have hf : f = f' := funext fun a => eq_of_heq (cvekl_fun (hb a) (hb' a)).2.2
        subst hf
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | CVEKL.app TB hA hB hf hx hnh =>
    match h' with
    | CVEKL.app TB' hA' hB' hf' hx' hnh' => by
        obtain ⟨ht, -, hfv⟩ := cvekl_fun hf hf'
        injection ht with h2 h3 h4 h5
        subst h3 h4 h5
        have e1 := tdenl_fun hA hA'
        subst e1
        have hTB : TB = TB' := funext fun a => tdenl_fun (hB a) (hB' a)
        subst hTB
        have hfv := eq_of_heq hfv
        subst hfv
        obtain ⟨-, -, hav⟩ := cvekl_fun hx hx'
        have hav := eq_of_heq hav
        subst hav
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_app he hnh).elim
    | .prim _ _ _ _ _ _ he => (spine_app he hnh).elim
  | .letE hA hv hb =>
    match h' with
    | .letE hA' hv' hb' => by
        have e1 := tdenl_fun hA hA'
        subst e1
        obtain ⟨-, -, hav⟩ := cvekl_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        obtain ⟨hB, hTB, hbv⟩ := cvekl_fun hb hb'
        subst hB hTB
        exact ⟨rfl, rfl, hbv⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .unfold hd hb he =>
    match h' with
    | .unfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact cvekl_fun hb hb'
    | .prim _ _ hnd' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEKL.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .prim hci hrow hnd hargs hd hty he =>
    match h' with
    | .prim hci' hrow' _ hargs' hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        rw [hrow] at hrow'; cases hrow'
        have := argsdenl_fun hargs hargs'
        subst this
        rw [hd] at hd'; cases hd'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEKL.app _ _ _ _ _ hnh' => (spine_app he hnh').elim

end

/-- `ConstValueE` for the level-syntactic carrier, at a fixed level list. -/
def ConstValueEAtL (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α : Type) (v : α) : Prop :=
  ∃ τ : Expr, CVEKL PT env [] (.const X ls) τ α v

theorem constValueEAtL_functional (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level)
    {α β : Type} {v : α} {w : β} (h : ConstValueEAtL PT env X ls α v) (h' : ConstValueEAtL PT env X ls β w) :
    α = β ∧ HEq v w :=
  let ⟨_, hv⟩ := h
  let ⟨_, hw⟩ := h'
  (cvekl_fun hv hw).2

def CVLSKL (PT : PrimTableK) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ConstValueEAtL PT env X (Tools.ShippingGen5ConstValueE.LS env X) α v

theorem cvlskl_functional (PT : PrimTableK) (env : Environment) (X : Name) {α β : Type} {v : α} {w : β}
    (h : CVLSKL PT env X α v) (h' : CVLSKL PT env X β w) : α = β ∧ HEq v w :=
  constValueEAtL_functional PT env X _ h h'

end Tools.ShippingGen5ConstValueESL
