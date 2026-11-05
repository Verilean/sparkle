import Tools.ShippingGen5ConstValueEV
set_option autoImplicit false
/-! # Prototype (P): proofs erased to `PUnit` (issue sparkle-ledger-dd4-final, Q-A (ii); draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Compare)

Types and the smallest lemmas only; NOT a carrier proposal and NOT connected to `PTcorpus`. A COPY of the `CVEKV` calculus (`Tools.ShippingGen5ConstValueEV`) with ONE new rule `CVPB.thm`:
a spine headed by a THEOREM denotes the erased proof `PUnit.unit : PUnit`, its label (the declared type of the theorem, as for `prim`) must denote `PUnit`.
Prop-valued type formers (`Eq`, `Nat.le`, `LT.lt` through its unfolding, ...) are ordinary type rows whose `den` is `PUnit`; a Prop binder is an argument `.tm ⟨PUnit, PUnit.unit⟩`.
Exclusivity: `thm` requires `PT.tms c ls = none` and `thmInfo`, so it is disjoint from `prim` (a row) and `unfold` (`defnInfo`).
* `cvp_fun`: functionality of the extended calculus (the induction of `cvekv_fun` plus the three new cases).
* Section `Rows`: a row that takes an erased proof argument (`Fin.mk`) CHECKS the proposition itself (`Classical`), so a derivation for an ill-typed use (`Fin.mk 5 7 _`) does not exist, although `conv` can move any proof between Prop labels.
Axioms: only those the original uses (and `Classical.choice` for the row). No TRUSTED. Existing files are unchanged. -/
namespace Tools.ShippingGen5CarrierP
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES

mutual

inductive TDenP (PT : PrimTableK) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDenP PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDenP PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDenP PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenP PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenP PT env ρ τ T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDenP PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenP PT env ρ τ T
  /-- Q1: a `let` label denotes by EVALUATING the bound term and extending the valuation (no substitution). -/
  | tlet {ρ : Val} {n : Name} {A v B : Expr} {nd : Bool} {TA : Type} {av : TA} {T : Type}
      (hA : TDenP PT env ρ A TA) (hv : CVP PT env ρ v A TA av)
      (hB : TDenP PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T) :
      TDenP PT env ρ (.letE n A v B nd) T

inductive ArgsDenP (PT : PrimTableK) (env : Environment) : Val → List Bool → List Expr → List Arg → Prop
  | nil {ρ : Val} : ArgsDenP PT env ρ [] [] []
  | ty {ρ : Val} {ks : List Bool} {e : Expr} {es : List Expr} {as : List Arg} {T : Type}
      (hT : TDenP PT env ρ e T) (hs : ArgsDenP PT env ρ ks es as) :
      ArgsDenP PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : Val} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List Arg} {α : Type} {v : α}
      (hv : CVP PT env ρ e τ α v) (hs : ArgsDenP PT env ρ ks es as) :
      ArgsDenP PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

/-- The derivations seen from outside: a rule derivation, or one rule derivation whose label is converted with evidence (Q2). -/
inductive CVP (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | core {ρ : Val} {e τ : Expr} {α : Type} {v : α} (h : CVPB PT env ρ e τ α v) : CVP PT env ρ e τ α v
  /-- Q2: the label changes from `τ0` to `τ` only when BOTH denote the same Lean type `α` (`TDenP` evidence). -/
  | conv {ρ : Val} {e τ0 τ : Expr} {α : Type} {v : α} (h : CVPB PT env ρ e τ0 α v)
      (h0 : TDenP PT env ρ τ0 α) (h1 : TDenP PT env ρ τ α) : CVP PT env ρ e τ α v

/-- The rules. Label-determining positions (`lam` body, `app` function, `letE` body, `unfold` body) hold a `CVPB`; value positions hold a `CVP`. -/
inductive CVPB (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | natLit {ρ : Val} {n : Nat} : CVPB PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n
  | strLit {ρ : Val} {s : String} : CVPB PT env ρ (.lit (.strVal s)) (.const `String []) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVPB PT env ρ (.bvar i) (liftS en.τ 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDenP PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      (a0 : TA) (hb : ∀ a : TA, CVPB PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVPB PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  /-- Q1: the label of the result is the `let`-binding of the argument, evaluated by `hx`; no `substS`. -/
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDenP PT env ρ A TA) (hB : ∀ a : TA, TDenP PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVPB PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVP PT env ρ x A TA av)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVPB PT env ρ (.app fe x) (.letE n A x B false) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDenP PT env ρ A TA) (hv : CVP PT env ρ v A TA av)
      (hb : CVPB PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVPB PT env ρ (.letE n A v b nd) (.letE n A v B nd) TB bv
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVPB PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVPB PT env ρ e τ α v
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenP PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenP PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVPB PT env ρ e (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty d.val
  /-- (P) a theorem-headed spine denotes the ERASED proof `PUnit.unit`. The label is the declared type of the theorem (as for `prim`), and it must denote `PUnit`
  (a Prop former whose row has `den = PUnit`). Exclusive with `prim` (no row) and `unfold` (not a definition). -/
  | thm {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo}
      (hci : env.find? c = some ci) (hthm : ∃ t, env.find? c = some (.thmInfo t)) (hrow : PT.tms c ls = none)
      (hT : TDenP PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) PUnit)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVPB PT env ρ e (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) PUnit PUnit.unit

end

/-- A converted label with evidence for the new label only is as good as one with evidence for both (the old label's evidence is the rule's own). -/
theorem cvp_conv {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ τ' : Expr} {α : Type} {v : α}
    (h : CVP PT env ρ e τ α v) (h0 : TDenP PT env ρ τ α) (h1 : TDenP PT env ρ τ' α) : CVP PT env ρ e τ' α v :=
  match h with
  | .core b => .conv b h0 h1
  | .conv b h0' _ => .conv b h0' h1

/-! ### Functionality (simultaneous induction, conversion included)

`cvpb_fun` also gives the label (rules determine it); `cvp_fun` gives only `(α, v)`, which is all a converted derivation determines. -/

mutual

theorem tdenp_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDenP PT env ρ τ T) {T' : Type} (h' : TDenP PT env ρ τ T') : T = T' :=
  match h with
  | .pi hA TB hB =>
    match h' with
    | .pi hA' TB' hB' => by
        have e1 := tdenp_fun hA hA'
        subst e1
        exact pi_inj_fun fun a => tdenp_fun (hB a) (hB' a)
    | .tcon _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tcon hrow hnd hargs hT he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon hrow' hnd' hargs' hT' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
        have := argsdenp_fun hargs hargs'
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
        exact tdenp_fun hb hb'
    | .tlet .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tlet hA hv hB =>
    match h' with
    | .tlet hA' hv' hB' => by
        have e1 := tdenp_fun hA hA'
        subst e1
        obtain ⟨-, hav⟩ := cvp_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        exact tdenp_fun hB hB'
    | .tcon _ _ _ _ he' => (spine_ne he' (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he' => (spine_ne he' (by intros; simp [Expr.getAppFn])).elim
termination_by structural h

theorem argsdenp_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenP PT env ρ ks es as) {as' : List Arg} (h' : ArgsDenP PT env ρ ks es as') : as = as' :=
  match h, h' with
  | .nil, .nil => rfl
  | .ty hT hs, .ty hT' hs' => by
      have e1 := tdenp_fun hT hT'
      subst e1
      rw [argsdenp_fun hs hs']
  | .tm hv hs, .tm hv' hs' => by
      obtain ⟨rfl, hw⟩ := cvp_fun hv hv'
      have := eq_of_heq hw
      subst this
      rw [argsdenp_fun hs hs']
termination_by structural h

theorem cvp_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVP PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVP PT env ρ e τ' β w) :
    α = β ∧ HEq v w :=
  match h with
  | .core b =>
    match h' with
    | .core b' => (cvpb_fun b b').2
    | .conv b' _ _ => (cvpb_fun b b').2
  | .conv b _ _ =>
    match h' with
    | .core b' => (cvpb_fun b b').2
    | .conv b' _ _ => (cvpb_fun b b').2
termination_by structural h

theorem cvpb_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVPB PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVPB PT env ρ e τ' β w) :
    τ = τ' ∧ α = β ∧ HEq v w :=
  match h with
  | .natLit =>
    match h' with
    | .natLit => ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .thm _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .strLit =>
    match h' with
    | .strLit => ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .thm _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .bvar h1 =>
    match h' with
    | .bvar h2 => by
        have := Option.some.inj (h1.symm.trans h2)
        subst this
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .thm _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .lam hA TB f a0 hb =>
    match h' with
    | .lam hA' TB' f' a0' hb' => by
        have e1 := tdenp_fun hA hA'
        subst e1
        obtain ⟨hB1, -, -⟩ := cvpb_fun (hb a0) (hb' a0)
        subst hB1
        have hTB : TB = TB' := funext fun a => (cvpb_fun (hb a) (hb' a)).2.1
        subst hTB
        have hf : f = f' := funext fun a => eq_of_heq (cvpb_fun (hb a) (hb' a)).2.2
        subst hf
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .thm _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | CVPB.app TB hA hB hf hx hnh =>
    match h' with
    | CVPB.app TB' hA' hB' hf' hx' hnh' => by
        obtain ⟨ht, -, hfv⟩ := cvpb_fun hf hf'
        injection ht with h2 h3 h4 h5
        subst h2 h3 h4 h5
        have e1 := tdenp_fun hA hA'
        subst e1
        have hTB : TB = TB' := funext fun a => tdenp_fun (hB a) (hB' a)
        subst hTB
        have hfv := eq_of_heq hfv
        subst hfv
        obtain ⟨-, hav⟩ := cvp_fun hx hx'
        have hav := eq_of_heq hav
        subst hav
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_app he hnh).elim
    | .prim _ _ _ _ _ _ he => (spine_app he hnh).elim
    | .thm _ _ _ _ he => (spine_app he hnh).elim
  | .letE hA hv hb =>
    match h' with
    | .letE hA' hv' hb' => by
        have e1 := tdenp_fun hA hA'
        subst e1
        obtain ⟨-, hav⟩ := cvp_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        obtain ⟨hB, hTB, hbv⟩ := cvpb_fun hb hb'
        subst hB hTB
        exact ⟨rfl, rfl, hbv⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .thm _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .unfold hd hb he =>
    match h' with
    | .unfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact cvpb_fun hb hb'
    | .prim _ _ hnd' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .thm _ ⟨t, ht⟩ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at ht; cases ht
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVPB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .prim hci hrow hnd hargs hd hty he =>
    match h' with
    | .prim hci' hrow' _ hargs' hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        rw [hrow] at hrow'; cases hrow'
        have := argsdenp_fun hargs hargs'
        subst this
        rw [hd] at hd'; cases hd'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .thm _ _ hrow' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVPB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .thm hci hthm hrow hT he =>
    match h' with
    | .thm hci' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        obtain ⟨t, ht⟩ := hthm
        rw [hd'] at ht; cases ht
    | .prim _ hrow' _ _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVPB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
termination_by structural h

end

/-- `ConstValueE` for the valuation carrier, at a fixed level list. -/
def ConstValuePAt (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α : Type) (v : α) : Prop :=
  ∃ τ : Expr, CVP PT env [] (.const X ls) τ α v

theorem constValuePAt_functional (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level)
    {α β : Type} {v : α} {w : β} (h : ConstValuePAt PT env X ls α v) (h' : ConstValuePAt PT env X ls β w) :
    α = β ∧ HEq v w :=
  let ⟨_, hv⟩ := h
  let ⟨_, hw⟩ := h'
  cvp_fun hv hw

/-- The `LS` choice (zero levels, fixed `X`-env) with the valuation carrier. -/
def CVLSKP (PT : PrimTableK) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ConstValuePAt PT env X (Tools.ShippingGen5ConstValueE.LS env X) α v

theorem cvlskp_functional (PT : PrimTableK) (env : Environment) (X : Name) {α β : Type} {v : α} {w : β}
    (h : CVLSKP PT env X α v) (h' : CVLSKP PT env X β w) : α = β ∧ HEq v w :=
  constValuePAt_functional PT env X _ h h'

/-! ## Rows -/

-- `Fin.mk`: kinds `[n, val, isLt]`, the proof is erased; the row checks `val < n` itself
open Classical in
noncomputable def finMkRow : List Arg → Option Dyn
  | [.tm ⟨t1, n⟩, .tm ⟨t2, v⟩, .tm ⟨t3, _⟩] =>
    if h1 : t1 = Nat then
      if h2 : t2 = Nat then
        if h3 : t3 = PUnit then
          if h : (cast h2 v : Nat) < (cast h1 n : Nat) then some ⟨Fin (cast h1 n), ⟨cast h2 v, h⟩⟩ else none
        else none
      else none
    else none
  | _ => none

/-- the erased proof argument of the right proposition gives the constructor -/
theorem finMkRow_spec (n v : Nat) (h : v < n) :
    finMkRow [.tm ⟨Nat, n⟩, .tm ⟨Nat, v⟩, .tm ⟨PUnit, PUnit.unit⟩] = some ⟨Fin n, ⟨v, h⟩⟩ := by
  simp [finMkRow, h]

/-- and a FALSE proposition has no row value, whatever (erased) proof argument is given: no junk value, the derivation just does not exist -/
theorem finMkRow_false (n v : Nat) (h : ¬ v < n) (p : PUnit) :
    finMkRow [.tm ⟨Nat, n⟩, .tm ⟨Nat, v⟩, .tm ⟨PUnit, p⟩] = none := by
  simp [finMkRow, h]

/-- all erased proofs are equal (so the argument list of the row is a function of the data) -/
theorem erased_proof_unique (p q : PUnit) : p = q := rfl

/-- proofs are interchangeable by `conv` between any two labels that denote `PUnit` (the carrier does not check that the label is the right proposition) -/
theorem conv_between_props {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ0 τ : Expr}
    (hd : CVPB PT env ρ e τ0 PUnit PUnit.unit) (h0 : TDenP PT env ρ τ0 PUnit) (h1 : TDenP PT env ρ τ PUnit) :
    CVP PT env ρ e τ PUnit PUnit.unit := .conv hd h0 h1

/-! ## Erasing PROPOSITIONS (not only proofs) loses types that depend on them

`Decidable p`, `Subtype`-like families and `if p then A else B` mention the proposition itself. If a Prop argument of a row were erased to `PUnit` as well (`Arg.ty PUnit`), the row could not tell
two propositions apart: whatever `den` is, it cannot produce both `Nat` (for `p := True`) and `PUnit` (for `p := False`). So a Prop-sorted TYPE argument must be kept (as data of sort `Prop`), only PROOFS are erased. -/

open Classical in
theorem erased_prop_arg_collision (den : List Arg → Option Type)
    (h : ∀ p : Prop, den [.ty PUnit] = some (if p then Nat else PUnit)) : False := by
  have h1 := h True
  have h2 := h False
  rw [h1] at h2
  simp only [if_pos trivial, if_neg not_false] at h2
  have e : Nat = PUnit := Option.some.inj h2
  have : (0 : Nat) = 1 := by
    have h0 : (cast e 0 : PUnit) = cast e 1 := rfl
    simpa using congrArg (cast e.symm) h0
  exact absurd this (by decide)

end Tools.ShippingGen5CarrierP
