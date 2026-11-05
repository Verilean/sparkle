import Tools.ShippingGen5ConstValueESProof
set_option autoImplicit false
/-! # `ConstValueE` with a VALUATION carrier `CVEKV` (issue sparkle-ledger-dd4-val, reviewer decisions Q1 = a, Q2 = a; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Val)

`CVEKV` is `CVEKS` (`Tools.ShippingGen5ConstValueES`) with two changes. Existing files are unchanged. `PT` stays an arbitrary parameter; no axiom, no `sorry`, no `native_decide`, no TRUSTED.

* **Q1 (valuation, no syntactic substitution).** `app` / `letE` evaluate the argument first and push it on the valuation. The TYPE LABEL of the result is therefore a `letE` binding, not `substS B 0 x`:
  `app` has label `.letE n A x B false`, `letE` has label `.letE n A v B nd`, and `TDenV` has a rule `tlet` that denotes such a label by evaluating `x` and extending the valuation.
  So the general substitution obligation `OblDenSubstS` does not occur: `denTypedV` has no such premise.
* **Q2 (evidence-carrying type conversion).** `CVEKV.conv` changes the type label `τ0 → τ` only with `TDenV ρ τ0 α` and `TDenV ρ τ α` (both denote the same Lean type `α`).
  It is not an unconditional conversion (negative control in `Tests/Gen5/ValCheck.lean`).

Layering: `CVEKVB` holds the rules, `CVEKV` is `CVEKVB` plus at most one `conv` on top. A `conv` is allowed where only `(α, v)` matters: arguments (`ArgsDenV.tm`, `app`'s `hx`, `letE`'s `hv`) and the root.
It is NOT allowed at the label-determining positions (`app`'s function, the bodies of `lam` / `letE`, the body of `unfold`). Converting the whole `lam` is the same as converting its body label (the `pi` rule),
but a converted FUNCTION label would give a second decomposition `(A', B')` of the same `Π`, and identifying the two needs injectivity of `Π` (not provable in Lean). -/
namespace Tools.ShippingGen5ConstValueEV
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES

mutual

inductive TDenV (PT : PrimTableK) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDenV PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDenV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDenV PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenV PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenV PT env ρ τ T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDenV PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenV PT env ρ τ T
  /-- Q1: a `let` label denotes by EVALUATING the bound term and extending the valuation (no substitution). -/
  | tlet {ρ : Val} {n : Name} {A v B : Expr} {nd : Bool} {TA : Type} {av : TA} {T : Type}
      (hA : TDenV PT env ρ A TA) (hv : CVEKV PT env ρ v A TA av)
      (hB : TDenV PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T) :
      TDenV PT env ρ (.letE n A v B nd) T

inductive ArgsDenV (PT : PrimTableK) (env : Environment) : Val → List Bool → List Expr → List Arg → Prop
  | nil {ρ : Val} : ArgsDenV PT env ρ [] [] []
  | ty {ρ : Val} {ks : List Bool} {e : Expr} {es : List Expr} {as : List Arg} {T : Type}
      (hT : TDenV PT env ρ e T) (hs : ArgsDenV PT env ρ ks es as) :
      ArgsDenV PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : Val} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List Arg} {α : Type} {v : α}
      (hv : CVEKV PT env ρ e τ α v) (hs : ArgsDenV PT env ρ ks es as) :
      ArgsDenV PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

/-- The derivations seen from outside: a rule derivation, or one rule derivation whose label is converted with evidence (Q2). -/
inductive CVEKV (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | core {ρ : Val} {e τ : Expr} {α : Type} {v : α} (h : CVEKVB PT env ρ e τ α v) : CVEKV PT env ρ e τ α v
  /-- Q2: the label changes from `τ0` to `τ` only when BOTH denote the same Lean type `α` (`TDenV` evidence). -/
  | conv {ρ : Val} {e τ0 τ : Expr} {α : Type} {v : α} (h : CVEKVB PT env ρ e τ0 α v)
      (h0 : TDenV PT env ρ τ0 α) (h1 : TDenV PT env ρ τ α) : CVEKV PT env ρ e τ α v

/-- The rules. Label-determining positions (`lam` body, `app` function, `letE` body, `unfold` body) hold a `CVEKVB`; value positions hold a `CVEKV`. -/
inductive CVEKVB (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | natLit {ρ : Val} {n : Nat} : CVEKVB PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n
  | strLit {ρ : Val} {s : String} : CVEKVB PT env ρ (.lit (.strVal s)) (.const `String []) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVEKVB PT env ρ (.bvar i) (liftS en.τ 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDenV PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      (a0 : TA) (hb : ∀ a : TA, CVEKVB PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVEKVB PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  /-- Q1: the label of the result is the `let`-binding of the argument, evaluated by `hx`; no `substS`. -/
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDenV PT env ρ A TA) (hB : ∀ a : TA, TDenV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVEKVB PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEKV PT env ρ x A TA av)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVEKVB PT env ρ (.app fe x) (.letE n A x B false) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDenV PT env ρ A TA) (hv : CVEKV PT env ρ v A TA av)
      (hb : CVEKVB PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVEKVB PT env ρ (.letE n A v b nd) (.letE n A v B nd) TB bv
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVEKVB PT env ρ (betaS (d.value.instantiateLevelParams d.levelParams ls) args) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEKVB PT env ρ e τ α v
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenV PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenV PT env ρ (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEKVB PT env ρ e (instForallS (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty d.val

end

/-- A converted label with evidence for the new label only is as good as one with evidence for both (the old label's evidence is the rule's own). -/
theorem cvekv_conv {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ τ' : Expr} {α : Type} {v : α}
    (h : CVEKV PT env ρ e τ α v) (h0 : TDenV PT env ρ τ α) (h1 : TDenV PT env ρ τ' α) : CVEKV PT env ρ e τ' α v :=
  match h with
  | .core b => .conv b h0 h1
  | .conv b h0' _ => .conv b h0' h1

/-! ### Functionality (simultaneous induction, conversion included)

`cvekvb_fun` also gives the label (rules determine it); `cvekv_fun` gives only `(α, v)`, which is all a converted derivation determines. -/

mutual

theorem tdenv_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDenV PT env ρ τ T) {T' : Type} (h' : TDenV PT env ρ τ T') : T = T' :=
  match h with
  | .pi hA TB hB =>
    match h' with
    | .pi hA' TB' hB' => by
        have e1 := tdenv_fun hA hA'
        subst e1
        exact pi_inj_fun fun a => tdenv_fun (hB a) (hB' a)
    | .tcon _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tcon hrow hnd hargs hT he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon hrow' hnd' hargs' hT' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
        have := argsdenv_fun hargs hargs'
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
        exact tdenv_fun hb hb'
    | .tlet .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tlet hA hv hB =>
    match h' with
    | .tlet hA' hv' hB' => by
        have e1 := tdenv_fun hA hA'
        subst e1
        obtain ⟨-, hav⟩ := cvekv_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        exact tdenv_fun hB hB'
    | .tcon _ _ _ _ he' => (spine_ne he' (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he' => (spine_ne he' (by intros; simp [Expr.getAppFn])).elim
termination_by structural h

theorem argsdenv_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenV PT env ρ ks es as) {as' : List Arg} (h' : ArgsDenV PT env ρ ks es as') : as = as' :=
  match h, h' with
  | .nil, .nil => rfl
  | .ty hT hs, .ty hT' hs' => by
      have e1 := tdenv_fun hT hT'
      subst e1
      rw [argsdenv_fun hs hs']
  | .tm hv hs, .tm hv' hs' => by
      obtain ⟨rfl, hw⟩ := cvekv_fun hv hv'
      have := eq_of_heq hw
      subst this
      rw [argsdenv_fun hs hs']
termination_by structural h

theorem cvekv_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEKV PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVEKV PT env ρ e τ' β w) :
    α = β ∧ HEq v w :=
  match h with
  | .core b =>
    match h' with
    | .core b' => (cvekvb_fun b b').2
    | .conv b' _ _ => (cvekvb_fun b b').2
  | .conv b _ _ =>
    match h' with
    | .core b' => (cvekvb_fun b b').2
    | .conv b' _ _ => (cvekvb_fun b b').2
termination_by structural h

theorem cvekvb_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEKVB PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVEKVB PT env ρ e τ' β w) :
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
        have e1 := tdenv_fun hA hA'
        subst e1
        obtain ⟨hB1, -, -⟩ := cvekvb_fun (hb a0) (hb' a0)
        subst hB1
        have hTB : TB = TB' := funext fun a => (cvekvb_fun (hb a) (hb' a)).2.1
        subst hTB
        have hf : f = f' := funext fun a => eq_of_heq (cvekvb_fun (hb a) (hb' a)).2.2
        subst hf
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | CVEKVB.app TB hA hB hf hx hnh =>
    match h' with
    | CVEKVB.app TB' hA' hB' hf' hx' hnh' => by
        obtain ⟨ht, -, hfv⟩ := cvekvb_fun hf hf'
        injection ht with h2 h3 h4 h5
        subst h2 h3 h4 h5
        have e1 := tdenv_fun hA hA'
        subst e1
        have hTB : TB = TB' := funext fun a => tdenv_fun (hB a) (hB' a)
        subst hTB
        have hfv := eq_of_heq hfv
        subst hfv
        obtain ⟨-, hav⟩ := cvekv_fun hx hx'
        have hav := eq_of_heq hav
        subst hav
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_app he hnh).elim
    | .prim _ _ _ _ _ _ he => (spine_app he hnh).elim
  | .letE hA hv hb =>
    match h' with
    | .letE hA' hv' hb' => by
        have e1 := tdenv_fun hA hA'
        subst e1
        obtain ⟨-, hav⟩ := cvekv_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        obtain ⟨hB, hTB, hbv⟩ := cvekvb_fun hb hb'
        subst hB hTB
        exact ⟨rfl, rfl, hbv⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .unfold hd hb he =>
    match h' with
    | .unfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact cvekvb_fun hb hb'
    | .prim _ _ hnd' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEKVB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .prim hci hrow hnd hargs hd hty he =>
    match h' with
    | .prim hci' hrow' _ hargs' hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        rw [hrow] at hrow'; cases hrow'
        have := argsdenv_fun hargs hargs'
        subst this
        rw [hd] at hd'; cases hd'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEKVB.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
termination_by structural h

end

/-- `ConstValueE` for the valuation carrier, at a fixed level list. -/
def ConstValueEAtV (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α : Type) (v : α) : Prop :=
  ∃ τ : Expr, CVEKV PT env [] (.const X ls) τ α v

theorem constValueEAtV_functional (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level)
    {α β : Type} {v : α} {w : β} (h : ConstValueEAtV PT env X ls α v) (h' : ConstValueEAtV PT env X ls β w) :
    α = β ∧ HEq v w :=
  let ⟨_, hv⟩ := h
  let ⟨_, hw⟩ := h'
  cvekv_fun hv hw

/-- The `LS` choice (zero levels, fixed `X`-env) with the valuation carrier. -/
def CVLSKV (PT : PrimTableK) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ConstValueEAtV PT env X (Tools.ShippingGen5ConstValueE.LS env X) α v

theorem cvlskv_functional (PT : PrimTableK) (env : Environment) (X : Name) {α β : Type} {v : α} {w : β}
    (h : CVLSKV PT env X α v) (h' : CVLSKV PT env X β w) : α = β ∧ HEq v w :=
  constValueEAtV_functional PT env X _ h h'


/-! ## Weakening (needed only for the well-formedness of valuations, as in `§SoundS`)

`InsV`, `insV_get`, `lbl_lt` / `lbl_ge` are reused from `ShippingGen5ConstValueESProof`. `EnvClosedS` is the same NAMED hypothesis (a bridge on `instantiateLevelParams`), used only here. -/

mutual

theorem tdenv_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {τ : Expr} {T : Type} (h : TDenV PT env ρ τ T) : TDenV PT env ρ' (liftS τ s 1) T :=
  match h with
  | .pi hA TB hB =>
    .pi (tdenv_wk hcl hI hA) TB fun a => tdenv_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hB a)
  | .tcon hrow hnd hargs hT he =>
    .tcon hrow hnd (argsdenv_wk hcl hI hargs) hT (by rw [he, liftS_mkAppN]; rfl)
  | .tunfold hd hb he => by
    have hb' := tdenv_wk hcl hI hb
    rw [liftS_betaS, liftS_closed _ (hcl.2 _ _ _ hd)] at hb'
    exact .tunfold hd hb' (by rw [he, liftS_mkAppN]; rfl)
  | .tlet hA hv hB =>
    .tlet (tdenv_wk hcl hI hA) (cvekv_wk hcl hI hv) (tdenv_wk hcl (.there ⟨_, ⟨_, _⟩⟩ hI) hB)
termination_by structural h

theorem argsdenv_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {ks : List Bool} {es : List Expr} {as : List Arg} (h : ArgsDenV PT env ρ ks es as) :
    ArgsDenV PT env ρ' ks (es.map (fun a => liftS a s 1)) as :=
  match h with
  | .nil => .nil
  | .ty hT hs => .ty (tdenv_wk hcl hI hT) (argsdenv_wk hcl hI hs)
  | .tm hv hs => .tm (cvekv_wk hcl hI hv) (argsdenv_wk hcl hI hs)
termination_by structural h

theorem cvekv_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {e τ : Expr} {α : Type} {v : α} (h : CVEKV PT env ρ e τ α v) :
    CVEKV PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
  match h with
  | .core b => .core (cvekvb_wk hcl hI b)
  | .conv b h0 h1 => .conv (cvekvb_wk hcl hI b) (tdenv_wk hcl hI h0) (tdenv_wk hcl hI h1)
termination_by structural h

theorem cvekvb_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {e τ : Expr} {α : Type} {v : α} (h : CVEKVB PT env ρ e τ α v) :
    CVEKVB PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
  match h with
  | .natLit => .natLit
  | .strLit => .strLit
  | .bvar (i := i) (en := en) h1 => by
    rcases insV_get hI i en h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [← lbl_lt en.τ i s h2]
      simp only [liftS, h2, if_true]
      exact .bvar h3
    · rw [← lbl_ge en.τ i s h2]
      simp only [liftS, show ¬ i < s by omega, if_false]
      exact .bvar h3
  | .lam hA TB f a0 hb =>
    .lam (tdenv_wk hcl hI hA) TB f a0 fun a => cvekvb_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hb a)
  | CVEKVB.app TB hA hB hf hx hnh => by
    refine CVEKVB.app TB (tdenv_wk hcl hI hA) (fun a => tdenv_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hB a)) (cvekvb_wk hcl hI hf) (cvekv_wk hcl hI hx) ?_
    rintro ⟨c, ls, hc⟩
    exact hnh ⟨c, ls, (getAppFn_liftS _ _ _ _ _).1 hc⟩
  | .letE hA hv hb =>
    .letE (tdenv_wk hcl hI hA) (cvekv_wk hcl hI hv) (cvekvb_wk hcl (.there ⟨_, ⟨_, _⟩⟩ hI) hb)
  | .unfold hd hb he => by
    have hb' := cvekvb_wk hcl hI hb
    rw [liftS_betaS, liftS_closed _ (hcl.2 _ _ _ hd)] at hb'
    exact .unfold hd hb' (by rw [he, liftS_mkAppN]; rfl)
  | .prim hci hrow hnd hargs hd hty he => by
    have hty' := tdenv_wk hcl hI hty
    rw [liftS_instForallS, liftS_closed _ (hcl.1 _ _ _ hci)] at hty' ⊢
    exact .prim hci hrow hnd (argsdenv_wk hcl hI hargs) hd hty' (by rw [he, liftS_mkAppN]; rfl)
termination_by structural h

end

/-! ## Soundness: `OblDenTyped` (`CVEKV ⇒ TDenV τ α`) closes every rule, with NO substitution obligation -/

/-- Valuation well-formedness (same shape as `WfValS`): each entry's lifted type denotes the entry's semantic type, in the valuation itself. -/
def WfValV (PT : PrimTableK) (env : Environment) (ρ : Val) : Prop :=
  ∀ (i : Nat) (en : Entry), ρ[i]? = some en → TDenV PT env ρ (liftS en.τ 0 (i + 1)) en.d.ty

theorem wfValV_nil (PT : PrimTableK) (env : Environment) : WfValV PT env [] := by
  intro i en h; simp at h

theorem wfValV_cons {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {ρ : Val} (hρ : WfValV PT env ρ)
    {A : Expr} {TA : Type} (hA : TDenV PT env ρ A TA) (a : TA) : WfValV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) := by
  intro i en h
  cases i with
  | zero =>
    simp at h; subst h
    exact tdenv_wk hcl (InsV.here ρ (E := ⟨A, ⟨TA, a⟩⟩)) hA
  | succ j =>
    simp at h
    have := tdenv_wk hcl (InsV.here ρ (E := ⟨A, ⟨TA, a⟩⟩)) (hρ j en h)
    rwa [liftS_liftS_add _ 0 0 (j + 1) 1 (Nat.le_refl _) (by omega)] at this

def OblDenTypedV (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α), WfValV PT env ρ → CVEKV PT env ρ e τ α v → TDenV PT env ρ τ α

/-- All eight rules (and `conv`) closed. Premises: the two literal rows (`OblDenLits`, a condition on `PT`) and `EnvClosedS` (bridge on `instantiateLevelParams`, used by weakening).
There is no `OblDenSubstS`: `app` / `letE` push the evaluated argument on the valuation and the label is a `tlet`. -/
theorem denTypedVB {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env)
    (hN : ∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenV PT env ρ (.const `String []) String)
    {ρ : Val} {e τ : Expr} {α : Type} {v : α} (hρ : WfValV PT env ρ) (h : CVEKVB PT env ρ e τ α v) :
    TDenV PT env ρ τ α :=
  match h with
  | .natLit => hN ρ
  | .strLit => hS ρ
  | .bvar h1 => hρ _ _ h1
  | .lam hA TB f a0 hb => .pi hA TB fun a => denTypedVB hcl hN hS (wfValV_cons hcl hρ hA a) (hb a)
  | CVEKVB.app (av := av) TB hA hB hf hx hnh => .tlet hA hx (hB av)
  | .letE (av := av) hA hv hb => .tlet hA hv (denTypedVB hcl hN hS (wfValV_cons hcl hρ hA av) hb)
  | .unfold hd hb he => denTypedVB hcl hN hS hρ hb
  | .prim hci hrow hnd hargs hd hty he => hty
termination_by structural h

theorem denTypedV {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env)
    (hN : ∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenV PT env ρ (.const `String []) String) :
    OblDenTypedV PT env :=
  fun _ _ _ _ _ hρ h =>
    match h with
    | .core b => denTypedVB hcl hN hS hρ b
    | .conv _ _ h1 => h1

end Tools.ShippingGen5ConstValueEV
