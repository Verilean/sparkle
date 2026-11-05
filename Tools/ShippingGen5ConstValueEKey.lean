import Tools.ShippingGen5ConstValueELS
set_option autoImplicit false
/-! # `ConstValueE` with a level-indexed primitive table (D.D-4, issue sparkle-ledger-dd4-key; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Key)

Recommended key: `Name × List Level`. `PrimTableK` looks a row up by the constant AND the level list of the spine, so the same name used at two
different `ls` (`Bool.rec.{0}`, `Bool.rec.{1}`, ...) gets two independent rows. Everything else is `ConstValueE` unchanged: same rules, same
exclusivity (`IsDefn` / `¬ IsDefn`, app `hnh`), same `Dyn`/`TyRow`/`TmRow`. Functionality is re-proved for the new key (`cvek_fun`).
`PT` stays an arbitrary parameter; no axiom, no `sorry`, no TRUSTED. Soundness (`OblRowTyped`, ...) is neither assumed nor proved. -/
namespace Tools.ShippingGen5ConstValueEKey
open Lean Tools.ShippingGen5ConstValueE

/-- The primitive table keyed by `(Name, List Level)`: at most one row per key, by construction of `Option`. -/
structure PrimTableK where
  tys : Name → List Level → Option TyRow
  tms : Name → List Level → Option TmRow

/-- A `Name`-keyed table is a level-keyed table that ignores the levels. -/
def _root_.Tools.ShippingGen5ConstValueE.PrimTable.toK (PT : PrimTable) : PrimTableK := ⟨fun c _ => PT.tys c, fun c _ => PT.tms c⟩

/-- The level-polymorphic reading: a row that takes the level list as an argument gives one row per `(c, ls)`. -/
def PrimTableK.ofPoly (tys : Name → Option (List Level → TyRow)) (tms : Name → Option (List Level → TmRow)) : PrimTableK :=
  ⟨fun c ls => (tys c).map (· ls), fun c ls => (tms c).map (· ls)⟩

mutual

inductive TDenK (PT : PrimTableK) (env : Environment) : Val → Expr → Type → Prop
  | pi {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
      (hA : TDenK PT env ρ A TA) (TB : TA → Type)
      (hB : ∀ a : TA, TDenK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
      TDenK PT env ρ (.forallE n A B bi) ((a : TA) → TB a)
  | tcon {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {row : TyRow} {as : List Arg} {T : Type}
      (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenK PT env ρ row.kinds args as) (hT : row.den as = some T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenK PT env ρ τ T
  | tunfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {T : Type}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TDenK PT env ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) T)
      {τ : Expr} (he : τ = mkAppN (.const c ls) args.toArray) :
      TDenK PT env ρ τ T

inductive ArgsDenK (PT : PrimTableK) (env : Environment) : Val → List Bool → List Expr → List Arg → Prop
  | nil {ρ : Val} : ArgsDenK PT env ρ [] [] []
  | ty {ρ : Val} {ks : List Bool} {e : Expr} {es : List Expr} {as : List Arg} {T : Type}
      (hT : TDenK PT env ρ e T) (hs : ArgsDenK PT env ρ ks es as) :
      ArgsDenK PT env ρ (false :: ks) (e :: es) (.ty T :: as)
  | tm {ρ : Val} {ks : List Bool} {e τ : Expr} {es : List Expr} {as : List Arg} {α : Type} {v : α}
      (hv : CVEK PT env ρ e τ α v) (hs : ArgsDenK PT env ρ ks es as) :
      ArgsDenK PT env ρ (true :: ks) (e :: es) (.tm ⟨α, v⟩ :: as)

inductive CVEK (PT : PrimTableK) (env : Environment) : Val → Expr → Expr → (α : Type) → α → Prop
  | natLit {ρ : Val} {n : Nat} : CVEK PT env ρ (.lit (.natVal n)) (.const `Nat []) Nat n
  | strLit {ρ : Val} {s : String} : CVEK PT env ρ (.lit (.strVal s)) (.const `String []) String s
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) :
      CVEK PT env ρ (.bvar i) (en.τ.liftLooseBVars 0 (i + 1)) en.d.ty en.d.val
  | lam {ρ : Val} {n : Name} {A body : Expr} {bi : BinderInfo} {B : Expr} {TA : Type}
      (hA : TDenK PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
      (a0 : TA) (hb : ∀ a : TA, CVEK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
      CVEK PT env ρ (.lam n A body bi) (.forallE n A B bi) ((a : TA) → TB a) f
  | app {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
      {fv : (a : TA) → TB a} {av : TA}
      (hA : TDenK PT env ρ A TA) (hB : ∀ a : TA, TDenK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
      (hf : CVEK PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEK PT env ρ x A TA av)
      (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
      CVEK PT env ρ (.app fe x) (B.instantiate1 x) (TB av) (fv av)
  | letE {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA : Type} {TB : Type} {av : TA} {bv : TB}
      (hA : TDenK PT env ρ A TA) (hv : CVEK PT env ρ v A TA av)
      (hb : CVEK PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
      CVEK PT env ρ (.letE n A v b nd) (B.instantiate1 v) TB bv
  | unfold {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr} {α : Type} {v : α}
      (hd : env.find? c = some (.defnInfo d))
      (hb : CVEK PT env ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) τ α v)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEK PT env ρ e τ α v
  /-- prim: the ONLY change from `CVE.prim` is the lookup `PT.tms c ls` (the key includes the spine's level list). -/
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenK PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenK PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty)
      {e : Expr} (he : e = mkAppN (.const c ls) args.toArray) :
      CVEK PT env ρ e (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty d.val

end

/-! ### Functionality with the level-indexed key (same proof as `cve_fun`; `spine_inj` already yields `ls = ls'`) -/

mutual

theorem tdenk_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDenK PT env ρ τ T) {T' : Type} (h' : TDenK PT env ρ τ T') : T = T' :=
  match h with
  | .pi hA TB hB =>
    match h' with
    | .pi hA' TB' hB' => by
        have e1 := tdenk_fun hA hA'
        subst e1
        exact pi_inj_fun fun a => tdenk_fun (hB a) (hB' a)
    | .tcon _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tunfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .tcon hrow hnd hargs hT he =>
    match h' with
    | .pi .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .tcon hrow' hnd' hargs' hT' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hrow] at hrow'; cases hrow'
        have := argsdenk_fun hargs hargs'
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
        exact tdenk_fun hb hb'

theorem argsdenk_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenK PT env ρ ks es as) {as' : List Arg} (h' : ArgsDenK PT env ρ ks es as') : as = as' :=
  match h, h' with
  | .nil, .nil => rfl
  | .ty hT hs, .ty hT' hs' => by
      have e1 := tdenk_fun hT hT'
      subst e1
      rw [argsdenk_fun hs hs']
  | .tm hv hs, .tm hv' hs' => by
      obtain ⟨_, rfl, hw⟩ := cvek_fun hv hv'
      have := eq_of_heq hw
      subst this
      rw [argsdenk_fun hs hs']

theorem cvek_fun {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEK PT env ρ e τ α v) {τ' : Expr} {β : Type} {w : β} (h' : CVEK PT env ρ e τ' β w) :
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
        have e1 := tdenk_fun hA hA'
        subst e1
        obtain ⟨hB1, -, -⟩ := cvek_fun (hb a0) (hb' a0)
        subst hB1
        have hTB : TB = TB' := funext fun a => (cvek_fun (hb a) (hb' a)).2.1
        subst hTB
        have hf : f = f' := funext fun a => eq_of_heq (cvek_fun (hb a) (hb' a)).2.2
        subst hf
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | CVEK.app TB hA hB hf hx hnh =>
    match h' with
    | CVEK.app TB' hA' hB' hf' hx' hnh' => by
        obtain ⟨ht, -, hfv⟩ := cvek_fun hf hf'
        injection ht with h2 h3 h4 h5
        subst h3 h4 h5
        have e1 := tdenk_fun hA hA'
        subst e1
        have hTB : TB = TB' := funext fun a => tdenk_fun (hB a) (hB' a)
        subst hTB
        have hfv := eq_of_heq hfv
        subst hfv
        obtain ⟨-, -, hav⟩ := cvek_fun hx hx'
        have hav := eq_of_heq hav
        subst hav
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold _ _ he => (spine_app he hnh).elim
    | .prim _ _ _ _ _ _ he => (spine_app he hnh).elim
  | .letE hA hv hb =>
    match h' with
    | .letE hA' hv' hb' => by
        have e1 := tdenk_fun hA hA'
        subst e1
        obtain ⟨-, -, hav⟩ := cvek_fun hv hv'
        have hav := eq_of_heq hav
        subst hav
        obtain ⟨hB, hTB, hbv⟩ := cvek_fun hb hb'
        subst hB hTB
        exact ⟨rfl, rfl, hbv⟩
    | .unfold _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | .prim _ _ _ _ _ _ he => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
  | .unfold hd hb he =>
    match h' with
    | .unfold hd' hb' he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hd] at hd'; cases hd'
        exact cvek_fun hb hb'
    | .prim _ _ hnd' _ _ _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd⟩ hnd'
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEK.app _ _ _ _ _ hnh' => (spine_app he hnh').elim
  | .prim hci hrow hnd hargs hd hty he =>
    match h' with
    | .prim hci' hrow' _ hargs' hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        rw [hci] at hci'; cases hci'
        rw [hrow] at hrow'; cases hrow'
        have := argsdenk_fun hargs hargs'
        subst this
        rw [hd] at hd'; cases hd'
        exact ⟨rfl, rfl, HEq.rfl⟩
    | .unfold hd' _ he' => by
        obtain ⟨rfl, rfl, rfl⟩ := spine_inj (he.symm.trans he')
        exact absurd ⟨_, hd'⟩ hnd
    | .natLit | .strLit | .bvar _ | .lam .. | .letE .. => (spine_ne he (by intros; simp [Expr.getAppFn])).elim
    | CVEK.app _ _ _ _ _ hnh' => (spine_app he hnh').elim

end

/-! ### A `Name`-keyed derivation is a level-keyed derivation (`toK` loses nothing; the new key only adds rows) -/

mutual

theorem tden_toK {PT : PrimTable} {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDen PT env ρ τ T) : TDenK PT.toK env ρ τ T :=
  match h with
  | .pi hA TB hB => .pi (tden_toK hA) TB fun a => tden_toK (hB a)
  | .tcon hrow hnd hargs hT he => .tcon hrow hnd (argsden_toK hargs) hT he
  | .tunfold hd hb he => .tunfold hd (tden_toK hb) he

theorem argsden_toK {PT : PrimTable} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDen PT env ρ ks es as) : ArgsDenK PT.toK env ρ ks es as :=
  match h with
  | .nil => .nil
  | .ty hT hs => .ty (tden_toK hT) (argsden_toK hs)
  | .tm hv hs => .tm (cve_toK hv) (argsden_toK hs)

theorem cve_toK {PT : PrimTable} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVE PT env ρ e τ α v) : CVEK PT.toK env ρ e τ α v :=
  match h with
  | .natLit => .natLit
  | .strLit => .strLit
  | .bvar h1 => .bvar h1
  | .lam hA TB f a0 hb => .lam (tden_toK hA) TB f a0 fun a => cve_toK (hb a)
  | CVE.app TB hA hB hf hx hnh => CVEK.app TB (tden_toK hA) (fun a => tden_toK (hB a)) (cve_toK hf) (cve_toK hx) hnh
  | .letE hA hv hb => .letE (tden_toK hA) (cve_toK hv) (cve_toK hb)
  | .unfold hd hb he => .unfold hd (cve_toK hb) he
  | .prim hci hrow hnd hargs hd hty he => .prim hci hrow hnd (argsden_toK hargs) hd (tden_toK hty) he

end

/-- The shape of the soundness obligation for a level-keyed table, as a `Prop` def (NOT assumed, NOT proved; compare `OblRowTyped PT env`
in `ShippingGen5ConstValueESound`): for each KEY `(c, ls)` with a row, and each argument list the row accepts, the row's value type
matches the declared type instantiated at THIS `ls`. Per-key, so a finite table has finitely many obligations. -/
def OblRowTypedK (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (c : Name) (ls : List Level) (ci : ConstantInfo) (row : TmRow) (ρ : Val) (args : List Expr) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ArgsDenK PT env ρ row.kinds args as → row.den as = some d →
    TDenK PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty

/-- `ConstValueE` with the level-indexed table at a fixed level list. -/
def ConstValueEKAt (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α : Type) (v : α) : Prop :=
  ∃ τ : Expr, CVEK PT env [] (.const X ls) τ α v

theorem constValueEKAt_functional (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level)
    {α β : Type} {v : α} {w : β} (h : ConstValueEKAt PT env X ls α v) (h' : ConstValueEKAt PT env X ls β w) :
    α = β ∧ HEq v w :=
  let ⟨_, hv⟩ := h
  let ⟨_, hw⟩ := h'
  (cvek_fun hv hw).2

/-- The `LS` choice (`Tools/ShippingGen5ConstValueELS.lean`) composed with the level-indexed table. Type `ConstValueRel`. -/
def CVLSK (PT : PrimTableK) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ConstValueEKAt PT env X (Tools.ShippingGen5ConstValueE.LS env X) α v

end Tools.ShippingGen5ConstValueEKey
