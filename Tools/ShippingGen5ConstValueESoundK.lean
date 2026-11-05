import Tools.ShippingGen5ConstValueESound
import Tools.ShippingGen5ConstValueEKey
set_option autoImplicit false
/-! # Soundness of the `CVEK` rules (K1 key): per-rule lemmas and the NAMED OBLIGATIONS that remain
(issue sparkle-ledger-dd4-sound; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Sound)

Nothing here is a TRUSTED statement, an axiom, a `sorry` or `native_decide`; `PT` stays an arbitrary parameter; `OblLevelErase` is neither assumed nor proved.
Existing files are unchanged.

* §1 Own structural `lbr` / `liftS` / `substS` (the Lean ones, `looseBVarRange` / `liftLooseBVars` / `instantiate1`, are `opaque`) and what is PROVED about them.
  The link to the Lean operations is a BRIDGE obligation (`OblLiftAgree`, `OblInst1Agree`, `OblLbrZero`): a `Prop` definition, unresolved with the current API, never assumed.
* §2 The kernel-typing parameter `Ty` and the rule obligations. `TyRK` is an inductive rule judgment on which `OblBvar/OblApp/OblLam/OblConst` and the new
  `OblLit/OblLet/OblUnfold/OblPrimK` hold (so the obligation bundle is satisfiable, not vacuous). It is NOT the kernel judgment: `Ty ⊇ TyRK` for the kernel `Ty` is exactly the bundle.
* §3 `cvek_tyRK`: every `CVEK` derivation yields a `TyRK` derivation at the context `ρ.map Entry.τ` (rule-by-rule). `tyRK_sub` / `cvek_sound`: the bundle implies soundness for any `Ty`
  (an implication between named `Prop`s, used nowhere as an assumption).
* §4 What `CVEK ⇒ TDenK (type)` needs (`lam` B/TB correspondence): the cases that are proved and the obligations that are not.
* §5 `OblRowTypedK`, organised per key `(c, ls)`: finite and local. -/
namespace Tools.ShippingGen5ConstValueESoundK
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey

/-! ## §1 Structural loose-bvar operations -/

/-- Structural loose-bvar range (the intended meaning of `Expr.looseBVarRange`). -/
def lbr : Expr → Nat
  | .bvar i => i + 1
  | .app f a => max (lbr f) (lbr a)
  | .lam _ A b _ => max (lbr A) (lbr b - 1)
  | .forallE _ A b _ => max (lbr A) (lbr b - 1)
  | .letE _ A v b _ => max (max (lbr A) (lbr v)) (lbr b - 1)
  | .mdata _ e => lbr e
  | .proj _ _ e => lbr e
  | _ => 0

/-- Structural lift: bvars `≥ s` are shifted up by `n` (the intended meaning of `liftLooseBVars s n`). -/
def liftS : Expr → Nat → Nat → Expr
  | .bvar i, s, n => if i < s then .bvar i else .bvar (i + n)
  | .app f a, s, n => .app (liftS f s n) (liftS a s n)
  | .lam x A b bi, s, n => .lam x (liftS A s n) (liftS b (s + 1) n) bi
  | .forallE x A b bi, s, n => .forallE x (liftS A s n) (liftS b (s + 1) n) bi
  | .letE x A v b nd, s, n => .letE x (liftS A s n) (liftS v s n) (liftS b (s + 1) n) nd
  | .mdata d e, s, n => .mdata d (liftS e s n)
  | .proj c i e, s, n => .proj c i (liftS e s n)
  | e, _, _ => e

/-- Structural single substitution of bvar `k` by `x` (lower bvars stay, higher ones drop by one): `substS b 0 x` is the intended meaning of `b.instantiate1 x`. -/
def substS : Expr → Nat → Expr → Expr
  | .bvar i, k, x => if i < k then .bvar i else if i = k then liftS x 0 k else .bvar (i - 1)
  | .app f a, k, x => .app (substS f k x) (substS a k x)
  | .lam n A b bi, k, x => .lam n (substS A k x) (substS b (k + 1) x) bi
  | .forallE n A b bi, k, x => .forallE n (substS A k x) (substS b (k + 1) x) bi
  | .letE n A v b nd, k, x => .letE n (substS A k x) (substS v k x) (substS b (k + 1) x) nd
  | .mdata d e, k, x => .mdata d (substS e k x)
  | .proj c i e, k, x => .proj c i (substS e k x)
  | e, _, _ => e

theorem liftS_of_lbr_le (e : Expr) : ∀ (s n : Nat), lbr e ≤ s → liftS e s n = e := by
  induction e with
  | bvar i => intro s n h; simp only [lbr] at h; simp [liftS]; omega
  | app f a ihf iha =>
    intro s n h; simp only [lbr, Nat.max_le] at h
    simp [liftS, ihf s n h.1, iha s n h.2]
  | lam x A b bi ihA ihb =>
    intro s n h; simp only [lbr, Nat.max_le] at h
    simp [liftS, ihA s n h.1, ihb (s + 1) n (by omega)]
  | forallE x A b bi ihA ihb =>
    intro s n h; simp only [lbr, Nat.max_le] at h
    simp [liftS, ihA s n h.1, ihb (s + 1) n (by omega)]
  | letE x A v b nd ihA ihv ihb =>
    intro s n h; simp only [lbr, Nat.max_le] at h
    simp [liftS, ihA s n h.1.1, ihv s n h.1.2, ihb (s + 1) n (by omega)]
  | mdata d e ih => intro s n h; simp only [lbr] at h; simp [liftS, ih s n h]
  | proj c i e ih => intro s n h; simp only [lbr] at h; simp [liftS, ih s n h]
  | _ => intros; rfl

/-- `OblLiftClosed`, for the structural lift. -/
theorem liftS_closed (e : Expr) (h : lbr e = 0) (s n : Nat) : liftS e s n = e :=
  liftS_of_lbr_le e s n (by omega)

theorem liftS_zero (e : Expr) : ∀ s, liftS e s 0 = e := by
  induction e with
  | bvar i => intro s; simp [liftS]
  | app f a ihf iha => intro s; simp [liftS, ihf, iha]
  | lam x A b bi ihA ihb => intro s; simp [liftS, ihA, ihb]
  | forallE x A b bi ihA ihb => intro s; simp [liftS, ihA, ihb]
  | letE x A v b nd ihA ihv ihb => intro s; simp [liftS, ihA, ihv, ihb]
  | mdata d e ih => intro s; simp [liftS, ih]
  | proj c i e ih => intro s; simp [liftS, ih]
  | _ => intros; rfl

theorem substS_of_lbr_le (e : Expr) : ∀ (k : Nat) (x : Expr), lbr e ≤ k → substS e k x = e := by
  induction e with
  | bvar i => intro k x h; simp only [lbr] at h; simp [substS]; omega
  | app f a ihf iha =>
    intro k x h; simp only [lbr, Nat.max_le] at h
    simp [substS, ihf k x h.1, iha k x h.2]
  | lam n A b bi ihA ihb =>
    intro k x h; simp only [lbr, Nat.max_le] at h
    simp [substS, ihA k x h.1, ihb (k + 1) x (by omega)]
  | forallE n A b bi ihA ihb =>
    intro k x h; simp only [lbr, Nat.max_le] at h
    simp [substS, ihA k x h.1, ihb (k + 1) x (by omega)]
  | letE n A v b nd ihA ihv ihb =>
    intro k x h; simp only [lbr, Nat.max_le] at h
    simp [substS, ihA k x h.1.1, ihv k x h.1.2, ihb (k + 1) x (by omega)]
  | mdata d e ih => intro k x h; simp only [lbr] at h; simp [substS, ih k x h]
  | proj c i e ih => intro k x h; simp only [lbr] at h; simp [substS, ih k x h]
  | _ => intros; rfl

/-- `instantiate1` of a closed expression: the structural substitution is the identity. -/
theorem substS_closed (e : Expr) (h : lbr e = 0) (x : Expr) : substS e 0 x = e :=
  substS_of_lbr_le e 0 x (by omega)

/-- A `bvar` just under `k` binders is untouched below `k`, replaced at `k` by the `k`-lifted argument, lowered above. -/
theorem substS_bvar_lt (i k : Nat) (x : Expr) (h : i < k) : substS (.bvar i) k x = .bvar i := by simp [substS, h]
theorem substS_bvar_eq (k : Nat) (x : Expr) : substS (.bvar k) k x = liftS x 0 k := by simp [substS]
theorem substS_bvar_gt (i k : Nat) (x : Expr) (h : k < i) : substS (.bvar i) k x = .bvar (i - 1) := by
  have h1 : ¬ i < k := by omega
  have h2 : ¬ i = k := by omega
  simp [substS, h1, h2]

/-- Bridges to the `opaque` Lean operations: `Prop` definitions only (never assumed, not proved). They are `opaque` (`@[extern]`), so no equation
lemma is available with the current API and derivations: UNRESOLVED (not shown impossible). `OblLbrZero` is the intended reading of `Expr.data`'s 20-bit
`looseBVarRange` field (`Expr.mkData` panics beyond `2^20 - 1`, so it is meant for expressions built without that panic). -/
def OblLiftAgree : Prop := ∀ (e : Expr) (s n : Nat), e.liftLooseBVars s n = liftS e s n
def OblInst1Agree : Prop := ∀ (b x : Expr), b.instantiate1 x = substS b 0 x
def OblLbrZero : Prop := ∀ e : Expr, e.looseBVarRange = 0 → lbr e = 0

/-- `OblLiftClosed` reduces to the two bridges (an implication between named `Prop`s; neither is assumed anywhere). -/
theorem oblLiftClosed_of_bridges (hl : OblLiftAgree) (hz : OblLbrZero) : OblLiftClosed := by
  intro e s n h
  rw [hl]; exact liftS_closed e (hz e h) s n

/-- The same for `instantiate1` of a closed codomain. -/
theorem inst1_closed_of_bridges (hi : OblInst1Agree) (hz : OblLbrZero) (b x : Expr) (h : b.looseBVarRange = 0) :
    b.instantiate1 x = b := by
  rw [hi]; exact substS_closed b (hz b h) x

/-- `instForall` through non-dependent codomains with closed bodies: no dependency on the arguments. -/
theorem instForall_nondep_closed (hi : OblInst1Agree) (hz : OblLbrZero) (n : Name) (A B : Expr) (bi : BinderInfo)
    (hB : B.looseBVarRange = 0) (a : Expr) (as : List Expr) :
    instForall (.forallE n A B bi) (a :: as) = instForall B as := by
  rw [instForall_cons_forallE, inst1_closed_of_bridges hi hz B a hB]

/-! ## §2 Rule obligations over the kernel-typing parameter `Ty`, and a rule judgment on which they hold -/

abbrev TyJ := Environment → List Expr → Expr → Expr → Prop

/-- O-lit: literals have `Nat` / `String`. -/
def OblLit (Ty : TyJ) : Prop :=
  (∀ (env : Environment) (Γ : List Expr) (n : Nat), Ty env Γ (.lit (.natVal n)) (.const `Nat [])) ∧
  (∀ (env : Environment) (Γ : List Expr) (s : String), Ty env Γ (.lit (.strVal s)) (.const `String []))

/-- O-let (letE rule): the same shape as `CVEK.letE`. -/
def OblLet (Ty : TyJ) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (n : Name) (A v b B : Expr) (nd : Bool),
    Ty env Γ v A → Ty env (A :: Γ) b B → Ty env Γ (.letE n A v b nd) (B.instantiate1 v)

/-- O-unfold (δβ type preservation): the type of a `defnInfo`-headed spine is the type of its instantiated, beta-reduced body (typing is up to conversion). -/
def OblUnfold (Ty : TyJ) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (c : Name) (ls : List Level) (args : List Expr) (d : DefinitionVal) (τ : Expr),
    env.find? c = some (.defnInfo d) →
    Ty env Γ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) τ →
    Ty env Γ (mkAppN (.const c ls) args.toArray) τ

/-- O-prim (the whole-spine rule of `CVEK.prim`): a spine headed by a row-carrying non-`defnInfo` constant, whose arguments denote, has the `instForall` type.
This is where the argument typing lives: the `ArgsDenK` premises must give `Ty` of each argument against the telescope (unresolved: type arguments are typed only through `TDenK`,
and `tcon` has no `hty`). -/
def OblPrimK (PT : PrimTableK) (Ty : TyJ) : Prop :=
  ∀ (env : Environment) (ρ : Val) (c : Name) (ls : List Level) (args : List Expr) (ci : ConstantInfo) (row : TmRow) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ¬ IsDefn env c → ArgsDenK PT env ρ row.kinds args as → row.den as = some d →
    TDenK PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty →
    Ty env (ρ.map Entry.τ) (mkAppN (.const c ls) args.toArray) (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args)

/-- The bundle: `Ty` satisfies every rule of `CVEK`. (A `Prop`; it appears only as the premise of the reduction theorems below.) -/
structure KernelRulesK (PT : PrimTableK) (Ty : TyJ) : Prop where
  bvar : OblBvar Ty
  app : OblApp Ty
  lam : OblLam Ty
  const : OblConst Ty
  lit : OblLit Ty
  letE : OblLet Ty
  unfold : OblUnfold Ty
  prim : OblPrimK PT Ty

/-- The rule judgment: one constructor per `CVEK` rule (plus `const`, which `CVEK` reaches through `prim`/`unfold`). Not the kernel judgment. -/
inductive TyRK (PT : PrimTableK) (env : Environment) : List Expr → Expr → Expr → Prop
  | natLit {Γ : List Expr} {n : Nat} : TyRK PT env Γ (.lit (.natVal n)) (.const `Nat [])
  | strLit {Γ : List Expr} {s : String} : TyRK PT env Γ (.lit (.strVal s)) (.const `String [])
  | bvar {Γ : List Expr} {i : Nat} {T : Expr} (h : Γ[i]? = some T) : TyRK PT env Γ (.bvar i) (T.liftLooseBVars 0 (i + 1))
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstantInfo} (h : env.find? c = some ci) :
      TyRK PT env Γ (.const c ls) (ci.type.instantiateLevelParams ci.levelParams ls)
  | app {Γ : List Expr} {f x A B : Expr} {n : Name} {bi : BinderInfo}
      (hf : TyRK PT env Γ f (.forallE n A B bi)) (hx : TyRK PT env Γ x A) : TyRK PT env Γ (.app f x) (B.instantiate1 x)
  | lam {Γ : List Expr} {A b B : Expr} {n : Name} {bi : BinderInfo}
      (hb : TyRK PT env (A :: Γ) b B) : TyRK PT env Γ (.lam n A b bi) (.forallE n A B bi)
  | letE {Γ : List Expr} {n : Name} {A v b B : Expr} {nd : Bool}
      (hv : TyRK PT env Γ v A) (hb : TyRK PT env (A :: Γ) b B) : TyRK PT env Γ (.letE n A v b nd) (B.instantiate1 v)
  | unfold {Γ : List Expr} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TyRK PT env Γ ((d.value.instantiateLevelParams d.levelParams ls).beta args.toArray) τ) :
      TyRK PT env Γ (mkAppN (.const c ls) args.toArray) τ
  | prim {ρ : Val} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {row : TmRow} {as : List Arg} {d : Dyn}
      (hci : env.find? c = some ci) (hrow : PT.tms c ls = some row) (hnd : ¬ IsDefn env c)
      (hargs : ArgsDenK PT env ρ row.kinds args as) (hd : row.den as = some d)
      (hty : TDenK PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty) :
      TyRK PT env (ρ.map Entry.τ) (mkAppN (.const c ls) args.toArray) (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args)

/-- `TyRK` as a `TyJ`. -/
def TyRKJ (PT : PrimTableK) : TyJ := fun env => TyRK PT env

/-- The bundle is satisfiable (non-vacuity): `TyRKJ` satisfies every rule. The four obligations that existed before are proved here, unconditionally. -/
theorem oblBvar_TyRK (PT : PrimTableK) : OblBvar (TyRKJ PT) := fun _ _ _ _ h => .bvar h
theorem oblApp_TyRK (PT : PrimTableK) : OblApp (TyRKJ PT) := fun _ _ _ _ _ _ _ _ hf hx => .app hf hx
theorem oblLam_TyRK (PT : PrimTableK) : OblLam (TyRKJ PT) := fun _ _ _ _ _ _ _ hb => .lam hb
theorem oblConst_TyRK (PT : PrimTableK) : OblConst (TyRKJ PT) := fun _ _ _ _ _ h => .const h
theorem oblLit_TyRK (PT : PrimTableK) : OblLit (TyRKJ PT) := ⟨fun _ _ _ => .natLit, fun _ _ _ => .strLit⟩
theorem oblLet_TyRK (PT : PrimTableK) : OblLet (TyRKJ PT) := fun _ _ _ _ _ _ _ _ hv hb => .letE hv hb
theorem oblUnfold_TyRK (PT : PrimTableK) : OblUnfold (TyRKJ PT) := fun _ _ _ _ _ _ _ hd hb => .unfold hd hb
theorem oblPrimK_TyRK (PT : PrimTableK) : OblPrimK PT (TyRKJ PT) :=
  fun _ _ _ _ _ _ _ _ _ hci hrow hnd hargs hd hty => .prim hci hrow hnd hargs hd hty

theorem kernelRulesK_TyRK (PT : PrimTableK) : KernelRulesK PT (TyRKJ PT) :=
  ⟨oblBvar_TyRK PT, oblApp_TyRK PT, oblLam_TyRK PT, oblConst_TyRK PT, oblLit_TyRK PT, oblLet_TyRK PT, oblUnfold_TyRK PT, oblPrimK_TyRK PT⟩

/-- `TyRK` is contained in every `Ty` satisfying the bundle (rule induction). -/
theorem tyRK_sub {PT : PrimTableK} {Ty : TyJ} (R : KernelRulesK PT Ty) {env : Environment} {Γ : List Expr} {e τ : Expr}
    (h : TyRK PT env Γ e τ) : Ty env Γ e τ := by
  induction h with
  | natLit => exact R.lit.1 _ _ _
  | strLit => exact R.lit.2 _ _ _
  | bvar h => exact R.bvar _ _ _ _ h
  | const h => exact R.const _ _ _ _ _ h
  | app _ _ ihf ihx => exact R.app _ _ _ _ _ _ _ _ ihf ihx
  | lam _ ih => exact R.lam _ _ _ _ _ _ _ ih
  | letE _ _ ihv ihb => exact R.letE _ _ _ _ _ _ _ _ ihv ihb
  | unfold hd _ ih => exact R.unfold _ _ _ _ _ _ _ hd ih
  | prim hci hrow hnd hargs hd hty => exact R.prim _ _ _ _ _ _ _ _ _ hci hrow hnd hargs hd hty

/-! ## §3 Every `CVEK` derivation is a `TyRK` derivation at the context `ρ.map Entry.τ` -/

theorem map_getElem?_entry (ρ : Val) (i : Nat) (en : Entry) (h : ρ[i]? = some en) : (ρ.map Entry.τ)[i]? = some en.τ := by
  simp [List.getElem?_map, h]

theorem cvek_tyRK {PT : PrimTableK} {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEK PT env ρ e τ α v) : TyRK PT env (ρ.map Entry.τ) e τ :=
  match h with
  | .natLit => .natLit
  | .strLit => .strLit
  | .bvar h1 => .bvar (map_getElem?_entry _ _ _ h1)
  | .lam _ _ _ a0 hb => .lam (cvek_tyRK (hb a0))
  | CVEK.app _ _ _ hf hx _ => .app (cvek_tyRK hf) (cvek_tyRK hx)
  | .letE _ hv hb => .letE (cvek_tyRK hv) (cvek_tyRK hb)
  | .unfold hd hb he => he ▸ .unfold hd (cvek_tyRK hb)
  | .prim hci hrow hnd hargs hd hty he => he ▸ .prim hci hrow hnd hargs hd hty

/-- Soundness of the `CVEK` rules against any `Ty` that satisfies the bundle (a reduction to the named obligations). -/
theorem cvek_sound {PT : PrimTableK} {Ty : TyJ} (R : KernelRulesK PT Ty) {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEK PT env ρ e τ α v) : Ty env (ρ.map Entry.τ) e τ :=
  tyRK_sub R (cvek_tyRK h)

/-- The per-rule shape lemmas used above, stated alone. -/
theorem sound_bvar (PT : PrimTableK) (env : Environment) (ρ : Val) (i : Nat) (en : Entry) (h : ρ[i]? = some en) :
    TyRK PT env (ρ.map Entry.τ) (.bvar i) (en.τ.liftLooseBVars 0 (i + 1)) := .bvar (map_getElem?_entry _ _ _ h)

/-- The context extension of the `lam`/`letE`/`app` B-premise is exactly the valuation extension. -/
theorem map_cons_entry (A : Expr) (d : Dyn) (ρ : Val) : (⟨A, d⟩ :: ρ).map Entry.τ = A :: ρ.map Entry.τ := rfl

/-- A `bvar` whose entry type is closed has that entry type (using the bridges only through `OblLiftClosed`). -/
theorem bvar_type_closed (hL : OblLiftClosed) (en : Entry) (hc : en.τ.looseBVarRange = 0) (i : Nat) :
    en.τ.liftLooseBVars 0 (i + 1) = en.τ := hL en.τ 0 (i + 1) hc

/-- The spine type is the iterated `app` rule: `instForall` is a chain of `instantiate1` through the telescope. -/
inductive TyArgs (PT : PrimTableK) (env : Environment) (Γ : List Expr) : Expr → List Expr → Expr → Prop
  | nil {T : Expr} : TyArgs PT env Γ T [] T
  | cons {n : Name} {A B : Expr} {bi : BinderInfo} {a : Expr} {as : List Expr} {R : Expr}
      (ha : TyRK PT env Γ a A) (hs : TyArgs PT env Γ (B.instantiate1 a) as R) : TyArgs PT env Γ (.forallE n A B bi) (a :: as) R

theorem tyArgs_instForall {PT : PrimTableK} {env : Environment} {Γ : List Expr} {T R : Expr} {as : List Expr}
    (h : TyArgs PT env Γ T as R) : instForall T as = R := by
  induction h with
  | nil => exact instForall_nil _
  | cons _ _ ih => rw [instForall_cons_forallE]; exact ih

theorem tyRK_spine {PT : PrimTableK} {env : Environment} {Γ : List Expr} {f T R : Expr} {as : List Expr}
    (hf : TyRK PT env Γ f T) (h : TyArgs PT env Γ T as R) : TyRK PT env Γ (as.foldl Expr.app f) R := by
  induction h generalizing f with
  | nil => exact hf
  | cons ha _ ih => exact ih (.app hf ha)

/-! ## §4 `CVEK ⇒ TDenK (type)`: the `lam` B/TB correspondence -/

/-- O-den-typed (invariant): the syntactic type `τ` of a derivable term denotes the semantic type `α`. NOT assumed; the cases below are proved, the rest are named. -/
def OblDenTyped (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α), CVEK PT env ρ e τ α v → TDenK PT env ρ τ α

/-- `lam`: if the body's type `B` denotes `TB a` at every extended valuation, then `∀ a, B` denotes `(a : TA) → TB a`. This is the B / TB correspondence. -/
theorem denTyped_lam {PT : PrimTableK} {env : Environment} {ρ : Val} {n : Name} {A B : Expr} {bi : BinderInfo} {TA : Type}
    (hA : TDenK PT env ρ A TA) (TB : TA → Type) (hB : ∀ a : TA, TDenK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
    TDenK PT env ρ (.forallE n A B bi) ((a : TA) → TB a) := .pi hA TB hB

/-- `lam`, from the body derivations and the body-level invariant (the premise is the invariant for derivations in the extended valuation). -/
theorem denTyped_lam_of_body {PT : PrimTableK} {env : Environment} {ρ : Val} {n : Name} {A body B : Expr} {bi : BinderInfo} {TA : Type}
    (ih : ∀ (ρ' : Val) (e τ : Expr) (α : Type) (v : α), CVEK PT env ρ' e τ α v → TDenK PT env ρ' τ α)
    (hA : TDenK PT env ρ A TA) (TB : TA → Type) (f : (a : TA) → TB a)
    (hb : ∀ a : TA, CVEK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) body B (TB a) (f a)) :
    TDenK PT env ρ (.forallE n A B bi) ((a : TA) → TB a) := .pi hA TB fun a => ih _ _ _ _ _ (hb a)

/- `prim` is `hty` itself and `unfold` reuses the body's `τ` and `α`, so both cases of `OblDenTyped` are immediate from the premise (no lemma needed). -/

/-- The remaining cases of `OblDenTyped`, each named (all UNRESOLVED; none is assumed):
* `OblDenLits`: the table has rows for `Nat` and `String` (`natLit` / `strLit` give `TDenK … (.const Nat []) Nat`);
* `OblDenSubst`: `TDenK` commutes with the substitution that `app` / `letE` perform (`B.instantiate1 x` denotes `TB av` when `B` denotes `TB a` at `⟨A, av⟩ :: ρ`);
* `OblDenBvar`: valuation well-formedness and weakening for `bvar` (`en.τ.liftLooseBVars 0 (i+1)` denotes `en.d.ty` in `ρ`). -/
def OblDenLits (PT : PrimTableK) (env : Environment) : Prop :=
  (∀ ρ : Val, TDenK PT env ρ (.const `Nat []) Nat) ∧ (∀ ρ : Val, TDenK PT env ρ (.const `String []) String)
def OblDenSubst (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (A B x : Expr) (TA : Type) (TB : TA → Type) (av : TA), TDenK PT env ρ A TA →
    (∀ a : TA, TDenK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) → CVEK PT env ρ x A TA av →
    TDenK PT env ρ (B.instantiate1 x) (TB av)
def OblDenBvar (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (i : Nat) (en : Entry), ρ[i]? = some en → TDenK PT env ρ (en.τ.liftLooseBVars 0 (i + 1)) en.d.ty

/-! ## §5 `OblRowTypedK`, per key -/

/-- The obligation of ONE key `(c, ls)`: finite and local. -/
def RowTypedAt (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) : Prop :=
  ∀ (ci : ConstantInfo) (row : TmRow) (ρ : Val) (args : List Expr) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ArgsDenK PT env ρ row.kinds args as → row.den as = some d →
    TDenK PT env ρ (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty

theorem oblRowTypedK_iff (PT : PrimTableK) (env : Environment) :
    OblRowTypedK PT env ↔ ∀ (c : Name) (ls : List Level), RowTypedAt PT env c ls :=
  ⟨fun h c ls ci row ρ args as d => h c ls ci row ρ args as d,
   fun h c ls ci row ρ args as d => h c ls ci row ρ args as d⟩

/-- A key without a row has no obligation. -/
theorem rowTypedAt_of_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (h : PT.tms c ls = none) :
    RowTypedAt PT env c ls := by
  intro ci row ρ args as d _ hrow; rw [h] at hrow; cases hrow

/-- A row whose `den` is always `none` has no obligation (a derivation through it cannot exist: the `Type 0` escape). -/
theorem rowTypedAt_of_den_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow)
    (hrow : PT.tms c ls = some row) (hden : ∀ as, row.den as = none) : RowTypedAt PT env c ls := by
  intro ci row' ρ args as d _ hrow' _ hd
  rw [hrow] at hrow'; cases hrow'
  rw [hden] at hd; cases hd

/-- A finite table: a key outside the finite list has no row; then the whole obligation is the conjunction over the list. -/
theorem oblRowTypedK_of_keys (PT : PrimTableK) (env : Environment) (keys : List (Name × List Level))
    (hkeys : ∀ c ls, PT.tms c ls ≠ none → (c, ls) ∈ keys) (h : ∀ k ∈ keys, RowTypedAt PT env k.1 k.2) : OblRowTypedK PT env :=
  (oblRowTypedK_iff PT env).2 fun c ls => by
    by_cases hn : PT.tms c ls = none
    · exact rowTypedAt_of_none PT env c ls hn
    · exact h (c, ls) (hkeys c ls hn)

/-- The argument list of a derivation has the length of the row's `kinds`. -/
theorem argsDenK_length {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenK PT env ρ ks es as) : es.length = ks.length ∧ as.length = ks.length :=
  match h with
  | .nil => ⟨rfl, rfl⟩
  | .ty _ hs => by have := argsDenK_length hs; simp [this.1, this.2]
  | .tm _ hs => by have := argsDenK_length hs; simp [this.1, this.2]

/-- A key whose row has no arguments (`kinds = []`): the obligation is the denotation of the declared type at `ls`. -/
theorem rowTypedAt_nullary (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow)
    (hrow : PT.tms c ls = some row) (hk : row.kinds = [])
    (h : ∀ (ci : ConstantInfo) (ρ : Val) (as : List Arg) (d : Dyn), env.find? c = some ci → ArgsDenK PT env ρ [] [] as → row.den as = some d →
      TDenK PT env ρ (ci.type.instantiateLevelParams ci.levelParams ls) d.ty) : RowTypedAt PT env c ls := by
  intro ci row' ρ args as d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  rw [hk] at hargs
  have hl := (argsDenK_length hargs).1
  have : args = [] := List.length_eq_zero_iff.mp (by simpa using hl)
  subst this
  have := h ci ρ as d hci hargs hd
  simpa [instForall_nil] using this

end Tools.ShippingGen5ConstValueESoundK
