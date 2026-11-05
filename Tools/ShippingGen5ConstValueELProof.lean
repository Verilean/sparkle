import Tools.ShippingGen5ConstValueESL
import Tools.ShippingGen5ConstValueESProof
set_option autoImplicit false
/-! # Proofs about the level-syntactic carrier `CVEKL` (issue sparkle-ledger-dd4-sound; draft §SoundS3)

Port of `ShippingGen5ConstValueESProof` §2-§6 (weakening, substitution, `denTypedS`, `TyRKS`) from `CVEKS` to `CVEKL` (`ShippingGen5ConstValueESL`). The purely syntactic lemmas (§1 / §3 of the
original: `liftS` / `substS` / `betaS` / `instForallS` commutation, `InsV`, `SafeArg`) do not mention a carrier and are reused as they are. The only change is the hypothesis:
`EnvClosedL` (closedness AFTER `instantiateLevelParamsS`) in place of `EnvClosedS`; by `envClosedL_of_declClosed` it follows from the plain `EnvDeclClosed`.
No TRUSTED, axiom, `sorry`, `native_decide`. `PT` is an arbitrary parameter. -/
namespace Tools.ShippingGen5ConstValueELProof
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueESL

mutual

theorem tdenl_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {τ : Expr} {T : Type} (h : TDenL PT env ρ τ T) : TDenL PT env ρ' (liftS τ s 1) T :=
  match h with
  | .pi hA TB hB =>
    .pi (tdenl_wk hcl hI hA) TB fun a => tdenl_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hB a)
  | .tcon hrow hnd hargs hT he =>
    .tcon hrow hnd (argsdenl_wk hcl hI hargs) hT (by rw [he, liftS_mkAppN]; rfl)
  | .tunfold hd hb he => by
    have hb' := tdenl_wk hcl hI hb
    rw [liftS_betaS, liftS_closed _ (hcl.2 _ _ _ hd)] at hb'
    exact .tunfold hd hb' (by rw [he, liftS_mkAppN]; rfl)

theorem argsdenl_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {ks : List Bool} {es : List Expr} {as : List Arg} (h : ArgsDenL PT env ρ ks es as) :
    ArgsDenL PT env ρ' ks (es.map (fun a => liftS a s 1)) as :=
  match h with
  | .nil => .nil
  | .ty hT hs => .ty (tdenl_wk hcl hI hT) (argsdenl_wk hcl hI hs)
  | .tm hv hs => .tm (cvekl_wk hcl hI hv) (argsdenl_wk hcl hI hs)

theorem cvekl_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {e τ : Expr} {α : Type} {v : α} (h : CVEKL PT env ρ e τ α v) :
    CVEKL PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
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
    .lam (tdenl_wk hcl hI hA) TB f a0 fun a => cvekl_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hb a)
  | CVEKL.app TB hA hB hf hx hnh => by
    rw [liftS_substS _ 0 s 1 _ (Nat.zero_le _)]
    refine CVEKL.app TB (tdenl_wk hcl hI hA) (fun a => tdenl_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hB a)) (cvekl_wk hcl hI hf) (cvekl_wk hcl hI hx) ?_
    rintro ⟨c, ls, hc⟩
    exact hnh ⟨c, ls, (getAppFn_liftS _ _ _ _ _).1 hc⟩
  | .letE hA hv hb => by
    rw [liftS_substS _ 0 s 1 _ (Nat.zero_le _)]
    exact .letE (tdenl_wk hcl hI hA) (cvekl_wk hcl hI hv) (cvekl_wk hcl (.there ⟨_, ⟨_, _⟩⟩ hI) hb)
  | .unfold hd hb he => by
    have hb' := cvekl_wk hcl hI hb
    rw [liftS_betaS, liftS_closed _ (hcl.2 _ _ _ hd)] at hb'
    exact .unfold hd hb' (by rw [he, liftS_mkAppN]; rfl)
  | .prim hci hrow hnd hargs hd hty he => by
    have hty' := tdenl_wk hcl hI hty
    rw [liftS_instForallS, liftS_closed _ (hcl.1 _ _ _ hci)] at hty' ⊢
    exact .prim hci hrow hnd (argsdenl_wk hcl hI hargs) hd hty' (by rw [he, liftS_mkAppN]; rfl)

end

inductive SubVL (PT : PrimTableK) (env : Environment) (A : Expr) (TA : Type) (av : TA) (x : Expr) : Nat → Val → Val → Prop
  | here (ρ0 : Val) (hx : CVEKL PT env ρ0 x A TA av) : SubVL PT env A TA av x 0 (⟨A, ⟨TA, av⟩⟩ :: ρ0) ρ0
  | there {k : Nat} {ρ ρ' : Val} (en : Entry) : SubVL PT env A TA av x k ρ ρ' → SubVL PT env A TA av x (k + 1) (en :: ρ) (⟨substS en.τ k x, en.d⟩ :: ρ')

theorem subvl_get {PT : PrimTableK} {env : Environment} {A : Expr} {TA : Type} {av : TA} {x : Expr} {k : Nat} {ρ ρ' : Val}
    (hS : SubVL PT env A TA av x k ρ ρ') :
    ∀ (i : Nat) (en : Entry), ρ[i]? = some en →
      (i < k ∧ ρ'[i]? = some ⟨substS en.τ (k - i - 1) x, en.d⟩) ∨ (i = k ∧ en = ⟨A, ⟨TA, av⟩⟩) ∨ (k < i ∧ ρ'[i - 1]? = some en) := by
  induction hS with
  | here ρ0 hx =>
    intro i en h
    cases i with
    | zero => simp at h; right; left; exact ⟨rfl, h.symm⟩
    | succ j => right; right; simpa using h
  | there en0 _ ih =>
    intro i en h
    cases i with
    | zero => simp at h; subst h; left; simp
    | succ j =>
      simp at h
      rcases ih j en h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; refine ⟨by omega, ?_⟩
        simp only [List.getElem?_cons_succ]; rw [h2]; congr 3; omega
      · right; left; exact ⟨by omega, h2⟩
      · right; right
        refine ⟨by omega, ?_⟩
        cases j with
        | zero => omega
        | succ j' => simpa using h2

/-- Under `SubVL` the argument is derivable in the lifted block: weakening of `hx` by the `k` entries below the removed one. -/
theorem subvl_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {A : Expr} {TA : Type} {av : TA} {x : Expr} {k : Nat} {ρ ρ' : Val}
    (hS : SubVL PT env A TA av x k ρ ρ') : CVEKL PT env ρ' (liftS x 0 k) (liftS A 0 k) TA av := by
  induction hS with
  | here ρ0 hx => simpa [liftS_zero] using hx
  | @there k0 ρ0 ρ0' en _ ih =>
    have := cvekl_wk hcl (InsV.here ρ0' (E := ⟨substS en.τ k0 x, en.d⟩) ) ih
    rwa [liftS_liftS_add _ 0 0 _ 1 (Nat.le_refl _) (by omega), liftS_liftS_add _ 0 0 _ 1 (Nat.le_refl _) (by omega)] at this


mutual

theorem tdenl_subst {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {A : Expr} {TA : Type} {av : TA} {x : Expr} (hx : SafeArg x)
    {k : Nat} {ρ ρ' : Val} (hS : SubVL PT env A TA av x k ρ ρ') {τ : Expr} {T : Type} (h : TDenL PT env ρ τ T) :
    TDenL PT env ρ' (substS τ k x) T :=
  match h with
  | .pi hA TB hB =>
    .pi (tdenl_subst hcl hx hS hA) TB fun a => tdenl_subst hcl hx (.there ⟨_, ⟨_, a⟩⟩ hS) (hB a)
  | .tcon hrow hnd hargs hT he =>
    .tcon hrow hnd (argsdenl_subst hcl hx hS hargs) hT (by rw [he, substS_mkAppN]; rfl)
  | .tunfold hd hb he => by
    have hb' := tdenl_subst hcl hx hS hb
    rw [substS_betaS hx, substS_of_lbr_le _ k x (lbr_le_of_zero (hcl.2 _ _ _ hd) k)] at hb'
    exact .tunfold hd hb' (by rw [he, substS_mkAppN]; rfl)

theorem argsdenl_subst {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {A : Expr} {TA : Type} {av : TA} {x : Expr} (hx : SafeArg x)
    {k : Nat} {ρ ρ' : Val} (hS : SubVL PT env A TA av x k ρ ρ') {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenL PT env ρ ks es as) : ArgsDenL PT env ρ' ks (es.map (fun a => substS a k x)) as :=
  match h with
  | .nil => .nil
  | .ty hT hs => .ty (tdenl_subst hcl hx hS hT) (argsdenl_subst hcl hx hS hs)
  | .tm hv hs => .tm (cvekl_subst hcl hx hS hv) (argsdenl_subst hcl hx hS hs)

theorem cvekl_subst {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {A : Expr} {TA : Type} {av : TA} {x : Expr} (hx : SafeArg x)
    {k : Nat} {ρ ρ' : Val} (hS : SubVL PT env A TA av x k ρ ρ') {e τ : Expr} {α : Type} {v : α} (h : CVEKL PT env ρ e τ α v) :
    CVEKL PT env ρ' (substS e k x) (substS τ k x) α v :=
  match h with
  | .natLit => .natLit
  | .strLit => .strLit
  | .bvar (i := i) (en := en) h1 => by
    rcases subvl_get hS i en h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [substS_liftS_ge en.τ 0 (i + 1) k x (by omega), show k - (i + 1) = k - i - 1 by omega]
      simp only [substS, h2, if_true]
      exact .bvar h3
    · subst h2; subst h3
      rw [substS_liftS_in A 0 (i + 1) i x (Nat.zero_le _) (by omega)]
      simp only [substS, Nat.lt_irrefl, if_false, if_true, Nat.add_sub_cancel]
      exact subvl_wk hcl hS
    · rw [substS_liftS_in en.τ 0 (i + 1) k x (Nat.zero_le _) (by omega)]
      have h4 : ¬ i < k := by omega
      have h5 : ¬ i = k := by omega
      simp only [substS, h4, h5, if_false, Nat.add_sub_cancel]
      have := CVEKL.bvar (PT := PT) (env := env) h3
      rwa [show i - 1 + 1 = i by omega] at this
  | .lam hA TB f a0 hb =>
    .lam (tdenl_subst hcl hx hS hA) TB f a0 fun a => cvekl_subst hcl hx (.there ⟨_, ⟨_, a⟩⟩ hS) (hb a)
  | CVEKL.app TB hA hB hf hx' hnh => by
    rw [substS_substS _ 0 k _ x (Nat.zero_le _), Nat.sub_zero]
    refine CVEKL.app TB (tdenl_subst hcl hx hS hA) (fun a => tdenl_subst hcl hx (.there ⟨_, ⟨_, a⟩⟩ hS) (hB a))
      (cvekl_subst hcl hx hS hf) (cvekl_subst hcl hx hS hx') ?_
    rintro ⟨c, ls, hc⟩
    exact hnh ⟨c, ls, (getAppFn_substS _ k hx c ls).1 hc⟩
  | .letE hA hv hb => by
    rw [substS_substS _ 0 k _ x (Nat.zero_le _), Nat.sub_zero]
    exact .letE (tdenl_subst hcl hx hS hA) (cvekl_subst hcl hx hS hv) (cvekl_subst hcl hx (.there ⟨_, ⟨_, _⟩⟩ hS) hb)
  | .unfold hd hb he => by
    have hb' := cvekl_subst hcl hx hS hb
    rw [substS_betaS hx, substS_of_lbr_le _ k x (lbr_le_of_zero (hcl.2 _ _ _ hd) k)] at hb'
    exact .unfold hd hb' (by rw [he, substS_mkAppN]; rfl)
  | .prim hci hrow hnd hargs hd hty he => by
    have hty' := tdenl_subst hcl hx hS hty
    rw [substS_instForallS hx, substS_of_lbr_le _ k x (lbr_le_of_zero (hcl.1 _ _ _ hci) k)] at hty' ⊢
    exact .prim hci hrow hnd (argsdenl_subst hcl hx hS hargs) hd hty' (by rw [he, substS_mkAppN]; rfl)

end

/-- Valuation well-formedness: each entry's (lifted) type denotes the entry's semantic type, in the valuation itself. Empty valuations are well-formed. -/
def WfValL (PT : PrimTableK) (env : Environment) (ρ : Val) : Prop :=
  ∀ (i : Nat) (en : Entry), ρ[i]? = some en → TDenL PT env ρ (liftS en.τ 0 (i + 1)) en.d.ty

theorem wfValL_nil (PT : PrimTableK) (env : Environment) : WfValL PT env [] := by
  intro i en h; simp at h

/-- Extension by a binder whose type denotes `TA` keeps the valuation well-formed (uses weakening). -/
theorem wfValL_cons {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {ρ : Val} (hρ : WfValL PT env ρ)
    {A : Expr} {TA : Type} (hA : TDenL PT env ρ A TA) (a : TA) : WfValL PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) := by
  intro i en h
  cases i with
  | zero =>
    simp at h; subst h
    exact tdenl_wk hcl (InsV.here ρ (E := ⟨A, ⟨TA, a⟩⟩)) hA
  | succ j =>
    simp at h
    have := tdenl_wk hcl (InsV.here ρ (E := ⟨A, ⟨TA, a⟩⟩)) (hρ j en h)
    rwa [liftS_liftS_add _ 0 0 (j + 1) 1 (Nat.le_refl _) (by omega)] at this

/-- `OblDenBvar` (reviewer P1): for a well-formed valuation the `bvar` label denotes the entry's type. (Not for arbitrary valuations: an entry with a junk `τ` has none.) -/
def OblDenBvarL (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (i : Nat) (en : Entry), WfValL PT env ρ → ρ[i]? = some en → TDenL PT env ρ (liftS en.τ 0 (i + 1)) en.d.ty

theorem oblDenBvarL (PT : PrimTableK) (env : Environment) : OblDenBvarL PT env := fun _ _ _ hρ h => hρ _ _ h

/-- `OblDenLits`, as a lemma about rows (a condition on `PT`, so it is the premises): a nullary type row whose value is `T` denotes the constant. -/
theorem tdenL_const_nullary {PT : PrimTableK} {env : Environment} {c : Name} {ls : List Level} {row : TyRow} {T : Type}
    (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c) (hk : row.kinds = []) (hT : row.den [] = some T) (ρ : Val) :
    TDenL PT env ρ (.const c ls) T :=
  .tcon (args := []) (as := []) hrow hnd (by rw [hk]; exact .nil) hT rfl

theorem oblDenLitsL_of_rows {PT : PrimTableK} {env : Environment} {rn rs : TyRow}
    (hn : PT.tys `Nat [] = some rn) (hnnd : ¬ IsDefn env `Nat) (hnk : rn.kinds = []) (hnT : rn.den [] = some Nat)
    (hs : PT.tys `String [] = some rs) (hsnd : ¬ IsDefn env `String) (hsk : rs.kinds = []) (hsT : rs.den [] = some String) :
    (∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) ∧ (∀ ρ : Val, TDenL PT env ρ (.const `String []) String) :=
  ⟨tdenL_const_nullary hn hnnd hnk hnT, tdenL_const_nullary hs hsnd hsk hsT⟩

/-- `OblDenSubst`, general form (all `x`): NOT proved for the carrier. The restricted form for `SafeArg x` is `oblDenSubstL_safe`. -/
def OblDenSubstL (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (A B x : Expr) (TA : Type) (T : Type) (av : TA),
    TDenL PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T → CVEKL PT env ρ x A TA av → TDenL PT env ρ (substS B 0 x) T

/-- `OblDenSubst`, proved for an argument that is not a `lam`, not a `forallE` and not const-headed (`SafeArg`). -/
theorem oblDenSubstL_safe {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {ρ : Val} {A B x : Expr} {TA T : Type} {av : TA}
    (hx : SafeArg x) (hB : TDenL PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T) (hv : CVEKL PT env ρ x A TA av) : TDenL PT env ρ (substS B 0 x) T :=
  tdenl_subst hcl hx (SubVL.here ρ hv) hB

/-- `OblDenTyped` for the syntactic carrier: for every well-formed valuation, a derivation's syntactic type denotes its semantic type. -/
def OblDenTypedL (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α), WfValL PT env ρ → CVEKL PT env ρ e τ α v → TDenL PT env ρ τ α

/-- All eight rules closed. The premises are the named, unresolved items: the two literal rows (`OblDenLits`, a condition on `PT`), `EnvClosedL` (a bridge on `instantiateLevelParams`),
and `OblDenSubstL` for `app` / `letE` (proved only for `SafeArg` arguments, `oblDenSubstL_safe`). `bvar` uses well-formedness; `lam` / `prim` / `unfold` need nothing else. -/
theorem denTypedL_aux {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env)
    (hN : ∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenL PT env ρ (.const `String []) String)
    (hsub : OblDenSubstL PT env) {ρ : Val} {e τ : Expr} {α : Type} {v : α} (hρ : WfValL PT env ρ) (h : CVEKL PT env ρ e τ α v) :
    TDenL PT env ρ τ α :=
  match h with
  | .natLit => hN ρ
  | .strLit => hS ρ
  | .bvar h1 => hρ _ _ h1
  | .lam hA TB f a0 hb => .pi hA TB fun a => denTypedL_aux hcl hN hS hsub (wfValL_cons hcl hρ hA a) (hb a)
  | CVEKL.app (av := av) TB hA hB hf hx hnh => hsub _ _ _ _ _ _ _ (hB av) hx
  | .letE (av := av) hA hv hb => hsub _ _ _ _ _ _ _ (denTypedL_aux hcl hN hS hsub (wfValL_cons hcl hρ hA av) hb) hv
  | .unfold hd hb he => denTypedL_aux hcl hN hS hsub hρ hb
  | .prim hci hrow hnd hargs hd hty he => hty

theorem denTypedL {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env)
    (hN : ∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenL PT env ρ (.const `String []) String)
    (hsub : OblDenSubstL PT env) : OblDenTypedL PT env :=
  fun _ _ _ _ _ hρ h => denTypedL_aux hcl hN hS hsub hρ h


/-! ## §6 P2: the rule judgment `TyRKL` and the obligations `OblUnfoldL` / `OblPrimKL`

`TyRKL` is a SYNTACTIC typing judgment inside the carrier (reviewer decision D2 = a). It is NOT Lean's kernel typing and nothing here claims agreement with the kernel.
Its `prim` rule is the strong one: the spine's arguments are typed against the declared telescope (`TyArgsL`). -/

mutual

inductive TyRKL (PT : PrimTableK) (env : Environment) : List Expr → Expr → Expr → Prop
  | natLit {Γ : List Expr} {n : Nat} : TyRKL PT env Γ (.lit (.natVal n)) (.const `Nat [])
  | strLit {Γ : List Expr} {s : String} : TyRKL PT env Γ (.lit (.strVal s)) (.const `String [])
  | bvar {Γ : List Expr} {i : Nat} {T : Expr} (h : Γ[i]? = some T) : TyRKL PT env Γ (.bvar i) (liftS T 0 (i + 1))
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstantInfo} (h : env.find? c = some ci) :
      TyRKL PT env Γ (.const c ls) (instantiateLevelParamsS ci.levelParams ls ci.type)
  | app {Γ : List Expr} {f x A B : Expr} {n : Name} {bi : BinderInfo}
      (hf : TyRKL PT env Γ f (.forallE n A B bi)) (hx : TyRKL PT env Γ x A) : TyRKL PT env Γ (.app f x) (substS B 0 x)
  | lam {Γ : List Expr} {A b B : Expr} {n : Name} {bi : BinderInfo}
      (hb : TyRKL PT env (A :: Γ) b B) : TyRKL PT env Γ (.lam n A b bi) (.forallE n A B bi)
  | letE {Γ : List Expr} {n : Name} {A v b B : Expr} {nd : Bool}
      (hv : TyRKL PT env Γ v A) (hb : TyRKL PT env (A :: Γ) b B) : TyRKL PT env Γ (.letE n A v b nd) (substS B 0 v)
  | unfold {Γ : List Expr} {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} {τ : Expr}
      (hd : env.find? c = some (.defnInfo d))
      (hb : TyRKL PT env Γ (betaS (instantiateLevelParamsS d.levelParams ls d.value) args) τ) :
      TyRKL PT env Γ (mkAppN (.const c ls) args.toArray) τ
  | prim {Γ : List Expr} {c : Name} {ls : List Level} {args : List Expr} {ci : ConstantInfo} {R : Expr}
      (hci : env.find? c = some ci) (hnd : ¬ IsDefn env c)
      (hargs : TyArgsL PT env Γ (instantiateLevelParamsS ci.levelParams ls ci.type) args R) :
      TyRKL PT env Γ (mkAppN (.const c ls) args.toArray) R

/-- A spine typed against a telescope: each argument has the (instantiated) binder type; the result is `R`. -/
inductive TyArgsL (PT : PrimTableK) (env : Environment) : List Expr → Expr → List Expr → Expr → Prop
  | nil {Γ : List Expr} {T : Expr} : TyArgsL PT env Γ T [] T
  | cons {Γ : List Expr} {n : Name} {A B : Expr} {bi : BinderInfo} {a : Expr} {as : List Expr} {R : Expr}
      (ha : TyRKL PT env Γ a A) (hs : TyArgsL PT env Γ (substS B 0 a) as R) : TyArgsL PT env Γ (.forallE n A B bi) (a :: as) R

end

theorem tyArgsL_instForallS {PT : PrimTableK} {env : Environment} {Γ : List Expr} {T R : Expr} {as : List Expr}
    (h : TyArgsL PT env Γ T as R) : instForallS T as = R :=
  match h with
  | .nil => instForallS_nil _
  | .cons _ hs => by rw [instForallS_cons_forallE]; exact tyArgsL_instForallS hs

/-- `OblUnfoldL` (β/δ type preservation, in `betaS`): the type of a `defnInfo`-headed spine is the type of its instantiated, β-reduced body. For `TyRKL` this is the `unfold` rule
(`oblUnfoldL_TyRKL`); that the KERNEL typing satisfies it is not stated (no `Prop`-valued kernel judgment in core). -/
def OblUnfoldL (Ty : TyJ) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (c : Name) (ls : List Level) (args : List Expr) (d : DefinitionVal) (τ : Expr),
    env.find? c = some (.defnInfo d) →
    Ty env Γ (betaS (instantiateLevelParamsS d.levelParams ls d.value) args) τ → Ty env Γ (mkAppN (.const c ls) args.toArray) τ

/-- `OblPrimKL`: a spine headed by a non-`defnInfo` constant whose arguments are typed against the declared telescope (type arguments included: they are terms of the telescope's `Sort`s)
has the telescope's result type. -/
def OblPrimKL (Ty : TyJ) : Prop :=
  ∀ (env : Environment) (Γ : List Expr) (c : Name) (ls : List Level) (args : List Expr) (ci : ConstantInfo) (R : Expr),
    env.find? c = some ci → ¬ IsDefn env c →
    TyArgsG Ty env Γ (instantiateLevelParamsS ci.levelParams ls ci.type) args R → Ty env Γ (mkAppN (.const c ls) args.toArray) R

structure KernelRulesKL (Ty : TyJ) : Prop where

  bvar : OblBvarS Ty
  app : OblAppS Ty
  lam : OblLam Ty
  const : OblConst Ty
  lit : OblLit Ty
  letE : OblLetS Ty
  unfold : OblUnfoldL Ty
  prim : OblPrimKL Ty

def TyRKLJ (PT : PrimTableK) : TyJ := fun env => TyRKL PT env

/-- The bundle is satisfiable by `TyRKLJ` (unfold and the strong prim are rules of the judgment). -/
theorem kernelRulesKL_TyRKL (PT : PrimTableK) : KernelRulesKL (TyRKLJ PT) where
  bvar := fun _ _ _ _ h => .bvar h
  app := fun _ _ _ _ _ _ _ _ hf hx => .app hf hx
  lam := fun _ _ _ _ _ _ _ hb => .lam hb
  const := fun _ _ _ _ _ h => .const h
  lit := ⟨fun _ _ _ => .natLit, fun _ _ _ => .strLit⟩
  letE := fun _ _ _ _ _ _ _ _ hv hb => .letE hv hb
  unfold := fun _ _ _ _ _ _ _ hd hb => .unfold hd hb
  prim := fun env Γ c ls args ci R hci hnd hs => by
    -- `TyArgsG (TyRKLJ PT)` is `TyArgsL`
    have : ∀ (T : Expr) (as : List Expr) (R : Expr), TyArgsG (TyRKLJ PT) env Γ T as R → TyArgsL PT env Γ T as R := by
      intro T as R h
      induction h with
      | nil => exact .nil
      | cons ha _ ih => exact .cons ha ih
    exact .prim hci hnd (this _ _ _ hs)

mutual

theorem tyRKL_sub {PT : PrimTableK} {Ty : TyJ} (R : KernelRulesKL Ty) {env : Environment} {Γ : List Expr} {e τ : Expr}
    (h : TyRKL PT env Γ e τ) : Ty env Γ e τ :=
  match h with
  | .natLit => R.lit.1 _ _ _
  | .strLit => R.lit.2 _ _ _
  | .bvar h => R.bvar _ _ _ _ h
  | .const h => R.const _ _ _ _ _ h
  | .app hf hx => R.app _ _ _ _ _ _ _ _ (tyRKL_sub R hf) (tyRKL_sub R hx)
  | .lam hb => R.lam _ _ _ _ _ _ _ (tyRKL_sub R hb)
  | .letE hv hb => R.letE _ _ _ _ _ _ _ _ (tyRKL_sub R hv) (tyRKL_sub R hb)
  | .unfold hd hb => R.unfold _ _ _ _ _ _ _ hd (tyRKL_sub R hb)
  | .prim hci hnd hargs => R.prim _ _ _ _ _ _ _ hci hnd (tyArgsL_sub R hargs)

theorem tyArgsL_sub {PT : PrimTableK} {Ty : TyJ} (R : KernelRulesKL Ty) {env : Environment} {Γ : List Expr} {T : Expr} {as : List Expr} {R' : Expr}
    (h : TyArgsL PT env Γ T as R') : TyArgsG Ty env Γ T as R' :=
  match h with
  | .nil => .nil
  | .cons ha hs => .cons (tyRKL_sub R ha) (tyArgsL_sub R hs)

end

/-- The per-key argument-typing obligation (named; NOT assumed anywhere): for a row-carrying key, every argument list the row accepts is typed against the declared telescope.
It is not a consequence of `ArgsDenL`: a term argument's derivation fixes its label `τ` but nothing forces `τ` to be (syntactically) the telescope's binder type, and a type argument
is only given a denotation (`TDenL`), never a typing. So it is a genuine row-level obligation, like `RowTypedAt`. -/
def RowArgsAtL (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) : Prop :=
  ∀ (ρ : Val) (args : List Expr) (ci : ConstantInfo) (row : TmRow) (as : List Arg) (d : Dyn),
    env.find? c = some ci → PT.tms c ls = some row → ArgsDenL PT env ρ row.kinds args as → row.den as = some d →
    TyArgsL PT env (ρ.map Entry.τ) (instantiateLevelParamsS ci.levelParams ls ci.type) args
      (instForallS (instantiateLevelParamsS ci.levelParams ls ci.type) args)

def OblPrimArgsL (PT : PrimTableK) (env : Environment) : Prop := ∀ (c : Name) (ls : List Level), RowArgsAtL PT env c ls

theorem rowArgsAtL_of_none (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (h : PT.tms c ls = none) : RowArgsAtL PT env c ls := by
  intro ρ args ci row as d _ hrow; rw [h] at hrow; cases hrow

theorem argsdenl_length {PT : PrimTableK} {env : Environment} {ρ : Val} {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenL PT env ρ ks es as) : es.length = ks.length ∧ as.length = ks.length :=
  match h with
  | .nil => ⟨rfl, rfl⟩
  | .ty _ hs => by have := argsdenl_length hs; simp [this.1, this.2]
  | .tm _ hs => by have := argsdenl_length hs; simp [this.1, this.2]

/-- A key whose row takes no arguments has no argument-typing obligation. -/
theorem rowArgsAtL_nullary (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow)
    (hrow : PT.tms c ls = some row) (hk : row.kinds = []) : RowArgsAtL PT env c ls := by
  intro ρ args ci row' as d _ hrow' hargs _
  rw [hrow] at hrow'; cases hrow'
  rw [hk] at hargs
  have : args = [] := List.length_eq_zero_iff.mp (by simpa using (argsdenl_length hargs).1)
  subst this
  rw [instForallS_nil]; exact .nil

/-- Every `CVEKL` derivation is a `TyRKL` derivation at `ρ.map Entry.τ`, given the per-key argument typing of the rows it uses. -/
theorem cvekl_tyRKS {PT : PrimTableK} {env : Environment} (hP : OblPrimArgsL PT env) {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEKL PT env ρ e τ α v) : TyRKL PT env (ρ.map Entry.τ) e τ :=
  match h with
  | .natLit => .natLit
  | .strLit => .strLit
  | .bvar h1 => .bvar (map_getElem?_entry _ _ _ h1)
  | .lam _ _ _ a0 hb => .lam (cvekl_tyRKS hP (hb a0))
  | CVEKL.app _ _ _ hf hx _ => .app (cvekl_tyRKS hP hf) (cvekl_tyRKS hP hx)
  | .letE _ hv hb => .letE (cvekl_tyRKS hP hv) (cvekl_tyRKS hP hb)
  | .unfold hd hb he => he ▸ .unfold hd (cvekl_tyRKS hP hb)
  | .prim hci hrow hnd hargs hd hty he => he ▸ .prim hci hnd (hP _ _ _ _ _ _ _ _ hci hrow hargs hd)

/-- Soundness of the `CVEKL` rules against any `Ty` satisfying the bundle: an implication between named `Prop`s (assumed nowhere). -/
theorem cvekl_sound {PT : PrimTableK} {env : Environment} {Ty : TyJ} (R : KernelRulesKL Ty) (hP : OblPrimArgsL PT env)
    {ρ : Val} {e τ : Expr} {α : Type} {v : α} (h : CVEKL PT env ρ e τ α v) : Ty env (ρ.map Entry.τ) e τ :=
  tyRKL_sub R (cvekl_tyRKS hP h)end Tools.ShippingGen5ConstValueELProof
