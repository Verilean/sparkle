import Tools.ShippingGen5ConstValueES
set_option autoImplicit false
/-! # Proofs about the syntactic carrier `CVEKS` (issue sparkle-ledger-dd4-sound; draft §SoundS)

§1 commutation lemmas for `liftS` / `substS` / `betaS` / `instForallS`; no axiom, no `sorry`. -/
namespace Tools.ShippingGen5ConstValueES
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK

/-- Closes the arithmetic residue of a `bvar` case (a leftover `if` on a sum, or an equation of indices). -/
local macro "bvtac" : tactic => `(tactic| first | omega | (split <;> (try simp) <;> omega))

/-! ## §1 lift / subst / beta lemmas -/

/-- Two lifts: the outer cut lies at or above the inner cut. -/
theorem liftS_liftS_le (e : Expr) : ∀ (a b m n : Nat), a ≤ b → liftS (liftS e a m) (b + m) n = liftS (liftS e b n) a m := by
  induction e with
  | bvar i => intro a b m n h; simp only [liftS]; by_cases h1 : i < a <;> by_cases h2 : i < b <;> simp [liftS, h1, h2] <;> bvtac
  | app f x ihf ihx => intro a b m n h; simp [liftS, ihf a b m n h, ihx a b m n h]
  | lam x A b' bi ihA ihb =>
    intro a b m n h; simp only [liftS]
    rw [show b + m + 1 = (b + 1) + m by omega, ihA a b m n h, ihb (a + 1) (b + 1) m n (by omega)]
  | forallE x A b' bi ihA ihb =>
    intro a b m n h; simp only [liftS]
    rw [show b + m + 1 = (b + 1) + m by omega, ihA a b m n h, ihb (a + 1) (b + 1) m n (by omega)]
  | letE x A v b' nd ihA ihv ihb =>
    intro a b m n h; simp only [liftS]
    rw [show b + m + 1 = (b + 1) + m by omega, ihA a b m n h, ihv a b m n h, ihb (a + 1) (b + 1) m n (by omega)]
  | mdata d e ih => intro a b m n h; simp [liftS, ih a b m n h]
  | proj c i e ih => intro a b m n h; simp [liftS, ih a b m n h]
  | _ => intros; rfl

/-- Two lifts at a cut inside the lifted block: they add up. -/
theorem liftS_liftS_add (e : Expr) : ∀ (a b m n : Nat), a ≤ b → b ≤ a + m → liftS (liftS e a m) b n = liftS e a (m + n) := by
  induction e with
  | bvar i => intro a b m n h1 h2; simp only [liftS]; by_cases h1 : i < a <;> by_cases h2 : i < b <;> simp [liftS, h1, h2] <;> bvtac
  | app f x ihf ihx => intro a b m n h1 h2; simp [liftS, ihf a b m n h1 h2, ihx a b m n h1 h2]
  | lam x A b' bi ihA ihb => intro a b m n h1 h2; simp [liftS, ihA a b m n h1 h2, ihb (a + 1) (b + 1) m n (by omega) (by omega)]
  | forallE x A b' bi ihA ihb => intro a b m n h1 h2; simp [liftS, ihA a b m n h1 h2, ihb (a + 1) (b + 1) m n (by omega) (by omega)]
  | letE x A v b' nd ihA ihv ihb =>
    intro a b m n h1 h2; simp [liftS, ihA a b m n h1 h2, ihv a b m n h1 h2, ihb (a + 1) (b + 1) m n (by omega) (by omega)]
  | mdata d e ih => intro a b m n h1 h2; simp [liftS, ih a b m n h1 h2]
  | proj c i e ih => intro a b m n h1 h2; simp [liftS, ih a b m n h1 h2]
  | _ => intros; rfl


/-- `liftS` through a cut that is above the substituted index: lift and substitute commute (with the argument lifted to the depth). -/
theorem liftS_substS (B : Expr) : ∀ (k s n : Nat) (x : Expr), k ≤ s →
    liftS (substS B k x) s n = substS (liftS B (s + 1) n) k (liftS x (s - k) n) := by
  induction B with
  | bvar i =>
    intro k s n x h
    by_cases h1 : i < k
    · have h3 : i < s := by omega
      have h5 : i < s + 1 := by omega
      simp [substS, liftS, h1, h3, h5]
    · by_cases h2 : i = k
      · subst h2
        have := liftS_liftS_le x 0 (s - i) i n (by omega)
        simp only [substS, liftS, Nat.lt_irrefl, if_false, if_true, show i < s + 1 by omega]
        rw [show s - i + i = s by omega] at this
        simpa using this
      · have h3 : k < i := by omega
        by_cases h4 : i - 1 < s
        · have h5 : i < s + 1 := by omega
          simp [substS, liftS, h1, h2, h4, h5]
        · have h5 : ¬ i < s + 1 := by omega
          have h6 : ¬ i + n < k := by omega
          have h7 : ¬ i + n = k := by omega
          simp [substS, liftS, h1, h2, h4, h5, h6, h7]
          omega
  | app f a ihf iha => intro k s n x h; simp [substS, liftS, ihf k s n x h, iha k s n x h]
  | lam x A b bi ihA ihb =>
    intro k s n y h
    simp only [substS, liftS]
    rw [ihA k s n y h, ihb (k + 1) (s + 1) n y (by omega), show s + 1 - (k + 1) = s - k by omega]
  | forallE x A b bi ihA ihb =>
    intro k s n y h
    simp only [substS, liftS]
    rw [ihA k s n y h, ihb (k + 1) (s + 1) n y (by omega), show s + 1 - (k + 1) = s - k by omega]
  | letE x A v b nd ihA ihv ihb =>
    intro k s n y h
    simp only [substS, liftS]
    rw [ihA k s n y h, ihv k s n y h, ihb (k + 1) (s + 1) n y (by omega), show s + 1 - (k + 1) = s - k by omega]
  | mdata d e ih => intro k s n x h; simp [substS, liftS, ih k s n x h]
  | proj c i e ih => intro k s n x h; simp [substS, liftS, ih k s n x h]
  | _ => intros; rfl

theorem liftS_foldl_app (as : List Expr) : ∀ (f : Expr) (s n : Nat),
    liftS (as.foldl Expr.app f) s n = (as.map (fun a => liftS a s n)).foldl Expr.app (liftS f s n) := by
  induction as with
  | nil => intros; rfl
  | cons a as ih => intro f s n; simp only [List.foldl, List.map, ih, liftS]

theorem liftS_mkAppN (f : Expr) (as : List Expr) (s n : Nat) :
    liftS (mkAppN f as.toArray) s n = mkAppN (liftS f s n) (as.map (fun a => liftS a s n)).toArray := by
  rw [mkAppN_toList, mkAppN_toList, liftS_foldl_app]

theorem liftS_betaS (as : List Expr) : ∀ (f : Expr) (s n : Nat),
    liftS (betaS f as) s n = betaS (liftS f s n) (as.map (fun a => liftS a s n)) := by
  induction as with
  | nil => intro f s n; simp [betaS_nil]
  | cons a as ih =>
    intro f s n
    cases f with
    | lam x A b bi =>
      simp only [betaS, liftS, List.map]
      rw [ih, liftS_substS b 0 s n a (Nat.zero_le _)]
      simp
    | bvar j => by_cases h : j < s <;> simp [betaS, liftS, h, liftS_foldl_app]
    | _ => simp [betaS, liftS, liftS_foldl_app]

theorem liftS_instForallS (as : List Expr) : ∀ (T : Expr) (s n : Nat),
    liftS (instForallS T as) s n = instForallS (liftS T s n) (as.map (fun a => liftS a s n)) := by
  induction as with
  | nil => intro T s n; simp [instForallS_nil]
  | cons a as ih =>
    intro T s n
    cases T with
    | forallE x A b bi =>
      simp only [instForallS, liftS, List.map]
      rw [ih, liftS_substS b 0 s n a (Nat.zero_le _)]
      simp
    | bvar j => by_cases h : j < s <;> simp [instForallS, liftS, h]
    | _ => simp [instForallS, liftS]

/-- `liftS` keeps the head constant of a spine. -/
theorem getAppFn_liftS (f : Expr) (s n : Nat) (c : Name) (ls : List Level) :
    (liftS f s n).getAppFn = .const c ls ↔ f.getAppFn = .const c ls := by
  induction f with
  | app g a ihg iha => simpa [liftS, Expr.getAppFn] using ihg
  | bvar i => by_cases h : i < s <;> simp [liftS, h, Expr.getAppFn]
  | _ => simp [liftS, Expr.getAppFn]


/-! ## §2 Weakening of the syntactic carrier

`InsV E s ρ ρ'`: `ρ'` is `ρ` with the entry `E` inserted at position `s`; the entries below `s` carry their types lifted (they live under the new binder). -/

inductive InsV (E : Entry) : Nat → Val → Val → Prop
  | here (ρ : Val) : InsV E 0 ρ (E :: ρ)
  | there {s : Nat} {ρ ρ' : Val} (en : Entry) : InsV E s ρ ρ' → InsV E (s + 1) (en :: ρ) (⟨liftS en.τ s 1, en.d⟩ :: ρ')

theorem insV_get {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ') :
    ∀ (i : Nat) (en : Entry), ρ[i]? = some en →
      (i < s ∧ ρ'[i]? = some ⟨liftS en.τ (s - i - 1) 1, en.d⟩) ∨ (s ≤ i ∧ ρ'[i + 1]? = some en) := by
  induction hI with
  | here ρ => intro i en h; right; simpa using h
  | there en0 _ ih =>
    intro i en h
    cases i with
    | zero =>
      simp at h; subst h; left; simp
    | succ j =>
      simp at h
      rcases ih j en h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; refine ⟨by omega, ?_⟩
        simp only [List.getElem?_cons_succ]; rw [h2]; congr 3; omega
      · right; exact ⟨by omega, by simpa using h2⟩

/-- Label of a `bvar` below the insertion point. -/
theorem lbl_lt (e : Expr) (i s : Nat) (h : i < s) :
    liftS (liftS e (s - i - 1) 1) 0 (i + 1) = liftS (liftS e 0 (i + 1)) s 1 := by
  have := liftS_liftS_le e 0 (s - i - 1) (i + 1) 1 (Nat.zero_le _)
  rw [show s - i - 1 + (i + 1) = s by omega] at this
  exact this.symm

/-- Label of a `bvar` at or above the insertion point. -/
theorem lbl_ge (e : Expr) (i s : Nat) (h : s ≤ i) :
    liftS e 0 (i + 1 + 1) = liftS (liftS e 0 (i + 1)) s 1 := by
  rw [liftS_liftS_add e 0 s (i + 1) 1 (Nat.zero_le _) (by omega)]

/-- Closedness of the environment's instantiated declarations (a NAMED hypothesis, never assumed globally): `instantiateLevelParams` is an `Expr` API
function, and that it keeps a closed declaration closed is a bridge, not proved here. -/
def EnvClosedS (env : Environment) : Prop :=
  (∀ (c : Name) (ls : List Level) (ci : ConstantInfo), env.find? c = some ci → lbr (ci.type.instantiateLevelParams ci.levelParams ls) = 0) ∧
  (∀ (c : Name) (ls : List Level) (d : DefinitionVal), env.find? c = some (.defnInfo d) → lbr (d.value.instantiateLevelParams d.levelParams ls) = 0)

mutual

theorem tdens_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {τ : Expr} {T : Type} (h : TDenS PT env ρ τ T) : TDenS PT env ρ' (liftS τ s 1) T :=
  match h with
  | .pi hA TB hB =>
    .pi (tdens_wk hcl hI hA) TB fun a => tdens_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hB a)
  | .tcon hrow hnd hargs hT he =>
    .tcon hrow hnd (argsdens_wk hcl hI hargs) hT (by rw [he, liftS_mkAppN]; rfl)
  | .tunfold hd hb he => by
    have hb' := tdens_wk hcl hI hb
    rw [liftS_betaS, liftS_closed _ (hcl.2 _ _ _ hd)] at hb'
    exact .tunfold hd hb' (by rw [he, liftS_mkAppN]; rfl)

theorem argsdens_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {ks : List Bool} {es : List Expr} {as : List Arg} (h : ArgsDenS PT env ρ ks es as) :
    ArgsDenS PT env ρ' ks (es.map (fun a => liftS a s 1)) as :=
  match h with
  | .nil => .nil
  | .ty hT hs => .ty (tdens_wk hcl hI hT) (argsdens_wk hcl hI hs)
  | .tm hv hs => .tm (cveks_wk hcl hI hv) (argsdens_wk hcl hI hs)

theorem cveks_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {E : Entry} {s : Nat} {ρ ρ' : Val} (hI : InsV E s ρ ρ')
    {e τ : Expr} {α : Type} {v : α} (h : CVEKS PT env ρ e τ α v) :
    CVEKS PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
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
    .lam (tdens_wk hcl hI hA) TB f a0 fun a => cveks_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hb a)
  | CVEKS.app TB hA hB hf hx hnh => by
    rw [liftS_substS _ 0 s 1 _ (Nat.zero_le _)]
    refine CVEKS.app TB (tdens_wk hcl hI hA) (fun a => tdens_wk hcl (.there ⟨_, ⟨_, a⟩⟩ hI) (hB a)) (cveks_wk hcl hI hf) (cveks_wk hcl hI hx) ?_
    rintro ⟨c, ls, hc⟩
    exact hnh ⟨c, ls, (getAppFn_liftS _ _ _ _ _).1 hc⟩
  | .letE hA hv hb => by
    rw [liftS_substS _ 0 s 1 _ (Nat.zero_le _)]
    exact .letE (tdens_wk hcl hI hA) (cveks_wk hcl hI hv) (cveks_wk hcl (.there ⟨_, ⟨_, _⟩⟩ hI) hb)
  | .unfold hd hb he => by
    have hb' := cveks_wk hcl hI hb
    rw [liftS_betaS, liftS_closed _ (hcl.2 _ _ _ hd)] at hb'
    exact .unfold hd hb' (by rw [he, liftS_mkAppN]; rfl)
  | .prim hci hrow hnd hargs hd hty he => by
    have hty' := tdens_wk hcl hI hty
    rw [liftS_instForallS, liftS_closed _ (hcl.1 _ _ _ hci)] at hty' ⊢
    exact .prim hci hrow hnd (argsdens_wk hcl hI hargs) hd hty' (by rw [he, liftS_mkAppN]; rfl)

end

end Tools.ShippingGen5ConstValueES
