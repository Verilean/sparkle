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


/-! ## §3 Substitution lemmas -/

/-- Substituting inside a lifted block removes one lifted position. -/
theorem substS_liftS_in (B : Expr) : ∀ (a n c : Nat) (x : Expr), a ≤ c → c < a + n → substS (liftS B a n) c x = liftS B a (n - 1) := by
  induction B with
  | bvar i =>
    intro a n c x h1 h2
    by_cases h : i < a
    · have h3 : i < c := by omega
      simp [liftS, substS, h, h3]
    · have h3 : ¬ i + n < c := by omega
      have h4 : ¬ i + n = c := by omega
      simp [liftS, substS, h, h3, h4]; omega
  | app f a ihf iha => intro a' n c x h1 h2; simp [liftS, substS, ihf a' n c x h1 h2, iha a' n c x h1 h2]
  | lam y A b bi ihA ihb => intro a n c x h1 h2; simp [liftS, substS, ihA a n c x h1 h2, ihb (a + 1) n (c + 1) x (by omega) (by omega)]
  | forallE y A b bi ihA ihb => intro a n c x h1 h2; simp [liftS, substS, ihA a n c x h1 h2, ihb (a + 1) n (c + 1) x (by omega) (by omega)]
  | letE y A v b nd ihA ihv ihb =>
    intro a n c x h1 h2; simp [liftS, substS, ihA a n c x h1 h2, ihv a n c x h1 h2, ihb (a + 1) n (c + 1) x (by omega) (by omega)]
  | mdata d e ih => intro a n c x h1 h2; simp [liftS, substS, ih a n c x h1 h2]
  | proj c' i e ih => intro a n c x h1 h2; simp [liftS, substS, ih a n c x h1 h2]
  | _ => intros; rfl

/-- Substituting above a lifted block: substitute first (at the shifted index), then lift. -/
theorem substS_liftS_ge (B : Expr) : ∀ (a m k : Nat) (x : Expr), a + m ≤ k →
    substS (liftS B a m) k x = liftS (substS B (k - m) x) a m := by
  induction B with
  | bvar i =>
    intro a m k x h
    by_cases h1 : i < a
    · have h2 : i < k - m := by omega
      have h3 : i < k := by omega
      simp [liftS, substS, h1, h2, h3]
    · by_cases h2 : i + m < k
      · have h3 : i < k - m := by omega
        simp [liftS, substS, h1, h2, h3]
      · by_cases h3 : i + m = k
        · have h4 : i = k - m := by omega
          have h5 : ¬ i < k - m := by omega
          subst h4
          have h6 := liftS_liftS_add x 0 a (k - m) m (Nat.zero_le _) (by omega)
          simp [liftS, substS, h1, h3]
          rw [h6]; congr 1; omega
        · have h4 : ¬ i < k - m := by omega
          have h5 : ¬ i = k - m := by omega
          have h6 : ¬ i - 1 < a := by omega
          simp [liftS, substS, h1, h2, h3, h4, h5, h6]
          omega
  | app f a ihf iha => intro a' m k x h; simp [liftS, substS, ihf a' m k x h, iha a' m k x h]
  | lam y A b bi ihA ihb =>
    intro a m k x h
    simp only [liftS, substS]
    rw [ihA a m k x h, ihb (a + 1) m (k + 1) x (by omega), show k + 1 - m = (k - m) + 1 by omega]
  | forallE y A b bi ihA ihb =>
    intro a m k x h
    simp only [liftS, substS]
    rw [ihA a m k x h, ihb (a + 1) m (k + 1) x (by omega), show k + 1 - m = (k - m) + 1 by omega]
  | letE y A v b nd ihA ihv ihb =>
    intro a m k x h
    simp only [liftS, substS]
    rw [ihA a m k x h, ihv a m k x h, ihb (a + 1) m (k + 1) x (by omega), show k + 1 - m = (k - m) + 1 by omega]
  | mdata d e ih => intro a m k x h; simp [liftS, substS, ih a m k x h]
  | proj c' i e ih => intro a m k x h; simp [liftS, substS, ih a m k x h]
  | _ => intros; rfl


/-- Two substitutions commute (the outer one acts on the substituted argument too). -/
theorem substS_substS (B : Expr) : ∀ (m k : Nat) (y x : Expr), m ≤ k →
    substS (substS B m y) k x = substS (substS B (k + 1) x) m (substS y (k - m) x) := by
  induction B with
  | bvar j =>
    intro m k y x h
    by_cases h1 : j < m
    · have h2 : j < k + 1 := by omega
      have h3 : j < k := by omega
      simp [substS, h1, h2, h3]
    · by_cases h2 : j = m
      · subst h2
        have h3 : j < k + 1 := by omega
        simp only [substS, Nat.lt_irrefl, if_false, if_true, h3]
        rw [substS_liftS_ge y 0 j k x (by omega)]
      · by_cases h3 : j < k + 1
        · have h4 : j - 1 < k := by omega
          simp [substS, h1, h2, h3, h4]
        · by_cases h4 : j = k + 1
          · subst h4
            have h5 : ¬ k + 1 < m := by omega
            have h6 : ¬ k + 1 = m := by omega
            have h7 : ¬ k + 1 < k + 1 := by omega
            have h8 : ¬ k < m := by omega
            simp only [substS, h5, h6, h7, h8, if_true, if_false, Nat.add_sub_cancel, Nat.lt_irrefl]
            rw [substS_liftS_in x 0 (k + 1) m (substS y (k - m) x) (Nat.zero_le _) (by omega)]
            simp
          · have h5 : ¬ j - 1 < k := by omega
            have h6 : ¬ j - 1 = k := by omega
            have h7 : ¬ j < k + 1 := h3
            have h8 : ¬ j = k + 1 := h4
            have h9 : ¬ j - 1 < m := by omega
            have h10 : ¬ j - 1 = m := by omega
            simp [substS, h1, h2, h5, h6, h7, h8, h9, h10]
  | app f a ihf iha => intro m k y x h; simp [substS, ihf m k y x h, iha m k y x h]
  | lam n A b bi ihA ihb =>
    intro m k y x h
    simp only [substS]
    rw [ihA m k y x h, ihb (m + 1) (k + 1) y x (by omega), show k + 1 - (m + 1) = k - m by omega]
  | forallE n A b bi ihA ihb =>
    intro m k y x h
    simp only [substS]
    rw [ihA m k y x h, ihb (m + 1) (k + 1) y x (by omega), show k + 1 - (m + 1) = k - m by omega]
  | letE n A v b nd ihA ihv ihb =>
    intro m k y x h
    simp only [substS]
    rw [ihA m k y x h, ihv m k y x h, ihb (m + 1) (k + 1) y x (by omega), show k + 1 - (m + 1) = k - m by omega]
  | mdata d e ih => intro m k y x h; simp [substS, ih m k y x h]
  | proj c i e ih => intro m k y x h; simp [substS, ih m k y x h]
  | _ => intros; rfl


/-- The substituted argument is stable under the carrier's two syntactic tests: it is not a `lam` (`betaS` would fire on it), not a `forallE` (`instForallS` would fire on it)
and not const-headed (the `app` rule's exclusivity `hnh`). -/
def SafeArg (x : Expr) : Prop := x.isLambda = false ∧ x.isForall = false ∧ ¬ ∃ (c : Name) (ls : List Level), x.getAppFn = .const c ls

theorem liftS_isLambda (e : Expr) (s n : Nat) : (liftS e s n).isLambda = e.isLambda := by
  cases e with
  | bvar i => by_cases h : i < s <;> simp [liftS, h, Expr.isLambda]
  | _ => simp [liftS, Expr.isLambda]

theorem liftS_isForall (e : Expr) (s n : Nat) : (liftS e s n).isForall = e.isForall := by
  cases e with
  | bvar i => by_cases h : i < s <;> simp [liftS, h, Expr.isForall]
  | _ => simp [liftS, Expr.isForall]

theorem substS_isLambda (f : Expr) (k : Nat) {x : Expr} (hx : SafeArg x) (hf : f.isLambda = false) : (substS f k x).isLambda = false := by
  cases f with
  | bvar j =>
    by_cases h1 : j < k
    · simp [substS, h1, Expr.isLambda]
    · by_cases h2 : j = k
      · subst h2; simp only [substS, Nat.lt_irrefl, if_false, if_true, liftS_isLambda]; exact hx.1
      · simp [substS, h1, h2, Expr.isLambda]
  | _ => simp [substS, Expr.isLambda] at hf ⊢

theorem substS_isForall (f : Expr) (k : Nat) {x : Expr} (hx : SafeArg x) (hf : f.isForall = false) : (substS f k x).isForall = false := by
  cases f with
  | bvar j =>
    by_cases h1 : j < k
    · simp [substS, h1, Expr.isForall]
    · by_cases h2 : j = k
      · subst h2; simp only [substS, Nat.lt_irrefl, if_false, if_true, liftS_isForall]; exact hx.2.1
      · simp [substS, h1, h2, Expr.isForall]
  | _ => simp [substS, Expr.isForall] at hf ⊢

theorem getAppFn_substS (f : Expr) (k : Nat) {x : Expr} (hx : SafeArg x) (c : Name) (ls : List Level) :
    (substS f k x).getAppFn = .const c ls ↔ f.getAppFn = .const c ls := by
  induction f with
  | app g a ihg iha => simpa [substS, Expr.getAppFn] using ihg
  | bvar j =>
    by_cases h1 : j < k
    · simp [substS, h1, Expr.getAppFn]
    · by_cases h2 : j = k
      · subst h2
        simp only [substS, Nat.lt_irrefl, if_false, if_true, getAppFn_liftS, Expr.getAppFn]
        constructor
        · intro h; exact absurd ⟨c, ls, h⟩ hx.2.2
        · intro h; cases h
      · simp [substS, h1, h2, Expr.getAppFn]
  | _ => simp [substS, Expr.getAppFn]

theorem substS_foldl_app (as : List Expr) : ∀ (f : Expr) (k : Nat) (x : Expr),
    substS (as.foldl Expr.app f) k x = (as.map (fun a => substS a k x)).foldl Expr.app (substS f k x) := by
  induction as with
  | nil => intros; rfl
  | cons a as ih => intro f k x; simp only [List.foldl, List.map, ih, substS]

theorem substS_mkAppN (f : Expr) (as : List Expr) (k : Nat) (x : Expr) :
    substS (mkAppN f as.toArray) k x = mkAppN (substS f k x) (as.map (fun a => substS a k x)).toArray := by
  rw [mkAppN_toList, mkAppN_toList, substS_foldl_app]

theorem betaS_of_not_lam (f : Expr) (hf : f.isLambda = false) (as : List Expr) : betaS f as = as.foldl Expr.app f := by
  cases as with
  | nil => simp [betaS_nil]
  | cons a as => cases f <;> simp [betaS, Expr.isLambda] at hf ⊢

theorem substS_betaS {x : Expr} (hx : SafeArg x) (as : List Expr) : ∀ (f : Expr) (k : Nat),
    substS (betaS f as) k x = betaS (substS f k x) (as.map (fun a => substS a k x)) := by
  induction as with
  | nil => intro f k; simp [betaS_nil]
  | cons a as ih =>
    intro f k
    by_cases hl : f.isLambda = true
    · cases f <;> simp [Expr.isLambda] at hl
      rename_i y A b bi
      simp only [betaS, substS, List.map]
      rw [ih, substS_substS b 0 k a x (Nat.zero_le _)]
      simp
    · have hl' : f.isLambda = false := by simpa using hl
      have h2 := substS_isLambda f k hx hl'
      rw [betaS_of_not_lam f hl', betaS_of_not_lam _ h2, List.map_cons, substS_foldl_app]
      simp

theorem substS_instForallS {x : Expr} (hx : SafeArg x) (as : List Expr) : ∀ (T : Expr) (k : Nat),
    substS (instForallS T as) k x = instForallS (substS T k x) (as.map (fun a => substS a k x)) := by
  induction as with
  | nil => intro T k; simp [instForallS_nil]
  | cons a as ih =>
    intro T k
    by_cases hl : T.isForall = true
    · cases T <;> simp [Expr.isForall] at hl
      simp only [instForallS, substS, List.map]
      rw [ih, substS_substS _ 0 k a x (Nat.zero_le _)]
      simp
    · have hl' : T.isForall = false := by simpa using hl
      have h2 := substS_isForall T k hx hl'
      have e1 : instForallS T (a :: as) = T := by cases T <;> simp [Expr.isForall] at hl' ⊢ <;> simp [instForallS]
      have e2 : instForallS (substS T k x) (substS a k x :: as.map (fun a => substS a k x)) = substS T k x := by
        cases h : substS T k x <;> simp [Expr.isForall, h] at h2 ⊢ <;> simp [instForallS]
      rw [e1, List.map_cons, e2]


/-! ## §4 Substitution of one entry by a derivable argument (restricted to `SafeArg`)

`SubV PT env A TA av x k ρ ρ'`: `ρ` has the entry `⟨A, ⟨TA, av⟩⟩` at position `k`; `ρ'` is `ρ` without it, the entries below it carrying their types
substituted; `x` is derivable in the base valuation with type `A` and value `av`. -/

inductive SubV (PT : PrimTableK) (env : Environment) (A : Expr) (TA : Type) (av : TA) (x : Expr) : Nat → Val → Val → Prop
  | here (ρ0 : Val) (hx : CVEKS PT env ρ0 x A TA av) : SubV PT env A TA av x 0 (⟨A, ⟨TA, av⟩⟩ :: ρ0) ρ0
  | there {k : Nat} {ρ ρ' : Val} (en : Entry) : SubV PT env A TA av x k ρ ρ' → SubV PT env A TA av x (k + 1) (en :: ρ) (⟨substS en.τ k x, en.d⟩ :: ρ')

theorem subv_get {PT : PrimTableK} {env : Environment} {A : Expr} {TA : Type} {av : TA} {x : Expr} {k : Nat} {ρ ρ' : Val}
    (hS : SubV PT env A TA av x k ρ ρ') :
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

/-- Under `SubV` the argument is derivable in the lifted block: weakening of `hx` by the `k` entries below the removed one. -/
theorem subv_wk {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {A : Expr} {TA : Type} {av : TA} {x : Expr} {k : Nat} {ρ ρ' : Val}
    (hS : SubV PT env A TA av x k ρ ρ') : CVEKS PT env ρ' (liftS x 0 k) (liftS A 0 k) TA av := by
  induction hS with
  | here ρ0 hx => simpa [liftS_zero] using hx
  | @there k0 ρ0 ρ0' en _ ih =>
    have := cveks_wk hcl (InsV.here ρ0' (E := ⟨substS en.τ k0 x, en.d⟩) ) ih
    rwa [liftS_liftS_add _ 0 0 _ 1 (Nat.le_refl _) (by omega), liftS_liftS_add _ 0 0 _ 1 (Nat.le_refl _) (by omega)] at this

theorem lbr_le_of_zero {e : Expr} (h : lbr e = 0) (k : Nat) : lbr e ≤ k := by omega

mutual

theorem tdens_subst {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {A : Expr} {TA : Type} {av : TA} {x : Expr} (hx : SafeArg x)
    {k : Nat} {ρ ρ' : Val} (hS : SubV PT env A TA av x k ρ ρ') {τ : Expr} {T : Type} (h : TDenS PT env ρ τ T) :
    TDenS PT env ρ' (substS τ k x) T :=
  match h with
  | .pi hA TB hB =>
    .pi (tdens_subst hcl hx hS hA) TB fun a => tdens_subst hcl hx (.there ⟨_, ⟨_, a⟩⟩ hS) (hB a)
  | .tcon hrow hnd hargs hT he =>
    .tcon hrow hnd (argsdens_subst hcl hx hS hargs) hT (by rw [he, substS_mkAppN]; rfl)
  | .tunfold hd hb he => by
    have hb' := tdens_subst hcl hx hS hb
    rw [substS_betaS hx, substS_of_lbr_le _ k x (lbr_le_of_zero (hcl.2 _ _ _ hd) k)] at hb'
    exact .tunfold hd hb' (by rw [he, substS_mkAppN]; rfl)

theorem argsdens_subst {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {A : Expr} {TA : Type} {av : TA} {x : Expr} (hx : SafeArg x)
    {k : Nat} {ρ ρ' : Val} (hS : SubV PT env A TA av x k ρ ρ') {ks : List Bool} {es : List Expr} {as : List Arg}
    (h : ArgsDenS PT env ρ ks es as) : ArgsDenS PT env ρ' ks (es.map (fun a => substS a k x)) as :=
  match h with
  | .nil => .nil
  | .ty hT hs => .ty (tdens_subst hcl hx hS hT) (argsdens_subst hcl hx hS hs)
  | .tm hv hs => .tm (cveks_subst hcl hx hS hv) (argsdens_subst hcl hx hS hs)

theorem cveks_subst {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {A : Expr} {TA : Type} {av : TA} {x : Expr} (hx : SafeArg x)
    {k : Nat} {ρ ρ' : Val} (hS : SubV PT env A TA av x k ρ ρ') {e τ : Expr} {α : Type} {v : α} (h : CVEKS PT env ρ e τ α v) :
    CVEKS PT env ρ' (substS e k x) (substS τ k x) α v :=
  match h with
  | .natLit => .natLit
  | .strLit => .strLit
  | .bvar (i := i) (en := en) h1 => by
    rcases subv_get hS i en h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [substS_liftS_ge en.τ 0 (i + 1) k x (by omega), show k - (i + 1) = k - i - 1 by omega]
      simp only [substS, h2, if_true]
      exact .bvar h3
    · subst h2; subst h3
      rw [substS_liftS_in A 0 (i + 1) i x (Nat.zero_le _) (by omega)]
      simp only [substS, Nat.lt_irrefl, if_false, if_true, Nat.add_sub_cancel]
      exact subv_wk hcl hS
    · rw [substS_liftS_in en.τ 0 (i + 1) k x (Nat.zero_le _) (by omega)]
      have h4 : ¬ i < k := by omega
      have h5 : ¬ i = k := by omega
      simp only [substS, h4, h5, if_false, Nat.add_sub_cancel]
      have := CVEKS.bvar (PT := PT) (env := env) h3
      rwa [show i - 1 + 1 = i by omega] at this
  | .lam hA TB f a0 hb =>
    .lam (tdens_subst hcl hx hS hA) TB f a0 fun a => cveks_subst hcl hx (.there ⟨_, ⟨_, a⟩⟩ hS) (hb a)
  | CVEKS.app TB hA hB hf hx' hnh => by
    rw [substS_substS _ 0 k _ x (Nat.zero_le _), Nat.sub_zero]
    refine CVEKS.app TB (tdens_subst hcl hx hS hA) (fun a => tdens_subst hcl hx (.there ⟨_, ⟨_, a⟩⟩ hS) (hB a))
      (cveks_subst hcl hx hS hf) (cveks_subst hcl hx hS hx') ?_
    rintro ⟨c, ls, hc⟩
    exact hnh ⟨c, ls, (getAppFn_substS _ k hx c ls).1 hc⟩
  | .letE hA hv hb => by
    rw [substS_substS _ 0 k _ x (Nat.zero_le _), Nat.sub_zero]
    exact .letE (tdens_subst hcl hx hS hA) (cveks_subst hcl hx hS hv) (cveks_subst hcl hx (.there ⟨_, ⟨_, _⟩⟩ hS) hb)
  | .unfold hd hb he => by
    have hb' := cveks_subst hcl hx hS hb
    rw [substS_betaS hx, substS_of_lbr_le _ k x (lbr_le_of_zero (hcl.2 _ _ _ hd) k)] at hb'
    exact .unfold hd hb' (by rw [he, substS_mkAppN]; rfl)
  | .prim hci hrow hnd hargs hd hty he => by
    have hty' := tdens_subst hcl hx hS hty
    rw [substS_instForallS hx, substS_of_lbr_le _ k x (lbr_le_of_zero (hcl.1 _ _ _ hci) k)] at hty' ⊢
    exact .prim hci hrow hnd (argsdens_subst hcl hx hS hargs) hd hty' (by rw [he, substS_mkAppN]; rfl)

end


/-! ## §5 P1: `OblDenLits` / `OblDenBvar` / `OblDenSubst`, and `OblDenTyped` for the syntactic carrier -/

/-- Valuation well-formedness: each entry's (lifted) type denotes the entry's semantic type, in the valuation itself. Empty valuations are well-formed. -/
def WfValS (PT : PrimTableK) (env : Environment) (ρ : Val) : Prop :=
  ∀ (i : Nat) (en : Entry), ρ[i]? = some en → TDenS PT env ρ (liftS en.τ 0 (i + 1)) en.d.ty

theorem wfValS_nil (PT : PrimTableK) (env : Environment) : WfValS PT env [] := by
  intro i en h; simp at h

/-- Extension by a binder whose type denotes `TA` keeps the valuation well-formed (uses weakening). -/
theorem wfValS_cons {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {ρ : Val} (hρ : WfValS PT env ρ)
    {A : Expr} {TA : Type} (hA : TDenS PT env ρ A TA) (a : TA) : WfValS PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) := by
  intro i en h
  cases i with
  | zero =>
    simp at h; subst h
    exact tdens_wk hcl (InsV.here ρ (E := ⟨A, ⟨TA, a⟩⟩)) hA
  | succ j =>
    simp at h
    have := tdens_wk hcl (InsV.here ρ (E := ⟨A, ⟨TA, a⟩⟩)) (hρ j en h)
    rwa [liftS_liftS_add _ 0 0 (j + 1) 1 (Nat.le_refl _) (by omega)] at this

/-- `OblDenBvar` (reviewer P1): for a well-formed valuation the `bvar` label denotes the entry's type. (Not for arbitrary valuations: an entry with a junk `τ` has none.) -/
def OblDenBvarS (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (i : Nat) (en : Entry), WfValS PT env ρ → ρ[i]? = some en → TDenS PT env ρ (liftS en.τ 0 (i + 1)) en.d.ty

theorem oblDenBvarS (PT : PrimTableK) (env : Environment) : OblDenBvarS PT env := fun _ _ _ hρ h => hρ _ _ h

/-- `OblDenLits`, as a lemma about rows (a condition on `PT`, so it is the premises): a nullary type row whose value is `T` denotes the constant. -/
theorem tden_const_nullary {PT : PrimTableK} {env : Environment} {c : Name} {ls : List Level} {row : TyRow} {T : Type}
    (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c) (hk : row.kinds = []) (hT : row.den [] = some T) (ρ : Val) :
    TDenS PT env ρ (.const c ls) T :=
  .tcon (args := []) (as := []) hrow hnd (by rw [hk]; exact .nil) hT rfl

theorem oblDenLits_of_rows {PT : PrimTableK} {env : Environment} {rn rs : TyRow}
    (hn : PT.tys `Nat [] = some rn) (hnnd : ¬ IsDefn env `Nat) (hnk : rn.kinds = []) (hnT : rn.den [] = some Nat)
    (hs : PT.tys `String [] = some rs) (hsnd : ¬ IsDefn env `String) (hsk : rs.kinds = []) (hsT : rs.den [] = some String) :
    (∀ ρ : Val, TDenS PT env ρ (.const `Nat []) Nat) ∧ (∀ ρ : Val, TDenS PT env ρ (.const `String []) String) :=
  ⟨tden_const_nullary hn hnnd hnk hnT, tden_const_nullary hs hsnd hsk hsT⟩

/-- `OblDenSubst`, general form (all `x`): NOT proved for the carrier. The restricted form for `SafeArg x` is `oblDenSubstS_safe`. -/
def OblDenSubstS (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (A B x : Expr) (TA : Type) (T : Type) (av : TA),
    TDenS PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T → CVEKS PT env ρ x A TA av → TDenS PT env ρ (substS B 0 x) T

/-- `OblDenSubst`, proved for an argument that is not a `lam`, not a `forallE` and not const-headed (`SafeArg`). -/
theorem oblDenSubstS_safe {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env) {ρ : Val} {A B x : Expr} {TA T : Type} {av : TA}
    (hx : SafeArg x) (hB : TDenS PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T) (hv : CVEKS PT env ρ x A TA av) : TDenS PT env ρ (substS B 0 x) T :=
  tdens_subst hcl hx (SubV.here ρ hv) hB

/-- `OblDenTyped` for the syntactic carrier: for every well-formed valuation, a derivation's syntactic type denotes its semantic type. -/
def OblDenTypedS (PT : PrimTableK) (env : Environment) : Prop :=
  ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α), WfValS PT env ρ → CVEKS PT env ρ e τ α v → TDenS PT env ρ τ α

/-- All eight rules closed. The premises are the named, unresolved items: the two literal rows (`OblDenLits`, a condition on `PT`), `EnvClosedS` (a bridge on `instantiateLevelParams`),
and `OblDenSubstS` for `app` / `letE` (proved only for `SafeArg` arguments, `oblDenSubstS_safe`). `bvar` uses well-formedness; `lam` / `prim` / `unfold` need nothing else. -/
theorem denTypedS_aux {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env)
    (hN : ∀ ρ : Val, TDenS PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenS PT env ρ (.const `String []) String)
    (hsub : OblDenSubstS PT env) {ρ : Val} {e τ : Expr} {α : Type} {v : α} (hρ : WfValS PT env ρ) (h : CVEKS PT env ρ e τ α v) :
    TDenS PT env ρ τ α :=
  match h with
  | .natLit => hN ρ
  | .strLit => hS ρ
  | .bvar h1 => hρ _ _ h1
  | .lam hA TB f a0 hb => .pi hA TB fun a => denTypedS_aux hcl hN hS hsub (wfValS_cons hcl hρ hA a) (hb a)
  | CVEKS.app (av := av) TB hA hB hf hx hnh => hsub _ _ _ _ _ _ _ (hB av) hx
  | .letE (av := av) hA hv hb => hsub _ _ _ _ _ _ _ (denTypedS_aux hcl hN hS hsub (wfValS_cons hcl hρ hA av) hb) hv
  | .unfold hd hb he => denTypedS_aux hcl hN hS hsub hρ hb
  | .prim hci hrow hnd hargs hd hty he => hty

theorem denTypedS {PT : PrimTableK} {env : Environment} (hcl : EnvClosedS env)
    (hN : ∀ ρ : Val, TDenS PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenS PT env ρ (.const `String []) String)
    (hsub : OblDenSubstS PT env) : OblDenTypedS PT env :=
  fun _ _ _ _ _ hρ h => denTypedS_aux hcl hN hS hsub hρ h

end Tools.ShippingGen5ConstValueES
