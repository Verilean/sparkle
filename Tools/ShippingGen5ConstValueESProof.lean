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

end Tools.ShippingGen5ConstValueES
