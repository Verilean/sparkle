import Tools.ShippingGen5EnvDeclClosed
import Tools.ShippingGen5ConstValueEVL
import Tools.ShippingGen5RowTypedV
set_option autoImplicit false
/-! # `EnvDeclClosed` stated on the structure of `Expr` alone (issue sparkle-ledger-dd4-envcl; draft §EnvCl)

No TRUSTED, axiom, `sorry`, `native_decide`. `PT` is an explicit parameter. Existing files are unchanged.

Goal: the environment hypothesis of the final carrier (`CVEKVL`) must not pass through Lean's `opaque` `Expr.looseBVarRange` (`OblLbrZero`).
* §1 `closedAtB e k` is a structural `Bool` (no `max`, no `Nat` subtraction): "every `bvar i` of `e` that is not captured by a binder inside `e` has `i < k`". Proved `closedAtB e k ↔ lbr e ≤ k`.
* §2 `EnvDeclClosedS env`: every stored declaration type / `defnInfo` value satisfies `closedAtB · 0`. Proved equivalent to `EnvDeclClosed` and `EnvClosedL`. Mentions `Expr.looseBVarRange` nowhere.
* §3 The final-carrier theorems (`denTypedL`, `denTypedVL`, `denTypedVL_of_rows`) restated with `EnvDeclClosedS` as the ONLY environment hypothesis.
* §4 What remains of the old bridge: the kernel invariant stated on `looseBVarRange` is only a SOURCE of `EnvDeclClosedS`; the bridge needed is `OblLbrZeroOn env` (stored terms only), implied by (and much weaker than) `OblLbrZero`.
  The Lean API gives no way to prove it (`Expr.mkData` / `mkAppData` are `opaque`); see the Check file and draft §EnvCl. -/
namespace Tools.ShippingGen5EnvClosedS
open Lean Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueESL Tools.ShippingGen5EnvDeclClosed

/-! ## §1 Structural closedness -/

/-- `closedAtB e k`: all loose bound variables of `e` have index `< k` (`k` = binders passed so far). Pure structural recursion. -/
def closedAtB : Expr → Nat → Bool
  | .bvar i, k => decide (i < k)
  | .app f a, k => closedAtB f k && closedAtB a k
  | .lam _ A b _, k => closedAtB A k && closedAtB b (k + 1)
  | .forallE _ A b _, k => closedAtB A k && closedAtB b (k + 1)
  | .letE _ A v b _, k => closedAtB A k && closedAtB v k && closedAtB b (k + 1)
  | .mdata _ e, k => closedAtB e k
  | .proj _ _ e, k => closedAtB e k
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => true

theorem closedAtB_iff : ∀ (e : Expr) (k : Nat), closedAtB e k = true ↔ lbr e ≤ k
  | .bvar i, k => by simp [closedAtB, lbr]; omega
  | .app f a, k => by simp [closedAtB, lbr, closedAtB_iff f k, closedAtB_iff a k]
  | .lam _ A b _, k => by simp [closedAtB, lbr, closedAtB_iff A k, closedAtB_iff b (k + 1)]; omega
  | .forallE _ A b _, k => by simp [closedAtB, lbr, closedAtB_iff A k, closedAtB_iff b (k + 1)]; omega
  | .letE _ A v b _, k => by simp [closedAtB, lbr, closedAtB_iff A k, closedAtB_iff v k, closedAtB_iff b (k + 1), and_assoc]; omega
  | .mdata _ e, k => by simp [closedAtB, lbr, closedAtB_iff e k]
  | .proj _ _ e, k => by simp [closedAtB, lbr, closedAtB_iff e k]
  | .fvar _, k | .mvar _, k | .sort _, k | .const _ _, k | .lit _, k => by simp [closedAtB, lbr]

/-- a closed term: no loose bound variable, in the structural sense -/
def ClosedS (e : Expr) : Prop := closedAtB e 0 = true

theorem closedS_iff (e : Expr) : ClosedS e ↔ lbr e = 0 := by
  unfold ClosedS; rw [closedAtB_iff]; omega

instance (e : Expr) : Decidable (ClosedS e) := inferInstanceAs (Decidable (closedAtB e 0 = true))

/-! ## §2 `EnvDeclClosedS` -/

/-- closedness of the stored declaration at one name, structural form -/
def DeclClosedSAt (env : Environment) (c : Name) : Prop :=
  (∀ ci : ConstantInfo, env.find? c = some ci → ClosedS ci.type) ∧
  (∀ d : DefinitionVal, env.find? c = some (.defnInfo d) → ClosedS d.value)

/-- Every stored declaration type and definition value is closed. Stated with `closedAtB` only: no `lbr` arithmetic, no `Expr.looseBVarRange`. A fact about `env`, never assumed or an axiom. -/
def EnvDeclClosedS (env : Environment) : Prop :=
  (∀ (c : Name) (ci : ConstantInfo), env.find? c = some ci → ClosedS ci.type) ∧
  (∀ (c : Name) (d : DefinitionVal), env.find? c = some (.defnInfo d) → ClosedS d.value)

theorem envDeclClosedS_iff (env : Environment) : EnvDeclClosedS env ↔ EnvDeclClosed env :=
  ⟨fun h => ⟨fun c ci hc => (closedS_iff _).1 (h.1 c ci hc), fun c d hd => (closedS_iff _).1 (h.2 c d hd)⟩,
   fun h => ⟨fun c ci hc => (closedS_iff _).2 (h.1 c ci hc), fun c d hd => (closedS_iff _).2 (h.2 c d hd)⟩⟩

theorem envDeclClosedS_iff_closedL (env : Environment) : EnvDeclClosedS env ↔ EnvClosedL env :=
  ⟨fun h => envClosedL_of_declClosed ((envDeclClosedS_iff env).1 h),
   fun h => (envDeclClosedS_iff env).2 (envDeclClosed_of_closedL h)⟩

/-- localised form, the structural twin of `EnvDeclClosedOn` -/
def EnvDeclClosedSOn (env : Environment) (R : Name → Prop) : Prop := ∀ c, R c → DeclClosedSAt env c

theorem envDeclClosedSOn_iff (env : Environment) (R : Name → Prop) : EnvDeclClosedSOn env R ↔ EnvDeclClosedOn env R :=
  ⟨fun h c hc => ⟨fun ci hci => (closedS_iff _).1 ((h c hc).1 ci hci), fun d hd => (closedS_iff _).1 ((h c hc).2 d hd)⟩,
   fun h c hc => ⟨fun ci hci => (closedS_iff _).2 ((h c hc).1 ci hci), fun d hd => (closedS_iff _).2 ((h c hc).2 d hd)⟩⟩

theorem envDeclClosedS_of_on {env : Environment} {R : Name → Prop} (h : EnvDeclClosedSOn env R) (hall : ∀ c ci, env.find? c = some ci → R c) : EnvDeclClosedS env :=
  ⟨fun c ci hci => (h c (hall c ci hci)).1 ci hci, fun c d hd => (h c (hall c _ hd)).2 d hd⟩

/-! ## §3 The final carrier needs exactly `EnvDeclClosedS` (and nothing about `looseBVarRange`) -/

open Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueEKey in
/-- `CVEKL` soundness of the eight rules, environment hypothesis `EnvDeclClosedS` only (besides the two literal-type facts). -/
theorem denTypedL_S {PT : PrimTableK} {env : Environment} (hcl : EnvDeclClosedS env)
    (hN : ∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenL PT env ρ (.const `String []) String)
    (hsub : OblDenSubstL PT env) : OblDenTypedL PT env :=
  Tools.ShippingGen5ConstValueELProof.denTypedL_of_declClosed ((envDeclClosedS_iff env).1 hcl) hN hS hsub

open Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueEKey in
/-- The final carrier `CVEKVL`: soundness of all rules from `EnvDeclClosedS` and the two literal rows (a spec on `PT`). -/
theorem denTypedVL_S {PT : PrimTableK} {env : Environment} (hcl : EnvDeclClosedS env)
    (hN : ∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenV PT env ρ (.const `String []) String) :
    OblDenTypedV PT env :=
  Tools.ShippingGen5ConstValueEVL.denTypedVL ((envDeclClosedS_iff env).1 hcl) hN hS

open Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueEKey in
theorem denTypedVL_of_rows_S {PT : PrimTableK} {env : Environment} (hcl : EnvDeclClosedS env) {rn rs : TyRow}
    (hn : PT.tys `Nat [] = some rn) (hnnd : ¬ IsDefn env `Nat) (hnk : rn.kinds = []) (hnT : rn.den [] = some Nat)
    (hs : PT.tys `String [] = some rs) (hsnd : ¬ IsDefn env `String) (hsk : rs.kinds = []) (hsT : rs.den [] = some String) :
    OblDenTypedV PT env :=
  Tools.ShippingGen5RowTypedV.denTypedVL_of_rows ((envDeclClosedS_iff env).1 hcl) hn hnnd hnk hnT hs hsnd hsk hsT

/-! ## §4 What is left of the kernel-invariant bridge -/

/-- The bridge restricted to the stored terms (named, unresolved, never assumed): where the kernel invariant says `looseBVarRange = 0`, the structural `lbr` is `0`. -/
def OblLbrZeroOn (env : Environment) : Prop :=
  (∀ (c : Name) (ci : ConstantInfo), env.find? c = some ci → ci.type.looseBVarRange = 0 → lbr ci.type = 0) ∧
  (∀ (c : Name) (d : DefinitionVal), env.find? c = some (.defnInfo d) → d.value.looseBVarRange = 0 → lbr d.value = 0)

/-- the old global bridge implies the restricted one (so the restricted one is the weaker obligation) -/
theorem oblLbrZeroOn_of_global (env : Environment) (hz : OblLbrZero) : OblLbrZeroOn env :=
  ⟨fun _ ci _ h => hz _ h, fun _ d _ h => hz _ h⟩

/-- Kernel invariant (on `looseBVarRange`) + the restricted bridge give `EnvDeclClosedS`. An implication between named `Prop`s. -/
theorem envDeclClosedS_of_kernel {env : Environment} (hz : OblLbrZeroOn env) (h : KernelClosedInvariant env) : EnvDeclClosedS env :=
  ⟨fun c ci hc => (closedS_iff _).2 (hz.1 c ci hc (h.1 c ci hc)), fun c d hd => (closedS_iff _).2 (hz.2 c d hd (h.2 c d hd))⟩

/-- The restricted bridge together with `EnvDeclClosedS`'s source: `EnvDeclClosedS` is itself the whole obligation. It is the weakest named hypothesis the carrier needs;
the pair (`KernelClosedInvariant`, `OblLbrZeroOn`) is only one possible route to it. -/
theorem kernelInvariant_of_declClosedS_and_range {env : Environment} (h : EnvDeclClosedS env)
    (hr : ∀ e : Expr, lbr e = 0 → e.looseBVarRange = 0) : KernelClosedInvariant env :=
  ⟨fun c ci hc => hr _ ((closedS_iff _).1 (h.1 c ci hc)), fun c d hd => hr _ ((closedS_iff _).1 (h.2 c d hd))⟩

end Tools.ShippingGen5EnvClosedS
