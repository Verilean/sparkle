import Tools.ShippingGen5ConstValueE
set_option autoImplicit false
-- D.D-4 B, DCF-1..3: structural check of the ConstValueE functionality theorems (PT universal, no extra hypothesis, negative controls).

namespace Tests.Gen5.DCFCheck
open Lean Tools.ShippingGen5ConstValueE

/-! ## Structural match of the theorem types (the stated type is checked against the theorem by definitional unification).
`PT` and `env` are universally quantified; the only hypotheses are the two derivations. -/

example : ∀ (PT : PrimTable) (env : Environment) (ρ : Val) (τ : Expr) (T T' : Type),
    TDen PT env ρ τ T → TDen PT env ρ τ T' → T = T' :=
  fun _ _ _ _ _ _ h h' => tden_fun h h'

example : ∀ (PT : PrimTable) (env : Environment) (ρ : Val) (ks : List Bool) (es : List Expr) (as as' : List Arg),
    ArgsDen PT env ρ ks es as → ArgsDen PT env ρ ks es as' → as = as' :=
  fun _ _ _ _ _ _ _ h h' => argsden_fun h h'

example : ∀ (PT : PrimTable) (env : Environment) (ρ : Val) (e τ τ' : Expr) (α β : Type) (v : α) (w : β),
    CVE PT env ρ e τ α v → CVE PT env ρ e τ' β w → τ = τ' ∧ α = β ∧ HEq v w :=
  fun _ _ _ _ _ _ _ _ _ _ h h' => cve_fun h h'

example : ∀ (PT : PrimTable) (env : Environment) (X : Name) (ls : List Level) (α β : Type) (v : α) (w : β),
    ConstValueEAt PT env X ls α v → ConstValueEAt PT env X ls β w → α = β ∧ HEq v w :=
  fun PT env X ls _ _ _ _ h h' => constValueEAt_functional PT env X ls h h'

/-! ## Negative controls -/

/-- Non-vacuous: a derivation exists (for the empty table). -/
def emptyPT : PrimTable := ⟨fun _ => none, fun _ => none⟩

example (env : Environment) : CVE emptyPT env [] (.lit (.natVal 3)) (.const `Nat []) Nat 3 := .natLit

/-- Functionality bites: two different literal values of the same literal are not both derivable (any `PT`, `env`). -/
theorem lit_values_differ (PT : PrimTable) (env : Environment) {n m : Nat}
    (h : CVE PT env [] (.lit (.natVal 3)) (.const `Nat []) Nat n) (h' : CVE PT env [] (.lit (.natVal 3)) (.const `Nat []) Nat m) :
    n = m := eq_of_heq (cve_fun h h').2.2

example (env : Environment) : ¬ (CVE emptyPT env [] (.lit (.natVal 3)) (.const `Nat []) Nat 3 ∧
    CVE emptyPT env [] (.lit (.natVal 3)) (.const `Nat []) Nat 4) :=
  fun ⟨h, h'⟩ => absurd (lit_values_differ emptyPT env h h') (by decide)

theorem unit_ne_bool : (Unit : Type) ≠ Bool := by
  intro e
  have h : ∀ a b : Bool, a = b := e ▸ (fun (a b : Unit) => Subsingleton.elim a b)
  exact Bool.noConfusion (h true false)

/-- The contrast with `cvTop` (CVTopCheck): at `CVE`, a `Unit` reading and a `Bool` reading of one term cannot coexist, for any `PT`, `env`. -/
theorem no_unit_and_bool (PT : PrimTable) (env : Environment) (ρ : Val) (e τ τ' : Expr)
    (h : CVE PT env ρ e τ Unit ()) (h' : CVE PT env ρ e τ' Bool true) : False :=
  unit_ne_bool (cve_fun h h').2.1

/-- Exclusivity is in the rules: a `prim` and an `unfold` derivation of the same const-headed spine cannot coexist
(the `IsDefn` premise of `prim` fails when the head is a `defnInfo`). -/
example (env : Environment) (c : Name) (d : DefinitionVal) (hd : env.find? c = some (.defnInfo d)) : IsDefn env c := ⟨d, hd⟩

end Tests.Gen5.DCFCheck

#print axioms Tools.ShippingGen5ConstValueE.tden_fun
#print axioms Tools.ShippingGen5ConstValueE.argsden_fun
#print axioms Tools.ShippingGen5ConstValueE.cve_fun
#print axioms Tools.ShippingGen5ConstValueE.constValueEAt_functional
#print axioms Tests.Gen5.DCFCheck.lit_values_differ
#print axioms Tests.Gen5.DCFCheck.no_unit_and_bool
