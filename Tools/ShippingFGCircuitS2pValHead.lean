import Tools.ShippingFGCircuitS2iDTFun
set_option autoImplicit false
-- FG circuit pilot S2p: the value-head rule `DT.viaVar` / `Sh.bvarV` (docs/FG-CIRCUIT-PILOT.md §41): lemmas about it.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
namespace Tools.ShippingFGCircuitS2pValHead
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT

/-- an evaluation that ends at `Hn.var ρ₀ i` ends at a VALUE entry (the only rule with a `var` result is `bvarV`; every other rule passes the result through or has a different result) -/
theorem sh_var_val {env : Environment} {ρ : Cx} {e : Expr} {sp : List Ent} {hn : Hn} (h : Sh env ρ e sp hn) :
    ∀ {ρ₀ : Cx} {i : Nat}, hn = Hn.var ρ₀ i → ∃ en : Entry, ρ₀[i]? = some (Ent.val en) := by
  induction h with
  | app h ih => exact ih
  | lam h ih => exact ih
  | letZ h ih => exact ih
  | bvarC hb h ih => exact ih
  | bvarV hb =>
    intro ρ₀ i h'
    injection h' with h1 h2
    subst h1; subst h2
    exact ⟨_, hb⟩
  | unf hd hl hs h ih => exact ih
  | ctor hc hs hn => intro ρ₀ i h'; cases h'
  | prim hs => intro ρ₀ i h'; cases h'
  | proj hx hS hf h ihx ih => exact ih
  | recNil hi hm h ihm ih => exact ih
  | recCons hi hm h ihm ih => exact ih

/-- a value entry is never the head of an application: with a non-empty spine no `Sh` derivation ends at `Hn.var` through `bvarV` (`bvarV` has the empty spine) -/
theorem bvarV_spine {env : Environment} {ρ : Cx} {i : Nat} {sp : List Ent} {ρ₀ : Cx} {j : Nat} (h : Sh env ρ (.bvar i) sp (Hn.var ρ₀ j)) :
    (∃ en, ρ[i]? = some (Ent.val en)) → sp = [] := by
  intro ⟨en, hen⟩
  cases h with
  | bvarC hb h => rw [hen] at hb; cases hb
  | bvarV hb => rfl

/-- the two `DT` bridges are exclusive: no `viaSh` conclusion (constructor/stuck head) has the same `Sh` evaluation as a `viaVar` one -/
theorem var_not_head {hn : Hn} {ρ₀ : Cx} {i : Nat} (h : hn = Hn.var ρ₀ i) : hn.isVar = true := by subst h; rfl

end Tools.ShippingFGCircuitS2pValHead

#print axioms Tools.ShippingFGCircuitS2pValHead.sh_var_val
#print axioms Tools.ShippingFGCircuitS2pValHead.bvarV_spine
