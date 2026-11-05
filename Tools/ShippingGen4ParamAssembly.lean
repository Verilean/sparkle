import Tools.ShippingGen4FKids
import Tools.ShippingGen4FKidsObl
import Tools.ShippingGen4FTop
import Tools.ShippingGen4Shape
import Tools.ShippingGen4ParamBridgeLegal
import Tools.ShippingGen4ParamBridgeSpecExpr
set_option autoImplicit false

/-! # M4 parametric assembly (scripts/gen4/PARAM_ASSEMBLY.md): `LegalBinding` and `AllPos` from a real run -/

namespace Tools.ShippingGen4ParamAssembly
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingLegacySem Tools.ShippingGen4ParamEntry
open Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamBridgeLegal Tools.ShippingGen4ParamLayerA

/-! ## 1. The constructive direction of `validateBindings`

`legal_of_facts` is the converse of `legal_facts` (ParamBridgeLegal): the five clauses (a)-(e) of the private
`validateBindings`, each stated as a Lean proposition, give `LegalBinding`. -/

theorem filter_len_one {names : List String} (h : names.Nodup) :
    ∀ a ∈ names, (names.filter (· == a)).length = 1 := by
  induction names with
  | nil => intro a ha; cases ha
  | cons x t ih =>
    intro a ha
    have hn := List.nodup_cons.mp h
    by_cases hx : x = a
    · subst hx
      have : t.filter (· == x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hbx
        have : b = x := by simpa using hbx
        exact hn.1 (this ▸ hb)
      simp [List.filter_cons, this]
    · have hat : a ∈ t := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hx
        · exact h
      have hxa : (x == a) = false := by simpa using hx
      simp [List.filter_cons, hxa, ih hn.2 a hat]

theorem dupName_none (names : List String) (h : names.Nodup) :
    names.find? (fun name => decide ((names.filter (· == name)).length > 1)) = none := by
  rw [List.find?_eq_none]
  intro a ha
  simp [filter_len_one h a ha]

theorem forIn_all_yield {α : Type} (l : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (h : ∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn l PUnit.unit f = .ok PUnit.unit := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.forIn_cons, h x List.mem_cons_self]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem legal_of_facts {D : Design} {θ : List (String × Nat)}
    (ha : ∀ m ∈ D.modules, (m.parameters.map (·.name)).Nodup)
    (hb : (θ.map (·.1)).Nodup)
    (hc : ∀ p ∈ θ, ∃ m ∈ D.modules, ∃ q ∈ m.parameters, q.name = p.1)
    (hd : ∀ p ∈ θ, p.2 ≠ 0)
    (he : ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v) :
    LegalBinding D θ := by
  unfold LegalBinding
  unfold_priv validateBindings
  unfold_priv validateParameterDeclarations
  unfold_priv duplicateName?
  rw [forIn_all_yield D.modules _ (by
    intro m hm
    dsimp only
    rw [dupName_none _ (ha m hm)]
    rfl)]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dupName_none _ hb]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [forIn_all_yield θ _ (by
    intro p hp
    obtain ⟨name, value⟩ := p
    obtain ⟨m, hm, q, hq, hqn⟩ := hc (name, value) hp
    have hcont : (List.flatMap (fun hardwareModule => List.map (fun x => x.name) hardwareModule.parameters) D.modules).contains name = true := by
      rw [List.contains_iff_mem]
      exact List.mem_flatMap.mpr ⟨m, hm, List.mem_map.mpr ⟨q, hq, hqn⟩⟩
    have hv : (value == 0) = false := by simpa using hd (name, value) hp
    have hmem : ∃ a, a ∈ D.modules ∧ ∃ a_1, a_1 ∈ a.parameters ∧ a_1.name = name := ⟨m, hm, q, hq, hqn⟩
    simp [hcont, hv, pure, Except.pure, hmem])]
  rw [forIn_all_yield _ _ (by
    intro name hn
    obtain ⟨m, hm, hmq⟩ := List.mem_flatMap.mp hn
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmq
    obtain ⟨v, hv⟩ := he m hm q hq
    simp [hv, pure, Except.pure])]

/-! ## 2. A returning `synthesizeFromConst` run reads a definition -/

theorem sfc_defn
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe ci isInst) (M, D)) :
    ∃ dv, ci = .defnInfo dv := by
  cases ci with
  | defnInfo dv => exact ⟨dv, rfl⟩
  | _ =>
    exfalso
    unfold synthesizeFromConst at hr
    simp only [certifiedShape_off true parameters _ (by simp),
      mixedCertifiedShape_off true parameters _ isInst (by simp), ite_self,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr
    all_goals (
      obtain ⟨y, hy, a3⟩ := MReturns.bind hr
      obtain rfl := MReturns.pure hy
      dsimp only at a3
      obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
      obtain rfl := MReturns.pure hy2
      dsimp only at h2
      obtain ⟨_, _, h3⟩ := MReturns.bind h2
      unfold Lean.throwError at h3
      obtain ⟨_, _, h4⟩ := MReturns.bind h3
      obtain ⟨_, _, h5⟩ := MReturns.bind h4
      exact MReturns.throw h5)

end Tools.ShippingGen4ParamAssembly
