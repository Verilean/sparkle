import Tools.ShippingGen4ParamIface
import Tools.ShippingGen4ParamBridgeSpecType
set_option autoImplicit false
-- BUILT: clean issue-linked build par23v-261a2b3c exit 0 (708 jobs, dirty=false) at 261a2b3c9ca9045be2b61920dd3e46b4e5ea46af; implementation of scripts/gen4/PARAMETRIC_BRIDGE_UNIT6_FREEZE.md §2 (F3; freeze 99f322ce approved). Private Specialize.requirePositive / validateBindings are named by their mangled constants (name resolution only). legal_facts gives NECESSARY conditions of LegalBinding (positive values, parameter coverage); not an equivalence. forIn_yield_each is restricted to bodies that yield () or throw. B1-B3/T/FG unsupplied.
namespace Tools.ShippingGen4ParamBridgeLegal
open Lean Elab Term Tools.ShippingGen4ParamEntry Sparkle.IR.AST Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeSpecType

elab "specRequirePositive " c:term:max v:term:max : term => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.requirePositive
  let c ← elabTerm c (some (mkConst ``String))
  let v ← elabTerm v (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.mkAppM n #[c, v]

open Lean Elab Tactic in
elab "unfold_priv " s:ident : tactic => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ (`Sparkle.IR.Specialize ++ s.getId)
  evalTactic (← `(tactic| unfold $(mkIdent n):ident))

open Lean Elab Tactic in
elab "unfold_priv " s:ident " at " h:ident : tactic => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ (`Sparkle.IR.Specialize ++ s.getId)
  evalTactic (← `(tactic| unfold $(mkIdent n):ident at $h:ident))

/-- Restricted to loops whose body either yields `()` or throws (the shape of both `validateBindings` loops);
an arbitrary `forIn` body may return `done`, so no general statement is made. -/
theorem forIn_yield_each {α : Type} (l : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (hf : ∀ a, f a PUnit.unit = .ok (.yield PUnit.unit) ∨ ∃ e, f a PUnit.unit = .error e)
    {r : PUnit} (h : forIn l PUnit.unit f = .ok r) : ∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit) := by
  induction l with
  | nil => intro a ha; cases ha
  | cons x t ih =>
    intro a ha
    rw [List.forIn_cons] at h
    rcases hf x with hx | ⟨e, hx⟩
    · rw [hx] at h
      simp only [bind, Except.bind] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hx
      · exact ih h a ha'
    · rw [hx] at h
      simp [bind, Except.bind] at h

theorem requirePositive_eq (context : String) (value : Nat) :
    specRequirePositive context value = requirePositiveM context value := by
  unfold requirePositiveM
  unfold_priv requirePositive
  by_cases hv : (value == 0) = true
  · simp [hv, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp [hv, pure, Except.pure]

theorem legal_facts {D : Design} {θ : List (String × Nat)} (h : LegalBinding D θ) :
    (∀ p ∈ θ, (p.2 == 0) = false) ∧
    ∀ m ∈ D.modules, ∀ q ∈ m.parameters, (θ.lookup q.name).isNone = false := by
  unfold LegalBinding at h
  unfold_priv validateBindings at h
  obtain ⟨_, -, h⟩ := except_bind_ok' h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · obtain ⟨_, h1, h⟩ := except_bind_ok' h
    obtain ⟨_, h2, -⟩ := except_bind_ok' h
    have e1 := forIn_yield_each _ _ (by
      intro a
      split <;> (try split) <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]) h1
    have e2 := forIn_yield_each _ _ (by
      intro a
      split <;> (try split) <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]) h2
    refine ⟨fun p hp => ?_, fun m hm q hq => ?_⟩
    · have := e1 p hp
      cases hz : (p.2 == 0)
      · rfl
      · split at this <;> (try split at this) <;> simp_all [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]
    · have := e2 q.name (List.mem_flatMap.mpr ⟨m, hm, List.mem_map.mpr ⟨q, hq, rfl⟩⟩)
      cases hz : (θ.lookup q.name).isNone
      · rfl
      · simp_all [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]

theorem legalBinding_allPos {D : Design} {θ : List (String × Nat)} (h : LegalBinding D θ) : AllPos θ := by
  intro p hp
  have := (legal_facts h).1 p hp
  exact Nat.pos_of_ne_zero (by intro hz; simp [hz] at this)

theorem legalBinding_covers {D : Design} {θ : List (String × Nat)} (h : LegalBinding D θ) :
    ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v := by
  intro m hm q hq
  have := (legal_facts h).2 m hm q hq
  cases hl : θ.lookup q.name with
  | none => simp [hl] at this
  | some v => exact ⟨v, rfl⟩

end Tools.ShippingGen4ParamBridgeLegal
