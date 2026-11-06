import Tools.ShippingFGCircuitS1wTbl
set_option autoImplicit false
-- FG circuit pilot S2b: the SHARED (closure-environment) weak-head relation `Sh`, docs/FG-CIRCUIT-PILOT.md §30. A relation (the specification of route 2a), its functionality, and a worked example.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # `Sh`: weak-head evaluation with closures (no substitution)

A closure entry `Ent.clo e ρ` is an UNEVALUATED expression `e` with its CAPTURED environment `ρ` (de Bruijn references, no copy of `e`). `Sh env ρ e sp hn` : `e` in `ρ` applied to the spine `sp` (closures)
reaches the head normal form `hn` : a constructor application whose fields are closures (`Hn.ctor`), or a stuck primitive head with closure arguments (`Hn.stuck`).
Rules: `app` pushes a closure of the argument (call-by-name, NOT evaluated first); `lam` binds the first spine closure; `letZ` binds a closure of the let value (only for a let whose type is not a core head, the case that
`DW.zeta` handled by substitution); `bvarC` follows a closure; `unf` unfolds a definition of `env` in the EMPTY environment (a definition is closed); `proj` projects the closure field of a constructor result.
Nothing is evaluated twice by the RELATION's size: a closure is shared by reference, so the size of a derivation is the number of machine steps, not the size of the substituted tree.
Value entries (`Ent.val`) are the existing `Entry` (Lean value + syntactic type), used where the value is representable. -/
namespace Tools.ShippingFGCircuitS2bMachine
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD

inductive Ent : Type 1
  | val (en : Entry)
  | clo (e : Expr) (ρ : List Ent)

abbrev Cx := List Ent

inductive Hn : Type 1
  | ctor (c : Name) (ind : Name) (np : Nat) (args : List Ent)
  | stuck (c : Name) (ls : List Level) (args : List Ent)

/-- heads that are never unfolded (the primitive value heads, the new stop heads, the core type heads) -/
def stopSh (c : Name) : Bool := stopC c || newStopC c || Tools.ShippingFGCircuitS1rCD.tyStopC c

inductive Sh (env : Environment) : Cx → Expr → List Ent → Hn → Prop
  | app {ρ : Cx} {f a : Expr} {sp : List Ent} {hn : Hn} (h : Sh env ρ f (.clo a ρ :: sp) hn) : Sh env ρ (.app f a) sp hn
  | lam {ρ : Cx} {n : Name} {A b : Expr} {bi : BinderInfo} {c : Ent} {sp : List Ent} {hn : Hn} (h : Sh env (c :: ρ) b sp hn) : Sh env ρ (.lam n A b bi) (c :: sp) hn
  | letZ {ρ : Cx} {n : Name} {A v b : Expr} {nd : Bool} {sp : List Ent} {hn : Hn} (hA : coreHead A = false) (h : Sh env (.clo v ρ :: ρ) b sp hn) :
      Sh env ρ (.letE n A v b nd) sp hn
  | bvarC {ρ : Cx} {i : Nat} {e' : Expr} {ρ' : Cx} {sp : List Ent} {hn : Hn} (hb : ρ[i]? = some (.clo e' ρ')) (h : Sh env ρ' e' sp hn) : Sh env ρ (.bvar i) sp hn
  | unf {ρ : Cx} {c : Name} {ls : List Level} {d : DefinitionVal} {sp : List Ent} {hn : Hn} (hd : env.find? c = some (.defnInfo d))
      (hl : d.levelParams.length = ls.length) (hs : stopSh c = false) (h : Sh env [] (instLE d.levelParams ls d.value) sp hn) : Sh env ρ (.const c ls) sp hn
  | ctor {ρ : Cx} {c : Name} {ls : List Level} {cv : ConstructorVal} {sp : List Ent} (hc : env.find? c = some (.ctorInfo cv)) (hs : stopSh c = false)
      (hn : sp.length = cv.numParams + cv.numFields) : Sh env ρ (.const c ls) sp (.ctor c cv.induct cv.numParams sp)
  | prim {ρ : Cx} {c : Name} {ls : List Level} {sp : List Ent} (hs : stopSh c = true) : Sh env ρ (.const c ls) sp (.stuck c ls sp)
  | proj {ρ : Cx} {S : Name} {i : Nat} {x : Expr} {sp : List Ent} {hn : Hn} {c ind : Name} {np : Nat} {args : List Ent} {e' : Expr} {ρ' : Cx}
      (hx : Sh env ρ x [] (.ctor c ind np args)) (hS : ind = S) (hf : args[np + i]? = some (.clo e' ρ')) (h : Sh env ρ' e' sp hn) : Sh env ρ (.proj S i x) sp hn

theorem Hn.ctor_inj {c c' ind ind' : Name} {np np' : Nat} {a a' : List Ent} (h : Hn.ctor c ind np a = Hn.ctor c' ind' np' a') : c = c' ∧ ind = ind' ∧ np = np' ∧ a = a' := by
  injection h with h1 h2 h3 h4; exact ⟨h1, h2, h3, h4⟩

set_option maxRecDepth 4000 in
/-- **functionality** of `Sh`: the machine is deterministic -/
theorem sh_fun {env : Environment} {ρ : Cx} {e : Expr} {sp : List Ent} {hn : Hn} (h : Sh env ρ e sp hn) : ∀ {hn' : Hn}, Sh env ρ e sp hn' → hn = hn' := by
  induction h with
  | app h ih => intro hn' h'; cases h' with | app h' => exact ih h'
  | lam h ih => intro hn' h'; cases h' with | lam h' => exact ih h'
  | letZ hA h ih => intro hn' h'; cases h' with | letZ hA' h' => exact ih h'
  | bvarC hb h ih =>
    intro hn' h'; cases h' with
    | bvarC hb' h' =>
      rw [hb] at hb'
      have := Option.some.inj hb'
      injection this with h1 h2
      subst h1; subst h2
      exact ih h'
  | unf hd hl hs h ih =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' =>
      rw [hd] at hd'
      have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
      subst this
      exact ih h'
    | ctor hc hs' hn => rw [hd] at hc; cases hc
    | prim hs' => rw [hs] at hs'; cases hs'
  | ctor hc hs hn =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' => rw [hc] at hd'; cases hd'
    | ctor hc' hs' hn' =>
      rw [hc] at hc'
      have := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
      subst this; rfl
    | prim hs' => rw [hs] at hs'; cases hs'
  | prim hs =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' => rw [hs] at hs'; cases hs'
    | ctor hc' hs' hn' => rw [hs] at hs'; cases hs'
    | prim hs' => rfl
  | proj hx hS hf h ihx ih =>
    intro hn' h'; cases h' with
    | proj hx' hS' hf' h' =>
      have e1 := Hn.ctor_inj (ihx hx')
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e1
      rw [hf] at hf'
      have := Option.some.inj hf'
      injection this with h1 h2
      subst h1; subst h2
      exact ih h'

/-! ## a worked example: sharing by reference

`let x := (a b)-pair-of-a-big-term; proj_0 (Prod.mk x x)`-shaped; the point is the shape of the derivation: one `letZ` per binding, and the second use of `x` is `bvarC` to the SAME closure. -/

end Tools.ShippingFGCircuitS2bMachine

#print axioms Tools.ShippingFGCircuitS2bMachine.sh_fun
