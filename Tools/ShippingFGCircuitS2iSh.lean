import Tools.ShippingFGCircuitS1sCD
set_option autoImplicit false
-- FG circuit pilot S2i: the closure-environment weak-head relation `Sh` (S2b `Sh` + the static `List.rec` rule, constructor levels kept in `Hn`), docs/FG-CIRCUIT-PILOT.md §35.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # `Sh` (S2i)

Differences from the S2b `Sh` (Tools/ShippingFGCircuitS2bMachine.lean):
* `Hn` keeps the LEVELS of the constructor / stuck constant (the reviewer's request: the bridge must not forget ctor levels);
* the `List.rec` rule (replaces the substitution rules `recIota`/`projRec` of `DS`): the major premise is a CLOSURE, evaluated by `Sh` to a STATIC `List.nil`/`List.cons`;
  the recursive call of the `cons` case is the closure `List.rec.{ls} #4 #3 #2 #1 #0` over the environment `[tl, consc, nilc, mot, a0]` (no copy of the arguments);
* the stop set `stopD` is `stopSh` plus `Signal.map` (the head of the narrow wiring rules `mapFst`/`mapSnd`: it is never unfolded to `Signal.mk`).

`Sh` is a relation on `Expr` (an environment machine), NOT a typed kernel evaluation: the typed meaning is given by the family `DT` (Tools/ShippingFGCircuitS2iDT.lean) that uses `Sh` only to reach a stuck/constructor head. -/
namespace Tools.ShippingFGCircuitS2iSh
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD
open Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD

/-- the value of a CLOSED level (kernel-evaluable; `none` for a parameter or a metavariable); the same definition as `lvlNat` of S2b (copied so that this file does not import `S2bShare`) -/
def lvlNatT : Level → Option Nat
  | .zero => some 0
  | .succ l => (lvlNatT l).map (· + 1)
  | .max a b => match lvlNatT a, lvlNatT b with
    | some x, some y => some (if x ≤ y then y else x)
    | _, _ => none
  | .imax a b => match lvlNatT a, lvlNatT b with
    | some x, some y => some (if y = 0 then 0 else if x ≤ y then y else x)
    | _, _ => none
  | _ => none

theorem lvlNatT_one : lvlNatT (.succ .zero) = some 1 := rfl
theorem lvlNatT_max11 : lvlNatT (.max (.succ .zero) (.succ .zero)) = some 1 := rfl

inductive Ent : Type 1
  | val (en : Entry)
  | clo (e : Expr) (ρ : List Ent)

abbrev Cx := List Ent

inductive Hn : Type 1
  | ctor (c : Name) (ls : List Level) (np : Nat) (sp : List Ent)
  | stuck (c : Name) (ls : List Level) (sp : List Ent)
  /-- NEW (S2p). the evaluation ended at a bare VALUE entry: the variable `i` of the environment `ρ` (empty spine) -/
  | var (ρ : List Ent) (i : Nat)

def Hn.head : Hn → Name × List Level × List Ent
  | .ctor c ls _ sp => (c, ls, sp)
  | .stuck c ls sp => (c, ls, sp)
  | .var _ _ => (.anonymous, [], [])

/-- the result is a bare value variable (it has no constructor / stuck head) -/
def Hn.isVar : Hn → Bool
  | .var .. => true
  | _ => false

/-- heads that are never unfolded: the primitive value heads, the new stop heads, the core type heads, and `Signal.map` (the narrow wiring rules) -/
def stopD (c : Name) : Bool := stopC c || newStopC c || tyStopC c || c == ``Signal.map || c == ``HShiftLeft.hShiftLeft || c == ``HAppend.hAppend

theorem stopD_listRec : stopD ``List.rec = false := by decide
theorem stopD_signalMap : stopD ``Signal.map = true := by decide
theorem stopD_shl : stopD ``HShiftLeft.hShiftLeft = true := by decide
theorem stopD_append : stopD ``HAppend.hAppend = true := by decide

/-- the recursive call of `List.rec.{ls}` as a closure expression over the environment `[tl, consc, nilc, mot, a0]` -/
def recCallE (ls : List Level) : Expr := mkApps (.const ``List.rec ls) [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]

inductive Sh (env : Environment) : Cx → Expr → List Ent → Hn → Prop
  | app {ρ : Cx} {f a : Expr} {sp : List Ent} {hn : Hn} (h : Sh env ρ f (.clo a ρ :: sp) hn) : Sh env ρ (.app f a) sp hn
  | lam {ρ : Cx} {n : Name} {A b : Expr} {bi : BinderInfo} {c : Ent} {sp : List Ent} {hn : Hn} (h : Sh env (c :: ρ) b sp hn) : Sh env ρ (.lam n A b bi) (c :: sp) hn
  | letZ {ρ : Cx} {n : Name} {A v b : Expr} {nd : Bool} {sp : List Ent} {hn : Hn} (h : Sh env (.clo v ρ :: ρ) b sp hn) :
      Sh env ρ (.letE n A v b nd) sp hn
  | bvarC {ρ : Cx} {i : Nat} {e' : Expr} {ρ' : Cx} {sp : List Ent} {hn : Hn} (hb : ρ[i]? = some (.clo e' ρ')) (h : Sh env ρ' e' sp hn) : Sh env ρ (.bvar i) sp hn
  /-- NEW (S2p). a variable bound to a VALUE entry, with an EMPTY spine, is itself the result (a value entry is never applied) -/
  | bvarV {ρ : Cx} {i : Nat} {en : Entry} (hb : ρ[i]? = some (.val en)) : Sh env ρ (.bvar i) [] (.var ρ i)
  | unf {ρ : Cx} {c : Name} {ls : List Level} {d : DefinitionVal} {sp : List Ent} {hn : Hn} (hd : env.find? c = some (.defnInfo d))
      (hl : d.levelParams.length = ls.length) (hs : stopD c = false) (h : Sh env [] (instLE d.levelParams ls d.value) sp hn) : Sh env ρ (.const c ls) sp hn
  | ctor {ρ : Cx} {c : Name} {ls : List Level} {cv : ConstructorVal} {sp : List Ent} (hc : env.find? c = some (.ctorInfo cv)) (hs : stopD c = false)
      (hn : sp.length = cv.numParams + cv.numFields) : Sh env ρ (.const c ls) sp (.ctor c ls cv.numParams sp)
  | prim {ρ : Cx} {c : Name} {ls : List Level} {sp : List Ent} (hs : stopD c = true) : Sh env ρ (.const c ls) sp (.stuck c ls sp)
  | proj {ρ : Cx} {S : Name} {i : Nat} {x : Expr} {sp : List Ent} {hn : Hn} {c : Name} {ls : List Level} {np : Nat} {args : List Ent} {e' : Expr} {ρ' : Cx}
      (hx : Sh env ρ x [] (.ctor c ls np args)) (hS : ∃ cv : ConstructorVal, env.find? c = some (.ctorInfo cv) ∧ cv.induct = S)
      (hf : args[np + i]? = some (.clo e' ρ')) (h : Sh env ρ' e' sp hn) : Sh env ρ (.proj S i x) sp hn
  /-- NEW (S2i). `List.rec.{ls} a0 mot nilc consc major extra…` with the major premise a closure that evaluates to the STATIC `List.nil`: continue with the closure `nilc` applied to `extra` -/
  | recNil {ρ : Cx} {ls : List Level} {ri : RecursorVal} {a0 mot consc : Ent} {em : Expr} {ρm : Cx} {extra : List Ent} {lsN : List Level} {sp1 : List Ent}
      {en : Expr} {ρn : Cx} {hn : Hn} (hi : env.find? ``List.rec = some (.recInfo ri))
      (hm : Sh env ρm em [] (.ctor ``List.nil lsN 1 sp1)) (h : Sh env ρn en extra hn) :
      Sh env ρ (.const ``List.rec ls) (a0 :: mot :: .clo en ρn :: consc :: .clo em ρm :: extra) hn
  /-- NEW (S2i). the major premise evaluates to the STATIC `List.cons α h tl`: continue with the closure `consc` applied to `h tl (rec-call) extra…`, the recursive call being the closure `recCallE ls` over `[tl, consc, nilc, mot, a0]` -/
  | recCons {ρ : Cx} {ls : List Level} {ri : RecursorVal} {a0 mot nilc : Ent} {em : Expr} {ρm : Cx} {extra : List Ent} {lsC : List Level} {al hd tl : Ent}
      {ec : Expr} {ρc : Cx} {hn : Hn} (hi : env.find? ``List.rec = some (.recInfo ri))
      (hm : Sh env ρm em [] (.ctor ``List.cons lsC 1 [al, hd, tl]))
      (h : Sh env ρc ec (hd :: tl :: .clo (recCallE ls) [tl, .clo ec ρc, nilc, mot, a0] :: extra) hn) :
      Sh env ρ (.const ``List.rec ls) (a0 :: mot :: nilc :: .clo ec ρc :: .clo em ρm :: extra) hn

theorem Hn.ctor_inj {c c' : Name} {ls ls' : List Level} {np np' : Nat} {a a' : List Ent} (h : Hn.ctor c ls np a = Hn.ctor c' ls' np' a') :
    c = c' ∧ ls = ls' ∧ np = np' ∧ a = a' := by
  injection h with h1 h2 h3 h4; exact ⟨h1, h2, h3, h4⟩

theorem Ent.clo_inj {e e' : Expr} {ρ ρ' : Cx} (h : Ent.clo e ρ = Ent.clo e' ρ') : e = e' ∧ ρ = ρ' := by
  injection h with h1 h2; exact ⟨h1, h2⟩

theorem Hn.ne_ctor_ctor_nil_cons {ls ls' : List Level} {np np' : Nat} {a a' : List Ent} :
    Hn.ctor ``List.nil ls np a ≠ Hn.ctor ``List.cons ls' np' a' := by
  intro h
  have := (Hn.ctor_inj h).1
  exact absurd this (by decide)

set_option maxRecDepth 4000 in
/-- **functionality** of `Sh`: the machine is deterministic -/
theorem sh_fun {env : Environment} {ρ : Cx} {e : Expr} {sp : List Ent} {hn : Hn} (h : Sh env ρ e sp hn) : ∀ {hn' : Hn}, Sh env ρ e sp hn' → hn = hn' := by
  induction h with
  | app h ih => intro hn' h'; cases h' with | app h' => exact ih h'
  | lam h ih => intro hn' h'; cases h' with | lam h' => exact ih h'
  | letZ h ih => intro hn' h'; cases h' with | letZ h' => exact ih h'
  | bvarC hb h ih =>
    intro hn' h'; cases h' with
    | bvarC hb' h' =>
      rw [hb] at hb'
      have := Option.some.inj hb'
      injection this with h1 h2
      subst h1; subst h2
      exact ih h'
    | bvarV hb' => rw [hb] at hb'; cases hb'
  | bvarV hb =>
    intro hn' h'; cases h' with
    | bvarC hb' h' => rw [hb] at hb'; cases hb'
    | bvarV hb' => rfl
  | unf hd hl hs h ih =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' =>
      rw [hd] at hd'
      have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
      subst this
      exact ih h'
    | ctor hc hs' hn => rw [hd] at hc; cases hc
    | prim hs' => rw [hs] at hs'; cases hs'
    | recNil hi' hm' h' => rw [hd] at hi'; cases hi'
    | recCons hi' hm' h' => rw [hd] at hi'; cases hi'
  | ctor hc hs hn =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' => rw [hc] at hd'; cases hd'
    | ctor hc' hs' hn' =>
      rw [hc] at hc'
      have := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
      subst this; rfl
    | prim hs' => rw [hs] at hs'; cases hs'
    | recNil hi' hm' h' => rw [hc] at hi'; cases hi'
    | recCons hi' hm' h' => rw [hc] at hi'; cases hi'
  | prim hs =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' => rw [hs] at hs'; cases hs'
    | ctor hc' hs' hn' => rw [hs] at hs'; cases hs'
    | prim hs' => rfl
    | recNil hi' hm' h' => rw [stopD_listRec] at hs; cases hs
    | recCons hi' hm' h' => rw [stopD_listRec] at hs; cases hs
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
  | recNil hi hm h ihm ih =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' => rw [hi] at hd'; cases hd'
    | ctor hc' hs' hn' => rw [hi] at hc'; cases hc'
    | prim hs' => rw [stopD_listRec] at hs'; cases hs'
    | recNil hi' hm' h' => exact ih h'
    | recCons hi' hm' h' =>
      exact absurd (ihm hm') Hn.ne_ctor_ctor_nil_cons
  | recCons hi hm h ihm ih =>
    intro hn' h'; cases h' with
    | unf hd' hl' hs' h' => rw [hi] at hd'; cases hd'
    | ctor hc' hs' hn' => rw [hi] at hc'; cases hc'
    | prim hs' => rw [stopD_listRec] at hs'; cases hs'
    | recNil hi' hm' h' => exact absurd (ihm hm').symm Hn.ne_ctor_ctor_nil_cons
    | recCons hi' hm' h' =>
      have e1 := Hn.ctor_inj (ihm hm')
      obtain ⟨_, _, _, e2⟩ := e1
      simp only [List.cons.injEq, and_true] at e2
      obtain ⟨_, rfl, rfl⟩ := e2
      exact ih h'

end Tools.ShippingFGCircuitS2iSh

#print axioms Tools.ShippingFGCircuitS2iSh.sh_fun
