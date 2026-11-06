import Tools.ShippingFGCircuitS1sCD
set_option autoImplicit false
-- FG circuit pilot S1w: environment-free evaluators over the named finite tables, their soundness, and the table versions of the `DW` rules. docs/FG-CIRCUIT-PILOT.md §26.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1w tables

The rules of `DW` that read the environment (`unf`, `beta`, `projStep`, `projCtor`, `recIota`, `projRec`, `prodMk`, `unitVal`, `inhMk`, `mapFst`/`mapSnd`) ask for facts like
`unfoldAt env e = some e'` or `recStep env e = some e'` about an ABSTRACT `env`. A closed term cannot compute them. Here every such function gets an environment-free
evaluator `…L lk` over a lookup `lk : Name → Option Lk` (the tables `Δ`/`Γ` and the `List.rec` fact). The evaluators are THREE-valued: `none` = a name that is not in the tables was met
(no information), `some none` = the function returns `none`, `some (some x)` = it returns `some x`. Soundness: `EnvLk env lk` and `…L lk x = some o` give `… env x = o`. -/
namespace Tools.ShippingFGCircuitS1wTbl
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD

/-- what the tables say about a constant -/
inductive Lk
  | defn (r : DefRow)
  | ctor (r : CtorRow)
  | recl

abbrev Look := Name → Option Lk

/-- the fact about `env` that a table entry stands for -/
def LkOk (env : Environment) (c : Name) : Lk → Prop
  | .defn r => ∃ d : DefinitionVal, env.find? c = some (.defnInfo d) ∧ d.levelParams = r.lps ∧ d.value = r.value
  | .ctor r => ∃ cv : ConstructorVal, env.find? c = some (.ctorInfo cv) ∧ cv.induct = r.induct ∧ cv.numParams = r.numParams ∧ cv.numFields = r.numFields
  | .recl => ∃ ri : RecursorVal, env.find? c = some (.recInfo ri)

def EnvLk (env : Environment) (lk : Look) : Prop := ∀ c k, lk c = some k → LkOk env c k

/-- the lookup from the named tables: definitions, constructors, and `List.rec` -/
def lookOf (Δ : Name → Option DefRow) (Γ : Name → Option CtorRow) : Look := fun c =>
  match Δ c with
  | some r => some (.defn r)
  | none =>
    match Γ c with
    | some r => some (.ctor r)
    | none => if c == ``List.rec then some .recl else none

def RecFact (env : Environment) : Prop := ∃ ri : RecursorVal, env.find? ``List.rec = some (.recInfo ri)

theorem envLk_of {env : Environment} {Δ : Name → Option DefRow} {Γ : Name → Option CtorRow} (hΔ : EnvDefs env Δ) (hΓ : EnvCtors env Γ) (hr : RecFact env) :
    EnvLk env (lookOf Δ Γ) := by
  intro c k hk
  unfold lookOf at hk
  cases hd : Δ c with
  | some r =>
    rw [hd] at hk
    cases hk
    exact hΔ c r hd
  | none =>
    rw [hd] at hk
    cases hg : Γ c with
    | some r =>
      rw [hg] at hk
      cases hk
      exact hΓ c r hg
    | none =>
      rw [hg] at hk
      by_cases hc : (c == ``List.rec) = true
      · rw [if_pos hc] at hk
        cases hk
        have : c = ``List.rec := by simpa using hc
        subst this
        exact hr
      · rw [if_neg hc] at hk
        cases hk

/-! ## evaluators -/

def unfoldL (lk : Look) (e : Expr) : Option (Option Expr) :=
  match appFn e with
  | .const c ls =>
    match lk c with
    | none => none
    | some (.defn r) => some (if r.lps.length = ls.length then some (betaApp (instLE r.lps ls r.value) (appArgs e)) else none)
    | some _ => some none
  | _ => some none

def iotaL (lk : Look) (s : Name) (j : Nat) (y : Expr) : Option (Option Expr) :=
  match appFn y with
  | .const c _ =>
    match lk c with
    | none => none
    | some (.ctor r) => some (if r.induct == s && (appArgs y).length == r.numParams + r.numFields then (appArgs y)[r.numParams + j]? else none)
    | some _ => some none
  | _ => some none

def whStepL (lk : Look) : Expr → Option (Option Expr)
  | .letE _ _ v b _ => some (some (instE b v 0))
  | .proj s j y =>
    match whStepL lk y with
    | none => none
    | some (some y') => some (some (.proj s j y'))
    | some none => iotaL lk s j y
  | .app f a =>
    match f with
    | .lam _ _ b _ => some (some (instE b a 0))
    | .letE _ _ v b _ => some (some (.app (instE b v 0) a))
    | _ => (whStepL lk f).map fun o => o.map fun f' => .app f' a
  | x => unfoldL lk x

def recMajorL (lk : Look) : Nat → Expr → Option (Option Expr)
  | 0, _ => some none
  | n + 1, x =>
    match appFn x with
    | .const c _ =>
      if c == ``List.nil || c == ``List.cons then some (some x)
      else
        match whStepL lk x with
        | none => none
        | some none => some none
        | some (some x') => recMajorL lk n x'
    | _ =>
      match whStepL lk x with
      | none => none
      | some none => some none
      | some (some x') => recMajorL lk n x'

def recStepCoreL (lk : Look) (c : Name) (ls : List Level) : List Expr → Option (Option Expr)
  | a0 :: mot :: nilc :: consc :: major :: extra =>
    match recMajorL lk 256 major with
    | none => none
    | some none => some none
    | some (some m) =>
      some (match appFn m, appArgs m with
      | .const k _, [_] => if k == ``List.nil then some (betaApp nilc extra) else none
      | .const k _, [_, h, t] =>
        if k == ``List.cons then some (betaApp consc ([h, t, mkApps (.const c ls) [a0, mot, nilc, consc, t]] ++ extra)) else none
      | _, _ => none)
  | _ => some none

def recStepL (lk : Look) (e : Expr) : Option (Option Expr) :=
  match appFn e with
  | .const c ls =>
    if c == ``List.rec then
      match lk c with
      | none => none
      | some .recl => recStepCoreL lk c ls (appArgs e)
      | some _ => some none
    else some none
  | _ => some none

def whStepRL (lk : Look) : Expr → Option (Option Expr)
  | .letE _ _ v b _ => some (some (instE b v 0))
  | .proj s j y =>
    match whStepRL lk y with
    | none => none
    | some (some y') => some (some (.proj s j y'))
    | some none =>
      match iotaL lk s j y with
      | none => none
      | some (some r) => some (some r)
      | some none =>
        match recStepL lk y with
        | none => none
        | some o => some (o.map fun y' => .proj s j y')
  | .app f a =>
    match f with
    | .lam _ _ b _ => some (some (instE b a 0))
    | .letE _ _ v b _ => some (some (.app (instE b v 0) a))
    | _ => (whStepRL lk f).map fun o => o.map fun f' => .app f' a
  | x => unfoldL lk x

def headRedexRL (lk : Look) (e : Expr) : Option (Option Expr) :=
  match appFn e, appArgs e with
  | .lam .., _ :: _ => some (some (betaApp (appFn e) (appArgs e)))
  | .letE _ _ v b _, _ :: _ => some (some (mkApps (instE b v 0) (appArgs e)))
  | .proj s j y, _ :: _ => (whStepRL lk (.proj s j y)).map fun o => o.map fun h' => mkApps h' (appArgs e)
  | _, _ => some none

/-! ## soundness -/

theorem unfoldL_sound {env : Environment} {lk : Look} (h : EnvLk env lk) {e : Expr} {o : Option Expr} (ho : unfoldL lk e = some o) : unfoldAt env e = o := by
  unfold unfoldL at ho
  unfold unfoldAt
  revert ho
  cases hc : appFn e with
  | const c ls =>
    intro ho
    simp only at ho ⊢
    cases hk : lk c with
    | none => rw [hk] at ho; simp at ho
    | some k =>
      rw [hk] at ho
      have hok := h c k hk
      cases k with
      | defn r =>
        obtain ⟨d, hd, hl, hv⟩ := hok
        simp only [hd, hl, hv]
        exact Option.some.inj ho
      | ctor r =>
        obtain ⟨cv, hd, _⟩ := hok
        simp only [hd]
        exact Option.some.inj ho
      | recl =>
        obtain ⟨ri, hd⟩ := hok
        simp only [hd]
        exact Option.some.inj ho
  | _ => intro ho; simp only at ho ⊢; exact Option.some.inj ho

theorem iotaL_sound {env : Environment} {lk : Look} (h : EnvLk env lk) {s : Name} {j : Nat} {y : Expr} {o : Option Expr} (ho : iotaL lk s j y = some o) : iotaAt env s j y = o := by
  unfold iotaL at ho
  unfold iotaAt
  revert ho
  cases hc : appFn y with
  | const c ls =>
    intro ho
    simp only at ho ⊢
    cases hk : lk c with
    | none => rw [hk] at ho; simp at ho
    | some k =>
      rw [hk] at ho
      have hok := h c k hk
      cases k with
      | ctor r =>
        obtain ⟨cv, hd, h1, h2, h3⟩ := hok
        simp only [hd, h1, h2, h3]
        exact Option.some.inj ho
      | defn r =>
        obtain ⟨d, hd, _⟩ := hok
        simp only [hd]
        exact Option.some.inj ho
      | recl =>
        obtain ⟨ri, hd⟩ := hok
        simp only [hd]
        exact Option.some.inj ho
  | _ => intro ho; simp only at ho ⊢; exact Option.some.inj ho

theorem whStepL_sound {env : Environment} {lk : Look} (h : EnvLk env lk) : ∀ (e : Expr) {o : Option Expr}, whStepL lk e = some o → whStep env e = o := by
  intro e
  induction e with
  | letE n t v b nd _ _ _ => intro o ho; simp only [whStepL] at ho; simp only [whStep]; exact Option.some.inj ho
  | proj s j y ih =>
    intro o ho
    simp only [whStepL] at ho
    simp only [whStep]
    cases hy : whStepL lk y with
    | none => rw [hy] at ho; simp at ho
    | some oy =>
      rw [hy] at ho
      have := ih hy
      rw [this]
      cases oy with
      | some y' => simp at ho; simp [← ho]
      | none => simp only at ho; exact iotaL_sound h ho
  | app f a ihf _ =>
    intro o ho
    simp only [whStepL] at ho
    simp only [whStep]
    cases f with
    | lam n t b bi => simp at ho; simp [← ho]
    | letE n t v b nd => simp at ho; simp [← ho]
    | bvar i => cases hf : whStepL lk (.bvar i) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | fvar i => cases hf : whStepL lk (.fvar i) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | mvar i => cases hf : whStepL lk (.mvar i) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | sort i => cases hf : whStepL lk (.sort i) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | const i l => cases hf : whStepL lk (.const i l) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | app g b => cases hf : whStepL lk (.app g b) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | forallE n t b bi => cases hf : whStepL lk (.forallE n t b bi) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | lit l => cases hf : whStepL lk (.lit l) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | mdata m b => cases hf : whStepL lk (.mdata m b) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
    | proj s j y => cases hf : whStepL lk (.proj s j y) <;> simp [hf] at ho <;> (rename_i oo; have := ihf hf; simp [this, ← ho])
  | bvar i => intro o ho; exact unfoldL_sound h ho
  | fvar i => intro o ho; exact unfoldL_sound h ho
  | mvar i => intro o ho; exact unfoldL_sound h ho
  | sort i => intro o ho; exact unfoldL_sound h ho
  | const i l => intro o ho; exact unfoldL_sound h ho
  | lam n t b bi _ _ => intro o ho; exact unfoldL_sound h ho
  | forallE n t b bi _ _ => intro o ho; exact unfoldL_sound h ho
  | lit l => intro o ho; exact unfoldL_sound h ho
  | mdata m b _ => intro o ho; exact unfoldL_sound h ho

end Tools.ShippingFGCircuitS1wTbl
