import Tools.ShippingSettledSoundness

/-! # Dependency order of shipping builder operations

Reservation is not computation: binary translation allocates its result before
translating its operands. `Pending` records absence from the existing body,
even when a name is already reserved. These proofs follow the actual allocator,
emitter and literal handler; full recursive translation remains separate.
-/
namespace Tools.ShippingTranslationOrder
open Lean Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.Compiler.Elab Tools.ShippingTranslateSoundness
open Tools.ShippingSettledSoundness

/-- Every name read or written by the current body. -/
def footprint (body : List Stmt) : List String :=
  body.flatMap fun st => stmtWrites st ++ stmtReads st

theorem footprint_cons (l : String) (r : Sparkle.IR.AST.Expr) (body : List Stmt) :
    footprint (.assign l r :: body) = l :: (refsOf r ++ footprint body) := by
  simp [footprint, stmtWrites, stmtReads]

theorem writes_mem_footprint {body : List Stmt} {x : String}
    (h : x ∈ writesOf body) : x ∈ footprint body := by
  obtain ⟨st, hs, hx⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨st, hs, List.mem_append_left _ hx⟩

theorem acyclic_snoc {body : List Stmt} {l : String} {r : Sparkle.IR.AST.Expr}
    (ha : Acyclic body) (hf : l ∉ footprint body) (hr : l ∉ refsOf r) :
    Acyclic (body ++ [.assign l r]) := by
  induction ha with
  | nil =>
    apply Acyclic.cons
    · simp [writesOf]
    · intro x hx; exact ⟨fun he => hr (he ▸ hx), by simp [writesOf]⟩
    · exact .nil
  | @cons a e rest ht hre ha ih =>
    have hf' : l ≠ a ∧ l ∉ refsOf e ∧ l ∉ footprint rest := by
      simpa [footprint_cons] using hf
    have hw : writesOf (rest ++ [.assign l r]) = writesOf rest ++ [l] := by
      rw [writesOf_append]; rfl
    apply Acyclic.cons
    · change a ∉ writesOf (rest ++ [.assign l r])
      rw [hw]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨ht, Ne.symm hf'.1⟩
    · intro x hx
      refine ⟨(hre x hx).1, ?_⟩
      change x ∉ writesOf (rest ++ [.assign l r])
      rw [hw]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨(hre x hx).2, fun he => hf'.2.1 (he ▸ hx)⟩
    · exact ih hf'.2.2

/-- The body is stored in reverse emission order by CircuitM. -/
def OrderInv (s : CircuitState) : Prop :=
  Acyclic s.module.body.reverse ∧
    ∀ x ∈ footprint s.module.body, s.usedNames.contains x = true

/-- A reserved result can still be pending: nothing has read or assigned it. -/
def Pending (s : CircuitState) (name : String) : Prop := name ∉ footprint s.module.body

theorem footprint_reverse_mem (body : List Stmt) (x : String) :
    x ∈ footprint body.reverse ↔ x ∈ footprint body := by
  simp [footprint, List.mem_flatMap]

theorem OrderInv.empty {s : CircuitState} (hb : s.module.body = []) : OrderInv s := by
  constructor
  · rw [hb]; exact .nil
  · simp [hb, footprint]

theorem OrderInv.transfer {s t : CircuitState} (h : OrderInv s)
    (hb : t.module.body = s.module.body)
    (hu : ∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true) : OrderInv t :=
  ⟨by rw [hb]; exact h.1, fun x hx => hu x (h.2 x (hb ▸ hx))⟩

/-- Actual allocation preserves order and establishes a pending result.
It deliberately does not assert that the reserved name is already computed. -/
theorem makeWire_order {ctx : CompilerState} {s t : CircuitState}
    {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool} {name : String}
    (h : Returns (CompilerM.makeWire hint ty named) ctx s name t) (hi : OrderInv s) :
    OrderInv t ∧ Pending t name ∧ t.usedNames.contains name = true := by
  obtain ⟨hn, ht⟩ := makeWire_returns h
  obtain ⟨hf, hu, hb, _⟩ := CircuitM.makeWire_spec hint ty named s
  rw [← hn] at hf hu
  rw [← ht] at hu hb
  have hp : Pending t name := by
    intro hm
    have hh := hi.2 name (hb ▸ hm)
    rw [hf] at hh; cases hh
  exact ⟨hi.transfer hb (fun x hx => by rw [hu]; simp [Std.HashSet.contains_insert, hx]),
    hp, by rw [hu]; simp [Std.HashSet.contains_insert]⟩

/-- Actual assignment emission preserves order when the pending target is
not read by its own RHS. Operands must be reserved, not assumed computed. -/
theorem emitAssign_order {ctx : CompilerState} {s t : CircuitState}
    {name : String} {rhs : Sparkle.IR.AST.Expr} {u : Unit}
    (h : Returns (CompilerM.emitAssign name rhs) ctx s u t)
    (hi : OrderInv s) (hp : Pending s name)
    (hu : s.usedNames.contains name = true)
    (hr : name ∉ refsOf rhs)
    (href : ∀ x ∈ refsOf rhs, s.usedNames.contains x = true) : OrderInv t := by
  have ht := emitAssign_returns h
  have hb : t.module.body = .assign name rhs :: s.module.body := by
    rw [ht, emitAssign_body_cons]
  have hus : t.usedNames = s.usedNames := by rw [ht, emitAssign_usedNames]
  constructor
  · rw [hb, List.reverse_cons]
    exact acyclic_snoc hi.1 (fun hm => hp ((footprint_reverse_mem _ _).mp hm)) hr
  · intro x hx
    rw [hb, footprint_cons] at hx
    rw [hus]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · rcases List.mem_append.mp hx with hx | hx
      · exact href x hx
      · exact hi.2 x hx

/-- The shipping literal handler, including the unsupported-payload branch.
No source denotation, width agreement, or recursion hypothesis is needed for
this structural result. -/
theorem translateSignalPureLiteral_order {ctx : CompilerState} {s t : CircuitState}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {result : Option String}
    (h : Returns (translateSignalPureLiteral? args hint named) ctx s result t)
    (hi : OrderInv s) : OrderInv t ∧
      (∀ name, result = some name → name ∈ writesOf t.module.body) := by
  unfold translateSignalPureLiteral? at h
  split at h
  · obtain ⟨name, sA, hm, hrest⟩ := Returns.bind h
    obtain ⟨u, sB, he, hret⟩ := Returns.bind hrest
    obtain ⟨hr, ht⟩ := Returns.pure hret
    obtain ⟨hiA, hp, hu⟩ := makeWire_order hm hi
    have hiB := emitAssign_order he hiA hp hu (by simp [refsOf]) (by simp [refsOf])
    refine ⟨ht ▸ hiB, ?_⟩
    intro name' heq
    rw [hr] at heq; cases heq
    rw [ht, emitAssign_returns he, emitAssign_body_cons, writes_cons]
    simp
  · obtain ⟨hr, ht⟩ := Returns.pure h
    exact ⟨ht ▸ hi, fun _ heq => by rw [hr] at heq; cases heq⟩

/-- Validated cache lookup does not emit any statement; order is unchanged.
The readiness of a returned cached wire is a separate record invariant. -/
theorem cacheLookup_order {ctx : CompilerState} {s t : CircuitState}
    {e : Lean.Expr} {result : Option String}
    (h : Returns (cacheLookupValidated e) ctx s result t) (hi : OrderInv s) : OrderInv t := by
  rw [(cacheLookupValidated_returns h).1]; exact hi

/-- Only leaves, not the recursive binary branch. -/
def Leaf (e : Lean.Expr) : Prop := e.isFVar = true ∨
  ∃ us, e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us

theorem core_leaf_order {rec : TranslateFn} {ctx : CompilerState} {s t : CircuitState}
    {e : Lean.Expr} {hint : String} {named : Bool} {result : Option String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hl : Leaf e) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateCore rec e hint false named) ctx s result t)
    (hi : OrderInv s) : OrderInv t ∧ ∃ name, result = some name := by
  cases hd with
  | @fvar id _ _ hv =>
    obtain ⟨hr, ht⟩ := lookupVar_returns h
    obtain ⟨name, hn, _⟩ := hb id _ _ hv
    exact ⟨ht ▸ hi, name, hr.trans hn⟩
  | pureLit hfn hback hlit =>
    have hleaf := h
    unfold translateCore at hleaf
    split at hleaf
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at hleaf
      simp only [beq_self_eq_true, if_true] at hleaf
      have ho := (translateSignalPureLiteral_order hleaf hi).1
      have hs := hleaf
      unfold translateSignalPureLiteral? at hs
      rw [hback] at hs
      simp only [Option.bind_some, hlit] at hs
      obtain ⟨name, _, _, rest⟩ := Returns.bind hs
      obtain ⟨_, _, _, ret⟩ := Returns.bind rest
      exact ⟨ho, name, (Returns.pure ret).1⟩
  | binary hfn hop _ _ _ _ =>
    rcases hl with hf | ⟨us, hp⟩
    · rw [isFVar_false_of_const hfn] at hf; cases hf
    · rw [hp] at hfn; cases hfn
      rw [signalBinOpOf_pure] at hop; cases hop

theorem core_leaf_continuation_order {rec : TranslateFn} {ctx : CompilerState}
    {s t : CircuitState} {e : Lean.Expr} {hint : String} {named c : Bool}
    {K : Option String → CompilerM String} {result : String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hK : ∀ name, K (some name) = if e.isFVar = true then pure name else
      (recordTranslation e name c >>= fun _ => pure name))
    (hd : Denotes ρ e n x) (hl : Leaf e) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateCore rec e hint false named >>= K) ctx s result t)
    (hi : OrderInv s) : OrderInv t := by
  obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
  obtain ⟨hic, name, hr⟩ := core_leaf_order hd hl hb hc hi
  rw [hr, hK] at hk
  split at hk
  · exact (Returns.pure hk).2 ▸ hic
  · obtain ⟨_, sr, hrec, ret⟩ := Returns.bind hk
    have hs := recordTranslation_returns hrec
    have ht := (Returns.pure ret).2
    rw [ht, hs]
    exact hic

/-- Both cache-hit and cache-miss paths of the actual step preserve the
ordering invariant on leaves, including recording the newly emitted result. -/
theorem step_leaf_order {fallback : TranslateFn → TranslateFn} {rec : TranslateFn}
    {ctx : CompilerState} {s t : CircuitState} {e : Lean.Expr}
    {hint : String} {named : Bool} {result : String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hl : Leaf e) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateStepWith fallback rec e hint false named) ctx s result t)
    (hi : OrderInv s) : OrderInv t := by
  unfold translateStepWith at h
  dsimp only at h
  by_cases hc : ((!named && !e.isFVar && !false) && translateCoreShape e) = true
  · rw [if_pos hc] at h
    obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
    have hs := (cacheLookupValidated_returns hc).1
    split at hk
    · rw [(Returns.pure hk).2, hs]; exact hi
    · rw [hs] at hk
      exact core_leaf_continuation_order (fun _ => rfl) hd hl hb hk hi
  · rw [if_neg hc] at h
    exact core_leaf_continuation_order (fun _ => rfl) hd hl hb h hi

theorem translateFuelFix_leaf_order (fuel : Nat) {ctx : CompilerState} {s t : CircuitState}
    {e : Lean.Expr} {hint : String} {named : Bool} {result : String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hl : Leaf e) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateFuelFix translateStep fuel e hint false named) ctx s result t)
    (hi : OrderInv s) : OrderInv t := by
  cases fuel with
  | zero => exact False.elim (Returns.throw h)
  | succ k => exact step_leaf_order hd hl hb h hi

/-- Order preservation at the REAL recursive entry for inputs and literals.
The binary case remains open; no recursive order hypothesis is assumed here. -/
theorem translateExprToWire_leaf_order {ctx : CompilerState} {s t : CircuitState}
    {e : Lean.Expr} {hint : String} {named : Bool} {result : String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hl : Leaf e) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateExprToWire e hint false named) ctx s result t)
    (hi : OrderInv s) : OrderInv t := by
  exact translateFuelFix_leaf_order translateFuelLimit hd hl hb h hi

/-- The leaf result is used by the semantic theorem: the actual translator's
finalized body has a unique simultaneous solution carrying the source value.
Initial semantic/order invariants are explicit, as at the translator boundary. -/
theorem translateExprToWire_leaf_settled {ctx : CompilerState}
    {we : Sparkle.IR.Semantics.WEnv} {mems : Sparkle.IR.Semantics.MEnv}
    {initial env0 : Sparkle.IR.Semantics.Env} {s t : CircuitState}
    {e : Lean.Expr} {hint : String} {named : Bool} {result : String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hl : Leaf e)
    (h : Returns (translateExprToWire e hint false named) ctx s result t)
    (hi : Inv ctx ρ we mems initial s env0) (ho : OrderInv s) (hw : WidthsAgree we t) :
    ∃ env, IREquations we t.module.finalize.body env ∧
      ExternalValues t.module.finalize.body initial env ∧ env result = x.toNat ∧
      ∀ other, IREquations we t.module.finalize.body other →
        ExternalValues t.module.finalize.body initial other → other = env := by
  obtain ⟨env, hinv, _, _, _, hval⟩ := translateExprToWire_sound hd h hi hw
  have horder := (translateExprToWire_leaf_order hd hl hi.lookup h ho).1
  have ha : Acyclic t.module.finalize.body := horder
  have hq := assign_equations ha hinv.runs
  have hx := assign_frame ha hinv.runs
  exact ⟨env, hq, hx, hval, fun other hq' hx' => equations_unique ha hq' hx' hq hx⟩

end Tools.ShippingTranslationOrder
