import Tools.ShippingBindingsSoundness

/-! # The shipping expression cache

`translateExprToWire` (Sparkle/Compiler/Elab.lean) memoises successful
translations in `CompilerState.exprCache : Option (IO.Ref (ExprStructMap String))`.
A hit returns a previously emitted wire name WITHOUT re-running the handler
chain, so the cache is only sound if the remembered wire still denotes the same
source value in the current scope.

The danger the handoff names is real and is NOT that the key changes: the
eligibility test is `!isNamed && !e.isFVar && !isTopLevel`, which excludes a
free variable ITSELF but not an expression CONTAINING one. So `x ^^^ a` is
cacheable even though its value depends on whatever `x` is bound to.

What makes this sound is a property of the key, not of the expression: the
compiler introduces every scoped binder with `withLocalDecl`, i.e.
`Lean.Meta.withLocalDeclD`, which mints a FRESH `FVarId` on each entry
(measured: three successive entries give `_uniq.1433/1434/1435`, and two
structurally identical bodies built in different scopes compare unequal).
`ExprStructMap` keys on `ExprStructEq`, whose `BEq` is `Expr.equal` — a
structural comparison that distinguishes `fvar` by id. Hence an expression
mentioning a binder from an exited scope cannot collide with the same shape
under a different binder: the keys differ.

`Expr.equal` is `opaque` in core, so nothing below unfolds it. Instead the
required property is stated as a hypothesis (`KeyFaithful`) and discharged by
the caller; that keeps the obligation visible rather than hiding it in a
`native_decide`. The theorems are about the cache's transition rules and what a
hit guarantees, given that hypothesis.

A consequence worth recording, found while proving this: core provides NO
`EquivBEq ExprStructEq` / `LawfulHashable ExprStructEq` instance — `#synth`
fails — precisely because `Expr.equal` is opaque. So `Std.HashMap.get?_insert`
and friends, which require those, are NOT available for this cache. The
insertion rule below therefore takes the lookup behaviour it needs as an
explicit hypothesis (`InsertSpec`) instead of silently assuming a lawful key.
Discharging `InsertSpec` and `KeyFaithful` for the real `Expr` key is an open
obligation on the core-level `Expr.equal`, not something this file hides.

Scope. These are rules for the cache table, in the same style as the binding
rules of `ShippingBindingsSoundness`. They do NOT claim that every MetaM
handler maintains the invariant, nor that the two insertion sites in the
shipping compiler are the only ones. Those remain open obligations, recorded in
docs/ShippingCompiler-Soundness.md. -/

namespace Tools.ShippingCacheSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingScalarSoundness Tools.ShippingAllocationSoundness
open Tools.ShippingBindingsSoundness

/-- The cache as the shipping compiler stores it. -/
abbrev Cache := Lean.ExprStructMap String

/-- Denotation of a source expression under a valuation of its free variables.
Kept abstract: the point here is the cache discipline, not a source semantics.
`sourceValue e` is the value the compiled wire for `e` must carry. -/
abbrev SourceValue := Lean.Expr → Nat

/-- A cached entry is honest: the remembered wire carries the source value of
the key, in the current environment. -/
def EntryAgrees (env : Env) (sourceValue : SourceValue) (key : Lean.Expr)
    (wire : String) : Prop := env wire = sourceValue key

/-- Every entry of the cache is honest. -/
def CacheAgrees (cache : Cache) (env : Env) (sourceValue : SourceValue) : Prop :=
  ∀ key wire, cache.get? ⟨key⟩ = some wire → EntryAgrees env sourceValue key wire

/-- Every cached wire is reserved, so a later allocation cannot reuse its name
and silently overwrite a live cached value. -/
def CacheReserved (cache : Cache) (used : Std.HashSet String) : Prop :=
  ∀ key wire, cache.get? ⟨key⟩ = some wire → used.contains wire = true

/-- The key discipline the fresh-binder argument provides: structurally equal
keys denote the same source value. This is what rules out a stale hit across a
scope change — a body mentioning an exited binder is a DIFFERENT key, because
`withLocalDecl` mints a fresh `FVarId` each entry.

Stated as a hypothesis because `Lean.Expr.equal` is `opaque`. -/
def KeyFaithful (sourceValue : SourceValue) : Prop :=
  ∀ a b : Lean.Expr, (ExprStructEq.mk a == ExprStructEq.mk b) = true →
    sourceValue a = sourceValue b

/-- The cache invariant carried by the compiler state. -/
structure Valid (cache : Cache) (env : Env) (sourceValue : SourceValue)
    (used : Std.HashSet String) : Prop where
  agrees : CacheAgrees cache env sourceValue
  reserved : CacheReserved cache used

/-! ## What a hit guarantees -/

/-- A cache hit returns a wire carrying the key's source value. This is the
theorem the `translateExprToWire` shim needs: it returns `w` without running
the handler chain, and this says `w` is still correct. -/
theorem Valid.hit {cache : Cache} {env : Env} {sourceValue : SourceValue}
    {used : Std.HashSet String} (h : Valid cache env sourceValue used)
    {key : Lean.Expr} {wire : String} (hit : cache.get? ⟨key⟩ = some wire) :
    env wire = sourceValue key := by
  have := h.agrees key wire hit
  simpa [EntryAgrees] using this

/-- A hit on the mdata-stripped fallback key (the shipping lookup retries with
`e.consumeMData`) is equally sound, PROVIDED stripping preserves the source
value. That proviso is exactly the `strip` hypothesis, and it is the honest
place for it: `consumeMData` is a metadata operation, and the claim that it
does not change the denotation belongs to the source semantics, not here. -/
theorem Valid.hit_stripped {cache : Cache} {env : Env} {sourceValue : SourceValue}
    {used : Std.HashSet String} (h : Valid cache env sourceValue used)
    {key : Lean.Expr} {wire : String}
    (strip : sourceValue key.consumeMData = sourceValue key)
    (hit : cache.get? ⟨key.consumeMData⟩ = some wire) :
    env wire = sourceValue key := by
  have hv := h.agrees _ wire hit
  simp only [EntryAgrees] at hv
  rw [hv, strip]

/-- A hit under a key that is only structurally equal to the query is sound
when the keys are faithful. This is the step that a scope change would break if
binders were reused: with fresh binders the premise simply fails for a stale
entry, so no unsound hit is possible. -/
theorem Valid.hit_congr {cache : Cache} {env : Env} {sourceValue : SourceValue}
    {used : Std.HashSet String} (h : Valid cache env sourceValue used)
    (faithful : KeyFaithful sourceValue)
    {query key : Lean.Expr} {wire : String}
    (hkey : (ExprStructEq.mk query == ExprStructEq.mk key) = true)
    (hit : cache.get? ⟨key⟩ = some wire) :
    env wire = sourceValue query := by
  have hq : sourceValue query = sourceValue key := faithful _ _ hkey
  have hv := h.agrees key wire hit
  simp only [EntryAgrees] at hv
  rw [hv, hq]

/-! ## Transition rules: the two insertion sites -/

/-- The lookup behaviour of `insert` that the rules below need. With a lawful
key this is `Std.HashMap.get?_insert`; `ExprStructEq` has no such instance (see
the header), so it is a hypothesis about the actual table. -/
def InsertSpec (cache : Cache) (key : Lean.Expr) (wire : String) : Prop :=
  ∀ k : Lean.Expr, (cache.insert ⟨key⟩ wire).get? ⟨k⟩ =
    if (ExprStructEq.mk key == ExprStructEq.mk k) = true then some wire
    else cache.get? ⟨k⟩

/-- Inserting a freshly translated result keeps the invariant, given that the
new wire really carries the key's value and is reserved. This is the shim's
write-back at the end of `translateExprToWire`.

`KeyFaithful` is required and the reason is the substance of this file: the
table returns the inserted wire for any key STRUCTURALLY equal to the inserted
one, not only for the literal same `Expr`. Soundness of the entry for those
neighbours is precisely faithfulness of the key. -/
theorem Valid.insert {cache : Cache} {env : Env} {sourceValue : SourceValue}
    {used : Std.HashSet String} (h : Valid cache env sourceValue used)
    (faithful : KeyFaithful sourceValue)
    (key : Lean.Expr) (wire : String)
    (spec : InsertSpec cache key wire)
    (hvalue : env wire = sourceValue key)
    (hused : used.contains wire = true) :
    Valid (cache.insert ⟨key⟩ wire) env sourceValue used := by
  constructor
  · intro k w hk
    rw [spec k] at hk
    by_cases hbeq : (ExprStructEq.mk key == ExprStructEq.mk k) = true
    · rw [if_pos hbeq] at hk
      have hw : w = wire := (Option.some.inj hk).symm
      subst hw
      have hkv : sourceValue key = sourceValue k := faithful _ _ hbeq
      show env w = sourceValue k
      rw [← hkv]; exact hvalue
    · rw [if_neg hbeq] at hk
      exact h.agrees k w hk
  · intro k w hk
    rw [spec k] at hk
    by_cases hbeq : (ExprStructEq.mk key == ExprStructEq.mk k) = true
    · rw [if_pos hbeq] at hk
      have hw : w = wire := (Option.some.inj hk).symm
      subst hw; exact hused
    · rw [if_neg hbeq] at hk
      exact h.reserved k w hk

/-- Reserving further names (the allocator's `used.insert`) preserves the cache
invariant: existing entries stay reserved. Together with `Valid.insert` this is
what lets allocation and caching interleave without a stale-name hazard. -/
theorem Valid.reserve {cache : Cache} {env : Env} {sourceValue : SourceValue}
    {used : Std.HashSet String} (h : Valid cache env sourceValue used)
    (name : String) : Valid cache env sourceValue (used.insert name) := by
  refine ⟨h.agrees, ?_⟩
  intro key wire hk
  simp [Std.HashSet.contains_insert, h.reserved key wire hk]

/-- An empty cache is valid for any environment — `CircuitM`'s per-synthesis
`IO.mkRef {}` starts here, so each synthesis begins in the invariant. -/
theorem valid_empty (env : Env) (sourceValue : SourceValue)
    (used : Std.HashSet String) :
    Valid (∅ : Cache) env sourceValue used := by
  constructor
  · intro key wire hk; simp at hk
  · intro key wire hk; simp at hk

/-! ## Writing a wire that is not cached

The hazard a cache adds to the allocator is that emitting to a wire could
change the value of a name some entry already depends on. The allocator only
ever writes FRESH names, and `CacheReserved` says every cached wire is already
reserved; so a fresh write cannot touch one. -/

/-- Updating the environment at a name that is not reserved leaves every cached
entry's value unchanged. -/
theorem Valid.write_fresh {cache : Cache} {env : Env} {sourceValue : SourceValue}
    {used : Std.HashSet String} (h : Valid cache env sourceValue used)
    (name : String) (value : Nat) (fresh : used.contains name = false) :
    Valid cache (fun w => if w = name then value else env w) sourceValue used := by
  refine ⟨?_, h.reserved⟩
  intro key wire hk
  have hres : used.contains wire = true := h.reserved key wire hk
  have hne : wire ≠ name := by
    intro heq; rw [heq] at hres; simp [fresh] at hres
  have hv := h.agrees key wire hk
  simp only [EntryAgrees] at hv
  simpa [EntryAgrees, hne] using hv

/-! ## Connection to the actual compiler

The rules above are about the table. These tie them to the real code in
`Sparkle/Compiler/Elab.lean` rather than to a model of it. -/

/-- The shipping eligibility test, verbatim from `translateExprToWire`. -/
def cacheable (e : Lean.Expr) (isTopLevel isNamed : Bool) : Bool :=
  !isNamed && !e.isFVar && !isTopLevel

/-- The fact that motivates this whole file: eligibility rejects a bare free
variable but ACCEPTS an application that contains one. So cache soundness
cannot rest on "cached expressions are closed" — it rests on the key. -/
theorem cacheable_open_application (f x : Lean.Expr) (hf : ¬ f.isFVar)
    (hx : x.isFVar) :
    cacheable (.app f x) false false = true ∧ x.isFVar = true := by
  refine ⟨?_, by simpa using hx⟩
  simp [cacheable, Lean.Expr.isFVar]

/-- A free variable itself is never cached, so the lexically scoped `varMap`
remains the only resolver for it. -/
theorem not_cacheable_fvar (id : Lean.FVarId) (isTopLevel isNamed : Bool) :
    cacheable (.fvar id) isTopLevel isNamed = false := by
  simp [cacheable, Lean.Expr.isFVar]

/-- Top-level and user-named translations bypass the cache, matching the
implementation's two remaining guards. -/
theorem not_cacheable_named (e : Lean.Expr) (isTopLevel : Bool) :
    cacheable e isTopLevel true = false := by simp [cacheable]

theorem not_cacheable_toplevel (e : Lean.Expr) (isNamed : Bool) :
    cacheable e true isNamed = false := by simp [cacheable, Bool.and_comm]

/-- The compiler reads the cache out of its reader state; `CircuitM.init`-based
synthesis installs a fresh `IO.Ref`. This is the state projection the shim
uses, as an equation on the actual structure. -/
theorem exprCache_of_state (state : CompilerState) :
    (CompilerM.getCompilerState state).run = fun s => pure (state, s) := rfl

/-- Each synthesis starts from an empty table, so `valid_empty` applies at
entry: the invariant is established, not assumed, at the start of a synthesis.
(The shipping code builds the ref with `IO.mkRef ({} : ExprStructMap String)`.) -/
theorem valid_at_synthesis_start (env : Env) (sourceValue : SourceValue)
    (used : Std.HashSet String) :
    Valid (∅ : Cache) env sourceValue used := valid_empty env sourceValue used

end Tools.ShippingCacheSoundness
