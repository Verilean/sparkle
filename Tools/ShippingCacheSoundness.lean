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
and friends, which require those, are NOT available for this cache.

Two things follow, and they are kept apart below.

* The HashMap half is NOT an assumption about hash maps: `insertSpec_of_lawful`
  proves the insert/lookup equation outright for every lawful key. What is
  missing is only lawfulness of the `Expr` key, so `InsertSpec` remains a
  hypothesis for the shipping table alone.
* The key half is split into `KeySound` (equal keys are equal expressions — a
  fact about `Expr.equal`) and `StableBetween` (the denotation did not move
  between write and read — a fact about the compiler). `KeyFaithful` follows
  from `KeySound` by `keyFaithful_of_keySound`.

`KeySound` is NOT provable while the cache keys on `Expr.equal`: reducing it
lands on the opaque constant, and the goal can only be closed by `sorry`
(checked). It is therefore a design obligation, not a proof obligation — the
plan for discharging it is in docs/ShippingCompiler-Soundness.md. Note also
that a comparison returning `false` on `mdata` is NOT an option: it is
irreflexive, so `EquivBEq` fails and every HashMap lemma is lost with it
(checked).

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

/-! ### The key hypothesis, split in two

Lumping these together hid which half is a statement about `Expr` equality and
which is a statement about the COMPILER's scoping. They are different
obligations with different owners, so they are separated here. -/

/-- (i) Key equality is real equality: the table's `BEq` on keys identifies only
structurally identical expressions.

This is a property of `Lean.Expr.equal` alone — no compiler notion enters. It
is exactly `LawfulBEq`-style soundness for the key, and it is the statement that
`Expr.equal`'s opacity blocks today. -/
def KeySound : Prop :=
  ∀ a b : Lean.Expr, (ExprStructEq.mk a == ExprStructEq.mk b) = true → a = b

/-- (ii) A cached entry is still about the same value when it is READ as when it
was WRITTEN. This is the scope/value-stability half, and it is a property of the
compiler, not of `Expr`: between the insertion and the hit, the environment and
the source valuation of that key must not have moved.

Keeping it separate matters because (i) alone does NOT give it: two occurrences
of the same closed key at different program points still need their denotation
to agree, which is a fact about how the compiler reuses wires. -/
def StableBetween (envAtWrite envAtRead : Env) (valueAtWrite valueAtRead : SourceValue)
    (key : Lean.Expr) (wire : String) : Prop :=
  envAtWrite wire = envAtRead wire ∧ valueAtWrite key = valueAtRead key

/-- The combined property the rules below consume. `KeyFaithful` follows from
`KeySound` (`keyFaithful_of_keySound`), so the `Expr`-level obligation is now
isolated in a single, purely syntactic statement. -/
def KeyFaithful (sourceValue : SourceValue) : Prop :=
  ∀ a b : Lean.Expr, (ExprStructEq.mk a == ExprStructEq.mk b) = true →
    sourceValue a = sourceValue b

/-- Key soundness is enough for faithfulness, for ANY valuation. Proved, so the
open obligation shrinks from "for every source valuation, equal keys agree" to
the single syntactic fact `KeySound`. -/
theorem keyFaithful_of_keySound (sound : KeySound) (sourceValue : SourceValue) :
    KeyFaithful sourceValue := by
  intro a b hab
  exact congrArg sourceValue (sound a b hab)

/-- Stability is reflexive when nothing moved between write and read — the case
the shipping cache is in when a later leaf revisits a sub-expression within the
same synthesis without re-entering a binder for it. -/
theorem stableBetween_refl (env : Env) (sourceValue : SourceValue)
    (key : Lean.Expr) (wire : String) :
    StableBetween env env sourceValue sourceValue key wire := ⟨rfl, rfl⟩

/-- A hit is correct in the READ environment given the entry was correct at
write time and the two are stable. This is the statement that actually covers
"insert here, use there", which `Valid.hit` alone does not: `Valid` is indexed
by one environment, whereas the cache spans the whole synthesis. -/
theorem hit_across (envW envR : Env) (valW valR : SourceValue)
    (key : Lean.Expr) (wire : String)
    (written : envW wire = valW key)
    (stable : StableBetween envW envR valW valR key wire) :
    envR wire = valR key := by
  obtain ⟨henv, hval⟩ := stable
  rw [← henv, written, hval]

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
the header), so for the SHIPPING table it is a hypothesis.

It is not, however, an assumption about HashMaps in general:
`insertSpec_of_lawful` below proves it outright for every lawful key, so the
only thing still missing is lawfulness of the `Expr` key itself. That is the
single remaining gap, and `docs/ShippingCompiler-Soundness.md` states the plan
for closing it. -/
def InsertSpec (cache : Cache) (key : Lean.Expr) (wire : String) : Prop :=
  ∀ k : Lean.Expr, (cache.insert ⟨key⟩ wire).get? ⟨k⟩ =
    if (ExprStructEq.mk key == ExprStructEq.mk k) = true then some wire
    else cache.get? ⟨k⟩

/-- `InsertSpec` is a THEOREM, not an assumption, for any key with a lawful
`BEq`. Proved with the standard axioms only. This removes "the HashMap might
not behave this way" from the trusted surface: what remains is exactly the
lawfulness of the key type the shipping cache uses. -/
theorem insertSpec_of_lawful {K V : Type} [BEq K] [Hashable K] [EquivBEq K]
    [LawfulHashable K] (m : Std.HashMap K V) (key : K) (v : V) (k : K) :
    (m.insert key v).get? k = if (key == k) = true then some v else m.get? k := by
  rw [Std.HashMap.get?_insert]

/-- The shape `Valid.insert` consumes, for a lawful key: the table's own
behaviour, with nothing assumed. Instantiating this at the shipping cache is
blocked ONLY by `EquivBEq ExprStructEq`. -/
theorem insertSpec_holds {K V : Type} [BEq K] [Hashable K] [EquivBEq K]
    [LawfulHashable K] (m : Std.HashMap K V) (key : K) (v : V) :
    ∀ k : K, (m.insert key v).get? k =
      if (key == k) = true then some v else m.get? k :=
  fun k => insertSpec_of_lawful m key v k

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
