import Tools.ShippingUnifiedProtection

/-! # The concatenation spine of the translator's output

`closeLets` walks, from the packed wire, one `assign w = {a, b}` per `let`
port, and asks each operand `a` to be declared at its port's width. This file
proves the translator leaves those statements and declarations: a structural
invariant on the builder state, alongside the semantic contract and the order
invariant of `Tools/ShippingUnifiedProtection.lean`.

* The cache is the real one: `translateRecord : wire → Lean.Expr`. The
  invariant (`RecQ`) says every recorded wire (a) has the links of the
  expression it is recorded for (`SpineQ`): while the expression is a
  canonical concatenation — by the compiler's own recognizer
  `canonicalConcat?`, the one `fallbackKind` dispatches on — the wire is driven
  by a concat statement, whose high operand is DECLARED at the concatenation's
  high width and whose low operand has the links of the low operand
  expression; and (b) is declared at the width of the value its expression
  means (`Meaning`, the existing source meaning — no second description of
  the source).
* Membership, not position: statements and declarations are only ever added
  (`Kept`). That a wire has ONE driver is the order invariant's (`Acyclic`),
  used where the spine is read off the final body.
* Protected names (`P`, the input ports): in use from the start, so no wire
  made later is one of them, and no statement drives one.
* Position and reads, for the order of the let-closed body: statements are
  appended in order (`Ext`: the body only grows at the front of the builder's
  list); every arm's result is a wire it MADE and has DRIVEN (`Last`,
  `Drives`); and the statements emitted for a term read, among the protected
  names, only those in `V` — the wires bound to the variables the term uses
  (`Uses`).
* Every path is covered: a fresh concat (`concat_spec`), a validated-cache
  hit and a miss with its record (`Spec.cached`), an overwrite of a record
  (`St.record`), a bound variable returning an existing wire, and every arm
  that is not a concatenation (`Good` / `Last`, by a walk of its code). -/
namespace Tools.ShippingUnifiedSpine
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTranslationOrder
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingScalarSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires binary_returns core_binary_returns)
open Tools.ShippingMixedRecursion (emit_bool_frame compare_step boolBin_step boolEq_step
  boolNot_step translateBoolUncachedWith_boolBin translateBoolBinary_returns)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingVectorMuxRecursion (emit_vector_frame vector_step vectorMuxUncached_muxE emit_vector_order)
open Tools.ShippingMixedOrderSoundness (emit_bool_order)
open Tools.ShippingUnifiedProtection

/-- The statement the concat arm emits for its result wire. -/
def link (w a b : String) : Stmt := .assign w (.concat [.ref a, .ref b])

/-- `w` is declared at width `n`. -/
def Decl (wires : List Port) (w : String) (n : Nat) : Prop :=
  ∃ ty, ({ name := w, ty := ty } : Port) ∈ wires ∧ ty.bitWidth = n

theorem Decl.mono {wires wires' : List Port} (h : ∀ p ∈ wires, p ∈ wires') {w : String} {n : Nat} :
    Decl wires w n → Decl wires' w n := fun ⟨ty, hm, hw⟩ => ⟨ty, h _ hm, hw⟩

/-- `x` is driven by a statement of `body`, or is a protected name (an input:
never driven). Either way no LATER statement drives it. -/
def Drv (P : String → Prop) (body : List Stmt) (x : String) : Prop :=
  (∃ rhs, Stmt.assign x rhs ∈ body) ∨ P x

theorem Drv.mono {P : String → Prop} {body body' : List Stmt} (h : ∀ st ∈ body, st ∈ body')
    {x : String} : Drv P body x → Drv P body' x
  | .inl ⟨rhs, hm⟩ => .inl ⟨rhs, h _ hm⟩
  | .inr hp => .inr hp

/-- Where a result wire comes from — exactly one of: the expression is NOT a
variable and a statement of `body` drives the wire; or the expression IS a
variable and the wire is the one bound to it (an input: protected, never
driven). -/
def Src (P : String → Prop) (bnd : FVarId → Option String) (body : List Stmt) (e : Lean.Expr)
    (x : String) : Prop :=
  (e.isFVar = false ∧ ∃ rhs, Stmt.assign x rhs ∈ body) ∨
    ∃ id, e = .fvar id ∧ bnd id = some x ∧ P x

theorem Src.mono {P : String → Prop} {bnd : FVarId → Option String} {body body' : List Stmt}
    (h : ∀ st ∈ body, st ∈ body') {e : Lean.Expr} {x : String} : Src P bnd body e x → Src P bnd body' e x
  | .inl ⟨hf, rhs, hm⟩ => .inl ⟨hf, rhs, h _ hm⟩
  | .inr hp => .inr hp

theorem Src.drv {P : String → Prop} {bnd : FVarId → Option String} {body : List Stmt}
    {e : Lean.Expr} {x : String} : Src P bnd body e x → Drv P body x
  | .inl ⟨_, h⟩ => .inl h
  | .inr ⟨_, _, _, hp⟩ => .inr hp

/-- `n` links from `w`, following the expression `e`: while `e` is a canonical
concatenation `hi ++ lo` (the compiler's `canonicalConcat?`), `w` is driven by
a concat statement `{x, y}`, `x` is declared at `hi`'s width and is driven or
is the wire bound to the variable `hi` is (`Src`), and `y` has the links of
`lo`. `bnd` is the binding of variables to wires. -/
def SpineQ (P : String → Prop) (bnd : FVarId → Option String) (wires : List Port)
    (body : List Stmt) : Nat → Lean.Expr → String → Prop
  | 0, _, _ => True
  | n + 1, e, w => ∀ m k a b, canonicalConcat? e = some (m, k, a, b) →
      ∃ x y, link w x y ∈ body ∧ Decl wires x m ∧ Src P bnd body a x ∧
        SpineQ P bnd wires body n b y

theorem SpineQ.mono {P : String → Prop} {bnd : FVarId → Option String}
    {wires wires' : List Port} {body body' : List Stmt}
    (hw : ∀ p ∈ wires, p ∈ wires') (hb : ∀ st ∈ body, st ∈ body') :
    ∀ {n : Nat} {e : Lean.Expr} {w : String},
      SpineQ P bnd wires body n e w → SpineQ P bnd wires' body' n e w
  | 0, _, _, _ => trivial
  | _ + 1, _, _, hs => fun m k a b he =>
    let ⟨x, y, hm, hd, hv, hr⟩ := hs m k a b he
    ⟨x, y, hb _ hm, hd.mono hw, hv.mono hb, SpineQ.mono hw hb hr⟩

theorem SpineQ.of_none {P : String → Prop} {bnd : FVarId → Option String} {wires : List Port}
    {body : List Stmt} {e : Lean.Expr} {w : String} (h : canonicalConcat? e = none) :
    ∀ n, SpineQ P bnd wires body n e w
  | 0 => trivial
  | _ + 1 => fun m k a b he => by rw [h] at he; cases he

/-- The statements a state adds are IN FRONT of the builder's list (which is
kept in reverse emission order): the earlier body is a suffix. Declarations
are kept. -/
def Kept (s t : CircuitState) : Prop :=
  (∃ more, t.module.body = more ++ s.module.body) ∧ ∀ p ∈ s.module.wires, p ∈ t.module.wires

theorem Kept.refl (s : CircuitState) : Kept s s := ⟨⟨[], rfl⟩, fun _ h => h⟩
theorem Kept.trans {s t u : CircuitState} (h : Kept s t) (k : Kept t u) : Kept s u := by
  obtain ⟨⟨m1, h1⟩, w1⟩ := h
  obtain ⟨⟨m2, h2⟩, w2⟩ := k
  exact ⟨⟨m2 ++ m1, by rw [h2, h1, List.append_assoc]⟩, fun p hp => w2 p (w1 p hp)⟩
theorem Kept.mem {s t : CircuitState} (h : Kept s t) : ∀ st ∈ s.module.body, st ∈ t.module.body := by
  obtain ⟨⟨m, hm⟩, -⟩ := h
  intro st hs
  rw [hm]
  exact List.mem_append_right _ hs

/-- **The record invariant**: every recorded wire has the links of the
expression it is recorded for, is declared at the width of the value that
expression means, is not a protected name, and is driven. -/
def RecQ (ctx : CompilerState) (inputs : FVarId → Option Value) (P : String → Prop)
    (s : CircuitState) : Prop :=
  ∀ w e, s.translateRecord.get? w = some e →
    (∀ n, SpineQ P (fun id => visible ctx s.sourceBindings id) s.module.wires s.module.body n e w) ∧
    (∀ v, Meaning inputs e v → Decl s.module.wires w v.kind.width) ∧
    ¬ P w ∧ (∃ rhs, Stmt.assign w rhs ∈ s.module.body) ∧ e.isFVar = false

theorem RecQ.empty {ctx inputs P} {s : CircuitState} (h : s.translateRecord = {}) :
    RecQ ctx inputs P s := by
  intro w e he; simp [h] at he

/-- Among the protected names, an expression reads only those in `V`. -/
def ReadsOK (P V : String → Prop) (rhs : Sparkle.IR.AST.Expr) : Prop :=
  ∀ x ∈ refsOf rhs, P x → V x

/-! ### Closed reads

Every statement reads only protected names and names driven EARLIER. The
builder's list is in reverse emission order, so "earlier" is "in the rest of
the list". `Cl P W s`: the body is closed, and every name in `W` — the wires
the program in hand may read — is protected or already driven. A wire that
was only MADE (reserved) is not in `W` until its assignment is emitted. -/

/-- Every statement reads protected names or names the statements after it in
the list (emitted before it) drive. -/
def ClosedB (P : String → Prop) : List Stmt → Prop
  | [] => True
  | st :: post => (∀ x ∈ stmtReads st, P x ∨ x ∈ writesOf post) ∧ ClosedB P post

/-- The body is closed, and every name of `W` is protected or driven. -/
def Cl (P W : String → Prop) (s : CircuitState) : Prop :=
  ClosedB P s.module.body ∧ ∀ x, W x → Drv P s.module.body x

theorem Cl.weaken {P W W' : String → Prop} {s : CircuitState} (h : ∀ x, W' x → W x) :
    Cl P W s → Cl P W' s := fun hc => ⟨hc.1, fun x hx => hc.2 x (h x hx)⟩

theorem Cl.add {P W : String → Prop} {s : CircuitState} {x : String}
    (hd : Drv P s.module.body x) : Cl P W s → Cl P (fun y => W y ∨ y = x) s :=
  fun hc => ⟨hc.1, fun y hy => hy.elim (hc.2 y) (fun e => e ▸ hd)⟩

theorem Cl.body {P W : String → Prop} {s t : CircuitState} (hb : t.module.body = s.module.body) :
    Cl P W s → Cl P W t := fun hc => ⟨hb ▸ hc.1, fun x hx => hb ▸ hc.2 x hx⟩

theorem mem_writesOf_assign {x : String} {rhs : Sparkle.IR.AST.Expr} {body : List Stmt}
    (h : Stmt.assign x rhs ∈ body) : x ∈ writesOf body :=
  List.mem_flatMap.mpr ⟨_, h, by simp [stmtWrites]⟩

/-- An assignment reading names of `W`: the body stays closed, and the
assigned name is now driven. -/
theorem Cl.emit {P W : String → Prop} {s : CircuitState} (lhs : String)
    (rhs : Sparkle.IR.AST.Expr) (h : ∀ x ∈ refsOf rhs, W x) :
    Cl P W s → Cl P (fun y => W y ∨ y = lhs) (CircuitM.emitAssign lhs rhs s).2 := by
  intro hc
  rw [Cl, emitAssign_body_cons]
  refine ⟨⟨fun x hx => ?_, hc.1⟩, fun y hy => ?_⟩
  · rcases hc.2 x (h x hx) with ⟨r, hr⟩ | hp
    · exact Or.inr (mem_writesOf_assign hr)
    · exact Or.inl hp
  · rcases hy with hy | hy
    · exact (hc.2 y hy).mono (fun st hs => List.mem_cons_of_mem _ hs)
    · exact hy ▸ Or.inl ⟨rhs, List.mem_cons_self ..⟩

/-- The state invariant.
* the record invariant;
* every input variable is bound to a wire declared at its value's width;
* the PROTECTED names `P` are in use — so no wire made from here on is one of
  them — and no statement drives one;
* the variables in `B` (those the term being translated uses) are bound to
  wires that, if protected, are in `V`; and every statement so far reads,
  among the protected names, only those in `V`. -/
def St (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) (s : CircuitState) : Prop :=
  RecQ ctx inputs P s ∧
    (∀ id v, inputs id = some v → ∃ z, visible ctx s.sourceBindings id = some z ∧
      Decl s.module.wires z v.kind.width ∧ P z) ∧
    (∀ x, P x → s.usedNames.contains x = true) ∧
    (∀ l r, Stmt.assign l r ∈ s.module.body → ¬ P l) ∧
    (∀ id z, B id → visible ctx s.sourceBindings id = some z → V z) ∧
    (∀ l r, Stmt.assign l r ∈ s.module.body → ReadsOK P V r)

/-- What every action does to the state: statements added in front,
declarations kept, bindings unchanged, names in use stay in use. -/
def Ext (s t : CircuitState) : Prop :=
  Kept s t ∧ t.sourceBindings = s.sourceBindings ∧
    ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true

theorem Ext.refl (s : CircuitState) : Ext s s := ⟨Kept.refl s, rfl, fun _ h => h⟩
theorem Ext.trans {s t u : CircuitState} (h : Ext s t) (k : Ext t u) : Ext s u :=
  ⟨h.1.trans k.1, k.2.1.trans h.2.1, fun z hz => k.2.2 z (h.2.2 z hz)⟩

theorem St.transfer {ctx inputs B P V} {s t : CircuitState} (h : St ctx inputs B P V s)
    (hr : t.translateRecord = s.translateRecord) (hx : Ext s t)
    (hb : ∀ l r, Stmt.assign l r ∈ t.module.body →
      Stmt.assign l r ∈ s.module.body ∨ (¬ P l ∧ ReadsOK P V r)) :
    St ctx inputs B P V t :=
  ⟨fun w e he => by
      obtain ⟨h1, h2, h3, ⟨rhs, h4⟩, h5⟩ := h.1 w e (hr ▸ he)
      exact ⟨fun n => by rw [hx.2.1]; exact (h1 n).mono hx.1.2 hx.1.mem,
        fun v hv => (h2 v hv).mono hx.1.2, h3,
        ⟨rhs, hx.1.mem _ h4⟩, h5⟩,
    fun id v hi => by
      obtain ⟨z, hz, hd, hp⟩ := h.2.1 id v hi
      exact ⟨z, by rw [hx.2.1]; exact hz, hd.mono hx.1.2, hp⟩,
    fun x hx' => hx.2.2 x (h.2.2.1 x hx'),
    fun l r hm => (hb l r hm).elim (h.2.2.2.1 l r) (·.1),
    fun id z hB hz => h.2.2.2.2.1 id z hB (by rw [← hx.2.1]; exact hz),
    fun l r hm => (hb l r hm).elim (h.2.2.2.2.2 l r) (·.2)⟩

/-- An action keeps the state invariant; statements in front, bindings kept. -/
def Good (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) {α : Type} (a : CompilerM α) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs B P V s → St ctx inputs B P V t ∧ Ext s t

/-- …and the wire it returns, if protected, is in `V`; and it keeps the reads
closed, the returned wire being protected or driven (`Cl`). -/
def GoodR (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) (a : CompilerM String) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs B P V s →
    St ctx inputs B P V t ∧ Ext s t ∧ (P r → V r) ∧
      ∀ W, Cl P W s → Cl P (fun y => W y ∨ y = r) t

variable {ctx : CompilerState} {inputs : FVarId → Option Value} {B : FVarId → Prop}
  {P V : String → Prop}

theorem GoodR.good {a : CompilerM String} (h : GoodR ctx inputs B P V a) :
    Good ctx inputs B P V a :=
  fun s t r hr hq => ⟨(h s t r hr hq).1, (h s t r hr hq).2.1⟩

theorem Good.pure {α : Type} (a : α) : Good ctx inputs B P V (Pure.pure a : CompilerM α) := by
  intro s t r hr hq
  obtain ⟨-, rfl⟩ := Returns.pure hr
  exact ⟨hq, Ext.refl _⟩

theorem Good.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    (hm : Good ctx inputs B P V m) (hf : ∀ a, Good ctx inputs B P V (f a)) :
    Good ctx inputs B P V (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, k1⟩ := hm s sm a h1 hq
  obtain ⟨q2, k2⟩ := hf a sm t r h2 q1
  exact ⟨q2, k1.trans k2⟩

/-- A bind of a translation: what it returns, if protected, is in `V`. -/
theorem Good.bindR {β : Type} {m : CompilerM String} {f : String → CompilerM β}
    (hm : GoodR ctx inputs B P V m) (hf : ∀ a, (P a → V a) → Good ctx inputs B P V (f a)) :
    Good ctx inputs B P V (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, k1, hv, -⟩ := hm s sm a h1 hq
  obtain ⟨q2, k2⟩ := hf a hv sm t r h2 q1
  exact ⟨q2, k1.trans k2⟩

theorem Good.throw {α : Type} (e : Exception) : Good ctx inputs B P V (throw e : CompilerM α) :=
  fun _ _ _ hr _ => (Returns.throw hr).elim

theorem Good.liftMetaM {α : Type} (x : MetaM α) :
    Good ctx inputs B P V (CompilerM.liftMetaM x) := by
  intro s t r hr hq
  obtain rfl := Returns.liftMetaM hr
  exact ⟨hq, Ext.refl _⟩

/-- What `makeWire` does: a name not in use before (so not a protected one),
declared at the given type; nothing else that the invariant reads. -/
theorem makeWire_facts {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {s t : CircuitState} {r : String}
    (hr : Returns (CompilerM.makeWire hint ty named) ctx s r t) (hq : St ctx inputs B P V s) :
    St ctx inputs B P V t ∧ Ext s t ∧ ¬ P r ∧ Decl t.module.wires r ty.bitWidth := by
  obtain ⟨hn, ht⟩ := makeWire_returns hr
  obtain ⟨hf, hu, hb, hw⟩ := CircuitM.makeWire_spec hint ty named s
  rw [← hn] at hf hu hw
  subst ht
  have hx : Ext s (CircuitM.makeWire hint ty named s).2 :=
    ⟨⟨⟨[], by rw [hb]; rfl⟩, fun p hp => by rw [hw]; exact List.mem_cons_of_mem _ hp⟩,
      CircuitM.makeWire_sourceBindings _ _ _ _,
      fun z hz => by rw [hu]; simp [Std.HashSet.contains_insert, hz]⟩
  refine ⟨hq.transfer (CircuitM.makeWire_translateRecord _ _ _ _) hx
    (fun l r' hm => Or.inl (hb ▸ hm)), hx, fun hp => ?_, ty, by rw [hw]; exact List.mem_cons_self .., rfl⟩
  have := hq.2.2.1 r hp
  rw [hf] at this
  cases this

theorem Good.makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    Good ctx inputs B P V (CompilerM.makeWire hint ty named) :=
  fun _ _ _ hr hq => ⟨(makeWire_facts hr hq).1, (makeWire_facts hr hq).2.1⟩

/-- A bind of `makeWire`: the wire it returns is not a protected name. -/
theorem Good.bindMake {β : Type} {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {f : String → CompilerM β} (hf : ∀ r, ¬ P r → Good ctx inputs B P V (f r)) :
    Good ctx inputs B P V (CompilerM.makeWire hint ty named >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, k1, hp, -⟩ := makeWire_facts h1 hq
  obtain ⟨q2, k2⟩ := hf a hp sm t r h2 q1
  exact ⟨q2, k1.trans k2⟩

theorem emitAssign_ext (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    Ext s (CircuitM.emitAssign lhs rhs s).2 :=
  ⟨⟨⟨[.assign lhs rhs], by rw [emitAssign_body_cons]; rfl⟩,
      fun p hp => by rw [emitAssign_wires]; exact hp⟩, rfl,
    fun z hz => by rw [emitAssign_usedNames]; exact hz⟩

/-- An assignment to a name that is not protected, reading only what `V` allows. -/
theorem Good.emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) (hl : ¬ P lhs)
    (hr : ReadsOK P V rhs) : Good ctx inputs B P V (CompilerM.emitAssign lhs rhs) := by
  intro s t r hret hq
  have ht := emitAssign_returns hret
  subst ht
  refine ⟨hq.transfer (emitAssign_translateRecord _ _ _) (emitAssign_ext _ _ _) (fun l r' hm => ?_),
    emitAssign_ext _ _ _⟩
  rw [emitAssign_body_cons] at hm
  rcases List.mem_cons.mp hm with heq | hin
  · cases heq; exact Or.inr ⟨hl, hr⟩
  · exact Or.inl hin

theorem Good.lookupVar (id : FVarId) : Good ctx inputs B P V (CompilerM.lookupVar id) := by
  intro s t r hr hq
  obtain ⟨-, rfl⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns hr
  exact ⟨hq, Ext.refl _⟩

/-- The wire an action returns is declared at width `N` and is not protected
(a wire the action made). -/
def Last (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) (N : Nat) (a : CompilerM String) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs B P V s → Decl t.module.wires r N ∧ ¬ P r

theorem Last.bind {α : Type} {N : Nat} {m : CompilerM α} {f : α → CompilerM String}
    (hm : Good ctx inputs B P V m) (hf : ∀ a, Last ctx inputs B P V N (f a)) :
    Last ctx inputs B P V N (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  exact hf a sm t r h2 (hm s sm a h1 hq).1

theorem Last.bindR {N : Nat} {m : CompilerM String} {f : String → CompilerM String}
    (hm : GoodR ctx inputs B P V m) (hf : ∀ a, (P a → V a) → Last ctx inputs B P V N (f a)) :
    Last ctx inputs B P V N (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hv, -⟩ := hm s sm a h1 hq
  exact hf a hv sm t r h2 q1

/-- A result wire made, assigned and returned. -/
theorem Last.emit {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {rhs : String → Sparkle.IR.AST.Expr} :
    Last ctx inputs B P V ty.bitWidth (CompilerM.makeWire hint ty named >>= fun r =>
      CompilerM.emitAssign r (rhs r) >>= fun _ => Pure.pure r) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨u, sn, h3, h4⟩ := Returns.bind h2
  obtain ⟨rfl, rfl⟩ := Returns.pure h4
  obtain ⟨-, -, hp, hd⟩ := makeWire_facts h1 hq
  have ht := emitAssign_returns h3
  subst ht
  exact ⟨hd.mono (emitAssign_ext _ _ _).1.2, hp⟩

/-- An action returns the given wire. -/
def Ret (ctx : CompilerState) (r : String) (a : CompilerM String) : Prop :=
  ∀ s t x, Returns a ctx s x t → x = r

theorem Ret.pure (r : String) : Ret ctx r (Pure.pure r) := fun _ _ _ h => (Returns.pure h).1
theorem Ret.bind {α : Type} {r : String} {m : CompilerM α} {f : α → CompilerM String}
    (hf : ∀ a, Ret ctx r (f a)) : Ret ctx r (m >>= f) := by
  intro s t x hr
  obtain ⟨a, sm, -, h2⟩ := Returns.bind hr
  exact hf a sm t x h2

/-- A result wire made FIRST, then other work, then returned. -/
theorem Last.makeFirst {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {f : String → CompilerM String} (hf : ∀ r, ¬ P r → Good ctx inputs B P V (f r))
    (hret : ∀ r, Ret ctx r (f r)) :
    Last ctx inputs B P V ty.bitWidth (CompilerM.makeWire hint ty named >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hp, hd⟩ := makeWire_facts h1 hq
  obtain rfl := hret a sm t r h2
  exact ⟨hd.mono (hf _ hp sm t _ h2 q1).2.1.2, hp⟩

/-- The wire an action returns is driven by a statement it leaves. -/
def Drives (ctx : CompilerState) (a : CompilerM String) : Prop :=
  ∀ s t r, Returns a ctx s r t → ∃ rhs, Stmt.assign r rhs ∈ t.module.body

theorem Drives.bind {α : Type} {m : CompilerM α} {f : α → CompilerM String}
    (hf : ∀ a, Drives ctx (f a)) : Drives ctx (m >>= f) := by
  intro s t r hr
  obtain ⟨a, sm, -, h2⟩ := Returns.bind hr
  exact hf a sm t r h2

/-- Assign, then return the assigned wire. -/
theorem Drives.assignRet {r : String} {rhs : Sparkle.IR.AST.Expr} :
    Drives ctx (CompilerM.emitAssign r rhs >>= fun _ => Pure.pure r) := by
  intro s t x hr
  obtain ⟨u, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨rfl, rfl⟩ := Returns.pure h2
  have ht := emitAssign_returns h1
  subst ht
  exact ⟨rhs, by rw [emitAssign_body_cons]; exact List.mem_cons_self ..⟩

/-! ### The closed-reads walk -/

/-- An action keeps the reads closed, for the readable names `W`. -/
def Cls (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V W : String → Prop) {α : Type} (a : CompilerM α) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs B P V s → Cl P W s → Cl P W t

/-- …and the wire it returns is protected or driven: readable from then on. -/
def ClsR (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V W : String → Prop) (a : CompilerM String) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs B P V s → Cl P W s →
    Cl P (fun y => W y ∨ y = r) t

variable {W : String → Prop}

theorem GoodR.cls {a : CompilerM String} (h : GoodR ctx inputs B P V a) (W : String → Prop) :
    ClsR ctx inputs B P V W a :=
  fun s t r hr hq hc => (h s t r hr hq).2.2.2 W hc

theorem Cls.pure {α : Type} (a : α) : Cls ctx inputs B P V W (Pure.pure a : CompilerM α) := by
  intro s t r hr _ hc
  obtain ⟨-, rfl⟩ := Returns.pure hr
  exact hc

theorem Cls.throw {α : Type} (e : Exception) : Cls ctx inputs B P V W (throw e : CompilerM α) :=
  fun _ _ _ hr _ _ => (Returns.throw hr).elim

theorem Cls.liftMetaM {α : Type} (x : MetaM α) :
    Cls ctx inputs B P V W (CompilerM.liftMetaM x) := by
  intro s t r hr _ hc
  obtain rfl := Returns.liftMetaM hr
  exact hc

theorem Cls.lookupVar (id : FVarId) : Cls ctx inputs B P V W (CompilerM.lookupVar id) := by
  intro s t r hr _ hc
  obtain ⟨-, rfl⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns hr
  exact hc

/-- Making a wire changes no statement: the wire is reserved, not readable. -/
theorem Cls.makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    Cls ctx inputs B P V W (CompilerM.makeWire hint ty named) := by
  intro s t r hr _ hc
  obtain ⟨-, ht⟩ := makeWire_returns hr
  obtain ⟨-, -, hb, -⟩ := CircuitM.makeWire_spec hint ty named s
  subst ht
  exact hc.body hb

theorem Cls.emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) (h : ∀ x ∈ refsOf rhs, W x) :
    Cls ctx inputs B P V W (CompilerM.emitAssign lhs rhs) := by
  intro s t r hret _ hc
  have ht := emitAssign_returns hret
  subst ht
  exact (hc.emit lhs rhs h).weaken (fun _ hx => Or.inl hx)

theorem Cls.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    (hg : Good ctx inputs B P V m) (hm : Cls ctx inputs B P V W m)
    (hf : ∀ a, Cls ctx inputs B P V W (f a)) : Cls ctx inputs B P V W (m >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  exact hf a sm t r h2 (hg s sm a h1 hq).1 (hm s sm a h1 hq hc)

/-- A bind of a translation: the wire it returns is readable in what follows. -/
theorem Cls.bindR {β : Type} {m : CompilerM String} {f : String → CompilerM β}
    (hg : GoodR ctx inputs B P V m)
    (hf : ∀ a, (P a → V a) → Cls ctx inputs B P V (fun y => W y ∨ y = a) (f a)) :
    Cls ctx inputs B P V W (m >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hv, hcl⟩ := hg s sm a h1 hq
  exact (hf a hv sm t r h2 q1 (hcl W hc)).weaken (fun _ hx => Or.inl hx)

/-- A bind of `makeWire`: the reserved wire is NOT readable. -/
theorem Cls.bindMake {β : Type} {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {f : String → CompilerM β} (hf : ∀ r, ¬ P r → Cls ctx inputs B P V W (f r)) :
    Cls ctx inputs B P V W (CompilerM.makeWire hint ty named >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hp, -⟩ := makeWire_facts h1 hq
  exact hf a hp sm t r h2 q1 (Cls.makeWire _ _ _ s sm a h1 hq hc)

/-- Assign a wire reading names of `W`, and return it: now driven. -/
theorem ClsR.emitRet {r : String} {rhs : Sparkle.IR.AST.Expr} (h : ∀ x ∈ refsOf rhs, W x) :
    ClsR ctx inputs B P V W (CompilerM.emitAssign r rhs >>= fun _ => Pure.pure r) := by
  intro s t x hr _ hc
  obtain ⟨u, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨rfl, rfl⟩ := Returns.pure h2
  have ht := emitAssign_returns h1
  subst ht
  exact hc.emit _ rhs h

theorem ClsR.bind {α : Type} {m : CompilerM α} {f : α → CompilerM String}
    (hg : Good ctx inputs B P V m) (hm : Cls ctx inputs B P V W m)
    (hf : ∀ a, ClsR ctx inputs B P V W (f a)) : ClsR ctx inputs B P V W (m >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  exact hf a sm t r h2 (hg s sm a h1 hq).1 (hm s sm a h1 hq hc)

/-- A bind of an action that keeps the state invariant and returns a readable
wire. -/
theorem ClsR.bindS {m : CompilerM String} {f : String → CompilerM String}
    (hg : ∀ s t r, Returns m ctx s r t → St ctx inputs B P V s → St ctx inputs B P V t)
    (hm : ClsR ctx inputs B P V W m)
    (hf : ∀ a, ClsR ctx inputs B P V (fun y => W y ∨ y = a) (f a)) :
    ClsR ctx inputs B P V W (m >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  exact (hf a sm t r h2 (hg s sm a h1 hq) (hm s sm a h1 hq hc)).weaken
    (fun _ hx => hx.elim (fun h => Or.inl (Or.inl h)) Or.inr)

theorem ClsR.bindR {m : CompilerM String} {f : String → CompilerM String}
    (hg : GoodR ctx inputs B P V m)
    (hf : ∀ a, (P a → V a) → ClsR ctx inputs B P V (fun y => W y ∨ y = a) (f a)) :
    ClsR ctx inputs B P V W (m >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hv, hcl⟩ := hg s sm a h1 hq
  exact (hf a hv sm t r h2 q1 (hcl W hc)).weaken
    (fun _ hx => hx.elim (fun h => Or.inl (Or.inl h)) Or.inr)

theorem ClsR.bindMake {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {f : String → CompilerM String} (hf : ∀ r, ¬ P r → ClsR ctx inputs B P V W (f r)) :
    ClsR ctx inputs B P V W (CompilerM.makeWire hint ty named >>= f) := by
  intro s t r hr hq hc
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hp, -⟩ := makeWire_facts h1 hq
  exact hf a hp sm t r h2 q1 (Cls.makeWire _ _ _ s sm a h1 hq hc)

-- (the rules are matched on the operations' names: unfolding them while
-- unifying a rule with another program is what makes a failed match slow)
attribute [local irreducible] CompilerM.makeWire CompilerM.emitAssign CompilerM.lookupVar

set_option hygiene false in
/-- A right-hand side over references: each is a made wire (not protected) or
a translation's result (in `V` if protected) — by the hypotheses in scope. -/
macro "reads" : tactic => `(tactic| (
  intro rdx rdhx rdhp
  simp [refsOf, refsOf.refsList] at rdhx
  repeat' (rcases rdhx with rdhx | rdhx)
  all_goals ((try subst rdhx); first | exact absurd rdhp (by assumption) | (revert rdhp; assumption))))

/-- The walk: binds, `pure`, the builder's operations, branches, and the
hypotheses in scope. -/
macro "good" : tactic => `(tactic| repeat (first
  | assumption
  | exact Good.pure _
  | exact Good.makeWire _ _ _
  | exact Good.emitAssign _ _ (by assumption) (by reads)
  | refine Good.bindMake (fun _ _ => ?_)
  | refine Good.bindR (by assumption) (fun _ _ => ?_)
  | exact Good.liftMetaM _
  | exact Good.lookupVar _
  | exact Good.throw _
  | refine Good.bind ?_ (fun _ => ?_)
  | split
  | intro _))

set_option hygiene false in
/-- A right-hand side over references, each readable (in `W`): the wires the
enclosing binds returned. -/
macro "wr" : tactic => `(tactic| (
  intro wrx wrh
  simp [refsOf, refsOf.refsList] at wrh
  repeat' (rcases wrh with wrh | wrh)
  all_goals ((try subst wrh); simp)))

/-- The closed-reads walk of an arm. -/
macro "cls" : tactic => `(tactic| repeat (first
  | exact ClsR.emitRet (by wr)
  | exact Cls.pure _
  | exact Cls.emitAssign _ _ (by wr)
  | exact Cls.makeWire _ _ _
  | exact Cls.liftMetaM _
  | exact Cls.lookupVar _
  | exact Cls.throw _
  | refine ClsR.bindMake (fun _ _ => ?_)
  | refine Cls.bindMake (fun _ _ => ?_)
  | refine ClsR.bindR (by assumption) (fun _ _ => ?_)
  | refine Cls.bindR (by assumption) (fun _ _ => ?_)
  | refine ClsR.bind (by good) ?_ (fun _ => ?_)
  | refine Cls.bind (by good) ?_ (fun _ => ?_)
  | split
  | intro _))

/-- The declared width of the result: skip to the final emit. -/
macro "last" : tactic => `(tactic| repeat (first
  | exact Last.emit
  | refine Last.bindR (by assumption) (fun _ _ => ?_)
  | refine Last.bind (by assumption) (fun _ => ?_)))

/-- The result is driven: skip to the final assign-and-return. -/
macro "drives" : tactic => `(tactic| repeat (first
  | exact Drives.assignRet
  | refine Drives.bind (fun _ => ?_)))

/-- An arm: it keeps the invariant; its result is a wire it made, declared at
width `N`, and driven; it keeps the reads closed. -/
def Arm (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) (N : Nat) (a : CompilerM String) : Prop :=
  Good ctx inputs B P V a ∧ Last ctx inputs B P V N a ∧ Drives ctx a ∧
    ∀ W, ClsR ctx inputs B P V W a

/-! ## The arms that are not a concatenation -/

section Arms
variable {rec : TranslateFn} {ae be ce : Lean.Expr} {hint : String} {named : Bool}

theorem compare_arm {le : SignalCompareKind}
    (oa : GoodR ctx inputs B P V (rec ae "a" false false))
    (ob : GoodR ctx inputs B P V (rec be "b" false false)) :
    Arm ctx inputs B P V 1 (translateSignalCompare rec le ae be hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateSignalCompare emitCompareResult emitBoolResult
  · good
  · last
  · drives
  · cls

theorem appCompare_arm {le : SignalCompareKind}
    (oa : GoodR ctx inputs B P V (rec ae "app_arg" false false))
    (ob : GoodR ctx inputs B P V (rec be "app_arg" false false)) :
    Arm ctx inputs B P V 1 (translateAppCompare rec le ae be hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateAppCompare emitCompareResult emitBoolResult
  · good
  · last
  · drives
  · cls

theorem boolBin_arm {kind : SignalBoolBinKind}
    (oa : GoodR ctx inputs B P V (rec ae "a" false false))
    (ob : GoodR ctx inputs B P V (rec be "b" false false)) :
    Arm ctx inputs B P V 1 (translateBoolBinary rec kind ae be hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateBoolBinary emitBoolResult
  · good
  · last
  · drives
  · cls

theorem appBool_arm {kind : SignalBoolBinKind}
    (oa : GoodR ctx inputs B P V (rec ae "app_arg" false false))
    (ob : GoodR ctx inputs B P V (rec be "app_arg" false false)) :
    Arm ctx inputs B P V 1 (translateAppBoolBinary rec kind ae be hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateAppBoolBinary emitBoolResult
  · good
  · last
  · drives
  · cls

/-- A Bool result wire: made (not protected), assigned, returned. -/
theorem emitBool_facts {rhs : Sparkle.IR.AST.Expr} {hint : String} {named : Bool}
    {s t : CircuitState} {r : String} (hro : ReadsOK P V rhs)
    (hr : Returns (emitBoolResult rhs hint named) ctx s r t) (hq : St ctx inputs B P V s) :
    St ctx inputs B P V t ∧ Ext s t ∧ ¬ P r := by
  unfold emitBoolResult at hr
  obtain ⟨w, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨u, sn, h3, h4⟩ := Returns.bind h2
  obtain ⟨rfl, rfl⟩ := Returns.pure h4
  obtain ⟨q1, k1, hp, -⟩ := makeWire_facts h1 hq
  obtain ⟨q2, k2⟩ := Good.emitAssign (ctx := ctx) (inputs := inputs) (B := B) _ _ hp hro sm _ u h3 q1
  exact ⟨q2, k1.trans k2, hp⟩

theorem appBool2_arm {f : AppBool2}
    (oa : GoodR ctx inputs B P V (rec ae "app_arg" false false))
    (ob : GoodR ctx inputs B P V (rec be "app_arg" false false)) :
    Arm ctx inputs B P V 1 (translateAppBool2 rec f ae be hint named) := by
  have inner : ∀ aw bw, (P aw → V aw) → (P bw → V bw) →
      ReadsOK P V (appBool2Inner f aw bw) := by
    intro aw bw ha hb x hx hp
    rcases appBool2Inner_refs hx with rfl | rfl
    · exact ha hp
    · exact hb hp
  have outer : ∀ aw bw n, (P aw → V aw) → (P bw → V bw) → ¬ P n →
      ReadsOK P V (appBool2Outer f aw bw n) := by
    intro aw bw n ha hb hn x hx hp
    rcases appBool2Outer_refs hx with rfl | rfl | rfl
    · exact ha hp
    · exact hb hp
    · exact absurd hp hn
  have mid : ∀ aw bw, (P aw → V aw) → (P bw → V bw) →
      ∀ s t n, Returns (emitBoolResult (appBool2Inner f aw bw) (appBool2Hint f) false) ctx s n t →
        St ctx inputs B P V s → St ctx inputs B P V t ∧ Ext s t ∧ ¬ P n :=
    fun aw bw ha hb s t n hr hq => emitBool_facts (inner aw bw ha hb) hr hq
  refine ⟨?_, ?_, ?_, fun W => ?_⟩
  · unfold translateAppBool2
    refine Good.bindR oa (fun aw ha => Good.bindR ob (fun bw hb => ?_))
    intro s t r hr hq
    obtain ⟨n, sm, h1, h2⟩ := Returns.bind hr
    obtain ⟨q1, k1, hn⟩ := mid aw bw ha hb s sm n h1 hq
    obtain ⟨q2, k2, -⟩ := emitBool_facts (outer aw bw n ha hb hn) h2 q1
    exact ⟨q2, k1.trans k2⟩
  · unfold translateAppBool2
    refine Last.bindR oa (fun aw ha => Last.bindR ob (fun bw hb => ?_))
    intro s t r hr hq
    obtain ⟨n, sm, h1, h2⟩ := Returns.bind hr
    obtain ⟨q1, -, -⟩ := mid aw bw ha hb s sm n h1 hq
    unfold emitBoolResult at h2
    exact Last.emit (ty := .bit) _ _ _ h2 q1
  · unfold translateAppBool2 emitBoolResult; drives
  · unfold translateAppBool2
    refine ClsR.bindR oa (fun aw ha => ClsR.bindR ob (fun bw hb => ?_))
    refine ClsR.bindS (fun s t n hr hq => (mid aw bw ha hb s t n hr hq).1) ?_ (fun n => ?_)
    · unfold emitBoolResult
      refine ClsR.bindMake (fun r _ => ClsR.emitRet ?_)
      intro x hx
      rcases appBool2Inner_refs hx with rfl | rfl
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl
    · unfold emitBoolResult
      refine ClsR.bindMake (fun r _ => ClsR.emitRet ?_)
      intro x hx
      rcases appBool2Outer_refs hx with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inr rfl))
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl

theorem mux_arm {ty : Sparkle.IR.Type.HWType}
    (oc : GoodR ctx inputs B P V (rec ce "mux_cond" false false))
    (oa : GoodR ctx inputs B P V (rec ae "mux_then" false false))
    (ob : GoodR ctx inputs B P V (rec be "mux_else" false false)) :
    Arm ctx inputs B P V ty.bitWidth (translateMuxWith rec (pure ty) ce ae be hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateMuxWith emitMuxResult
  · good
  · refine Last.bindR oc (fun _ _ => Last.bindR oa (fun _ _ => Last.bindR ob (fun _ _ => ?_)))
    intro s t r hr hq
    obtain ⟨x, sm, h1, h2⟩ := Returns.bind hr
    obtain ⟨rfl, rfl⟩ := Returns.pure h1
    exact Last.emit _ _ _ h2 hq
  · drives
  · cls

theorem setw_arm {ws wt : Nat} (oa : GoodR ctx inputs B P V (rec ae "s" false false)) :
    Arm ctx inputs B P V wt (do
      let sw ← rec ae "s" false false
      emitCastResult (setwRhs ws wt sw) wt hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold emitCastResult
  · refine Good.bindR oa (fun sw hsw => Good.bindMake (fun r hr =>
      Good.bind (Good.emitAssign _ _ hr ?_) (fun _ => Good.pure _)))
    intro x hx hp
    have := setwRhs_refs hx
    subst this
    exact hsw hp
  · exact Last.bindR oa (fun _ _ => Last.emit (ty := .bitVector wt))
  · drives
  · refine ClsR.bindR oa (fun sw _ => ClsR.bindMake (fun r _ => ClsR.emitRet ?_))
    intro x hx
    have := setwRhs_refs hx
    subst this
    exact Or.inr rfl

theorem hwTypeFromWidth_bitWidth (len : Nat) :
    (Sparkle.IR.Type.hwTypeFromWidth len).bitWidth = len := by
  unfold Sparkle.IR.Type.hwTypeFromWidth
  split
  · rename_i h; simp at h; subst h; rfl
  · rfl

theorem slice_arm {hd : String} {start len : Nat}
    (oa : GoodR ctx inputs B P V (rec ae hd false false)) :
    Arm ctx inputs B P V len (do
      let sw ← rec ae hd false false
      emitSliceResult (sliceRhs start len sw) len hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold emitSliceResult
  · refine Good.bindR oa (fun sw hsw => Good.bindMake (fun r hr =>
      Good.bind (Good.emitAssign _ _ hr ?_) (fun _ => Good.pure _)))
    intro x hx hp
    have := sliceRhs_refs hx
    subst this
    exact hsw hp
  · have := Last.bindR (N := (Sparkle.IR.Type.hwTypeFromWidth len).bitWidth) oa
      (fun sw _ => Last.emit (ctx := ctx) (inputs := inputs) (B := B) (P := P) (V := V)
        (hint := hint) (ty := Sparkle.IR.Type.hwTypeFromWidth len) (named := named)
        (rhs := fun _ => sliceRhs start len sw))
    rw [hwTypeFromWidth_bitWidth] at this
    exact this
  · drives
  · refine ClsR.bindR oa (fun sw _ => ClsR.bindMake (fun r _ => ClsR.emitRet ?_))
    intro x hx
    have := sliceRhs_refs hx
    subst this
    exact Or.inr rfl

theorem Arm.goodR {N : Nat} {a : CompilerM String} (h : Arm ctx inputs B P V N a) :
    GoodR ctx inputs B P V a :=
  fun s t r hr hq => ⟨(h.1 s t r hr hq).1, (h.1 s t r hr hq).2,
    fun hp => absurd hp (h.2.1 s t r hr hq).2, fun W hc => h.2.2.2 W s t r hr hq hc⟩

theorem concatConst_arm {k v : Nat} : Arm ctx inputs B P V k (emitConcatConst k v) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold emitConcatConst emitCastResult
  · good
  · exact Last.emit (ty := .bitVector k)
  · drives
  · cls

theorem concatActs_arm {wd : Nat} {hiAct loAct : CompilerM String}
    (oa : GoodR ctx inputs B P V hiAct) (ob : GoodR ctx inputs B P V loAct) :
    Arm ctx inputs B P V wd (translateConcatActs wd hiAct loAct hint named) := by
  refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateConcatActs
  · good
  · refine Last.makeFirst (ty := .bitVector wd) (fun r hr => ?_) (fun r => ?_)
    · good
    · exact Ret.bind (fun _ => Ret.bind (fun _ => Ret.bind (fun _ => Ret.pure r)))
  · drives
  · cls

end Arms

/-! ## The result's links and declaration -/

/-- An action for the expression `e`: it keeps the invariant, the statements
and the bindings; the wire it returns has the links of `e`, is declared at
the width of the value `e` means, is in `V` if protected, and is driven (or
is an input); the reads stay closed, the returned wire readable. -/
def Spec (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) (e : Lean.Expr) (a : CompilerM String) : Prop :=
  ∀ s t w, Returns a ctx s w t → St ctx inputs B P V s →
    St ctx inputs B P V t ∧ Ext s t ∧
      (∀ n, SpineQ P (fun id => visible ctx t.sourceBindings id) t.module.wires t.module.body n e w) ∧
      (∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width) ∧
      (P w → V w) ∧ Src P (fun id => visible ctx t.sourceBindings id) t.module.body e w ∧
      ∀ W, Cl P W s → Cl P (fun y => W y ∨ y = w) t

theorem Spec.goodR {e : Lean.Expr} {a : CompilerM String} (h : Spec ctx inputs B P V e a) :
    GoodR ctx inputs B P V a :=
  fun s t r hr hq => ⟨(h s t r hr hq).1, (h s t r hr hq).2.1, (h s t r hr hq).2.2.2.2.1,
    (h s t r hr hq).2.2.2.2.2.2⟩

/-- …and the wire is one the action made and drove (what the cache may record). -/
def SpecA (ctx : CompilerState) (inputs : FVarId → Option Value) (B : FVarId → Prop)
    (P V : String → Prop) (e : Lean.Expr) (a : CompilerM String) : Prop :=
  Spec ctx inputs B P V e a ∧ e.isFVar = false ∧
    ∀ s t w, Returns a ctx s w t → St ctx inputs B P V s →
      ¬ P w ∧ ∃ rhs, Stmt.assign w rhs ∈ t.module.body

/-- For an expression that is not a canonical concatenation: the arm, and the
width its value has. -/
theorem SpecA.of_arm {e : Lean.Expr} {a : CompilerM String} {N : Nat}
    (ha : Arm ctx inputs B P V N a) (hn : canonicalConcat? e = none) (hf : e.isFVar = false)
    (hm : ∀ v, Meaning inputs e v → v.kind.width = N) : SpecA ctx inputs B P V e a :=
  ⟨fun s t r hr hq => ⟨(ha.1 s t r hr hq).1, (ha.1 s t r hr hq).2, SpineQ.of_none hn,
      fun v hv => by rw [hm v hv]; exact (ha.2.1 s t r hr hq).1,
      fun hp => absurd hp (ha.2.1 s t r hr hq).2, .inl ⟨hf, ha.2.2.1 s t r hr⟩,
      fun W hc => ha.2.2.2 W s t r hr hq hc⟩, hf,
    fun s t r hr hq => ⟨(ha.2.1 s t r hr hq).2, ha.2.2.1 s t r hr⟩⟩

/-- A record of the result keeps the record invariant. -/
theorem St.record {s : CircuitState} {e : Lean.Expr} {w : String} (h : St ctx inputs B P V s)
    (hw : ∀ n, SpineQ P (fun id => visible ctx s.sourceBindings id) s.module.wires s.module.body n e w)
    (hd : ∀ v, Meaning inputs e v → Decl s.module.wires w v.kind.width)
    (hp : ¬ P w) (hdr : ∃ rhs, Stmt.assign w rhs ∈ s.module.body) (hf : e.isFVar = false) :
    St ctx inputs B P V { s with translateRecord := s.translateRecord.insert w e } := by
  refine ⟨fun w' e' he' => ?_, h.2⟩
  rw [Std.HashMap.get?_insert] at he'
  split at he'
  · rename_i hww
    cases he'
    rw [← (beq_iff_eq.mp hww)]
    exact ⟨hw, hd, hp, hdr, hf⟩
  · exact h.1 w' e' he'

/-- **The validated cache wrapper**: a hit returns a recorded wire — its
links, declaration, non-protection and driver are the record invariant's; a
miss lowers and records the result. -/
theorem Spec.cached {lower : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (h : SpecA ctx inputs B P V e (lower e hint top named)) :
    Spec ctx inputs B P V e (translateControlCachedWith lower e hint top named) := by
  intro s t w hr hq
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hrec⟩ := cacheLookupValidated_returns hit
    subst hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq.1 w e (hrec w rfl)
    exact ⟨hq, Ext.refl _, h1, h2, fun hp => absurd hp h3, .inl ⟨h5, h4⟩,
      fun W hc => hc.add (.inl h4)⟩
  · obtain ⟨q, k, sp, sd, hv, hdv, hcl⟩ := h.1 s sm w miss hq
    obtain ⟨hnp, hdr⟩ := h.2.2 s sm w miss hq
    have ht := recordTranslation_returns record
    subst ht
    exact ⟨q.record sp sd hnp hdr h.2.1, k, sp, sd, hv, hdv, fun W hc => (hcl W hc).body rfl⟩

/-- **The concat arm**: the result wire is driven by `{hi, lo}`; `hi` is
declared at the high operand's width and driven (or an input); `lo` has the
links of the low operand; the result is declared at the sum. -/
theorem concat_spec {e a b : Lean.Expr} {m k : Nat} {hint : String} {named : Bool}
    {hiAct loAct : CompilerM String} (he : canonicalConcat? e = some (m, k, a, b))
    (hma : ∃ v, Meaning inputs a v ∧ v.kind.width = m)
    (hm : ∀ v, Meaning inputs e v → v.kind.width = m + k)
    (oa : Spec ctx inputs B P V a hiAct) (ob : Spec ctx inputs B P V b loAct) :
    SpecA ctx inputs B P V e (translateConcatActs (m + k) hiAct loAct hint named) := by
  have harm := concatActs_arm (hint := hint) (named := named) (wd := m + k) oa.goodR ob.goodR
  have hfv : e.isFVar = false := by
    cases e <;> first | rfl | (simp [canonicalConcat?] at he)
  refine ⟨fun s t w hr hq => ?_, hfv, fun s t w hr hq =>
    ⟨(harm.2.1 s t w hr hq).2, harm.2.2.1 s t w hr⟩⟩
  have hg := harm.1 s t w hr hq
  refine ⟨hg.1, hg.2, ?_, fun v hv => by rw [hm v hv]; exact (harm.2.1 s t w hr hq).1,
    fun hp => absurd hp (harm.2.1 s t w hr hq).2, .inl ⟨hfv, harm.2.2.1 s t w hr⟩,
    fun W hc => harm.2.2.2 W s t w hr hq hc⟩
  unfold translateConcatActs at hr
  obtain ⟨res, sA, hmk, rest⟩ := Returns.bind hr
  obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
  obtain ⟨wb, sC, hb', rest⟩ := Returns.bind rest
  obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
  obtain ⟨hwv, ht⟩ := Returns.pure ret
  subst ht
  subst hwv
  obtain ⟨qA, -⟩ := Good.makeWire (ctx := ctx) (inputs := inputs) (B := B) (P := P) (V := V)
    _ _ _ s sA w hmk hq
  obtain ⟨qB, -, -, hda, -, hdrv, -⟩ := oa sA sB wa ha qA
  obtain ⟨-, xBC, spb, -⟩ := ob sB sC wb hb' qB
  have hD := emitAssign_returns hem
  subst hD
  have xCD := emitAssign_ext w (.concat [.ref wa, .ref wb]) sC
  obtain ⟨va, hva, hwa⟩ := hma
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    intro m' k' a' b' he2
    rw [he] at he2
    cases he2
    refine ⟨wa, wb, by rw [emitAssign_body_cons]; exact List.mem_cons_self .., ?_, ?_, ?_⟩
    · rw [← hwa]
      exact (hda va hva).mono (xBC.1.trans xCD.1).2
    · rw [(xBC.trans xCD).2.1]
      exact hdrv.mono (xBC.1.trans xCD.1).mem
    · exact (spb n).mono xCD.1.2 xCD.1.mem

/-! ## One step of the knot, for an expression that is not a concatenation -/

/-- **The step**, for `e` not a canonical concatenation: the validated lookup
(a hit changes nothing), the core, the record of its result, or the fallback
when the core declines. -/
theorem step_spec {rec : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (hn : canonicalConcat? e = none)
    (hcore : Good ctx inputs B P V (translateCore rec e hint top named))
    (hcl : ∀ W, Cls ctx inputs B P V W (translateCore rec e hint top named))
    (hres : ∀ s t z, Returns (translateCore rec e hint top named) ctx s (some z) t →
      St ctx inputs B P V s →
      (∀ v, Meaning inputs e v → Decl t.module.wires z v.kind.width) ∧ (P z → V z) ∧
        Src P (fun id => visible ctx t.sourceBindings id) t.module.body e z ∧
        (e.isFVar = false → ¬ P z ∧ ∃ rhs, Stmt.assign z rhs ∈ t.module.body))
    (hfb : ∀ s t, St ctx inputs B P V s →
      Returns (translateCore rec e hint top named) ctx s none t →
      Spec ctx inputs B P V e (translateFallback rec e hint top named)) :
    Spec ctx inputs B P V e (translateStepWith translateFallback rec e hint top named) := by
  have cont : ∀ {s t w} {K : Option String → CompilerM String} (c : Bool),
      (∀ z, K (some z) = Pure.pure z ∨
        (e.isFVar = false ∧ K (some z) = (recordTranslation e z c >>= fun _ => Pure.pure z)) ∨
        K (some z) = (if e.isFVar = true then Pure.pure z
          else recordTranslation e z c >>= fun _ => Pure.pure z)) →
      K none = translateFallback rec e hint top named →
      Returns (translateCore rec e hint top named >>= K) ctx s w t → St ctx inputs B P V s →
      St ctx inputs B P V t ∧ Ext s t ∧
        (∀ n, SpineQ P (fun id => visible ctx t.sourceBindings id) t.module.wires t.module.body n e w) ∧
        (∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width) ∧
        (P w → V w) ∧ Src P (fun id => visible ctx t.sourceBindings id) t.module.body e w ∧
        ∀ W, Cl P W s → Cl P (fun y => W y ∨ y = w) t := by
    intro s t w K c hsome hnone hr hq
    obtain ⟨r, sc, hc, rest⟩ := Returns.bind hr
    obtain ⟨qc, kc⟩ := hcore s sc r hc hq
    cases r with
    | some z =>
      obtain ⟨hdz, hvz, hdrz, hfz⟩ := hres s sc z hc hq
      have hp : ∀ {t w}, Returns (Pure.pure z : CompilerM String) ctx sc w t →
          St ctx inputs B P V t ∧ Ext s t ∧
            (∀ n, SpineQ P (fun id => visible ctx t.sourceBindings id) t.module.wires t.module.body n e w) ∧
            (∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width) ∧
            (P w → V w) ∧ Src P (fun id => visible ctx t.sourceBindings id) t.module.body e w ∧
            ∀ W, Cl P W s → Cl P (fun y => W y ∨ y = w) t := by
        intro t w h
        obtain ⟨rfl, rfl⟩ := Returns.pure h
        exact ⟨qc, kc, SpineQ.of_none hn, hdz, hvz, hdrz,
          fun W hW => (hcl W s _ _ hc hq hW).add hdrz.drv⟩
      have hrc : ∀ {t w}, e.isFVar = false →
          Returns (recordTranslation e z c >>= fun _ => (Pure.pure z : CompilerM String))
            ctx sc w t → St ctx inputs B P V t ∧ Ext s t ∧
            (∀ n, SpineQ P (fun id => visible ctx t.sourceBindings id) t.module.wires t.module.body n e w) ∧
            (∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width) ∧
            (P w → V w) ∧ Src P (fun id => visible ctx t.sourceBindings id) t.module.body e w ∧
            ∀ W, Cl P W s → Cl P (fun y => W y ∨ y = w) t := by
        intro t w hnf h
        obtain ⟨u, sr, record, ret⟩ := Returns.bind h
        obtain ⟨rfl, rfl⟩ := Returns.pure ret
        have hs := recordTranslation_returns record
        subst hs
        exact ⟨qc.record (SpineQ.of_none hn) hdz (hfz hnf).1 (hfz hnf).2 hnf,
          kc.trans ⟨Kept.refl _, rfl, fun _ h => h⟩, SpineQ.of_none hn, hdz, hvz, hdrz,
          fun W hW => ((hcl W s sc _ hc hq hW).add hdrz.drv).body rfl⟩
      rcases hsome z with hk | ⟨hnf, hk⟩ | hk <;> rw [hk] at rest
      · exact hp rest
      · exact hrc hnf rest
      · split at rest
        · exact hp rest
        · rename_i hnf
          exact hrc (by simpa using hnf) rest
    | none =>
      rw [hnone] at rest
      obtain ⟨q, k, sp, sd, hv, hdv, hcl'⟩ := hfb s sc hq hc sc t w rest qc
      exact ⟨q, kc.trans k, sp, sd, hv, hdv, fun W hW => hcl' W (hcl W s sc _ hc hq hW)⟩
  intro s t w hr hq
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  all_goals first
    | exact cont _ (fun z => by first | exact Or.inl rfl | exact Or.inr (Or.inl ⟨by simp_all, rfl⟩) | exact Or.inr (Or.inr rfl)) rfl hr hq
    | (obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
       obtain ⟨hs, hrec⟩ := cacheLookupValidated_returns rh
       subst hs
       cases hit with
       | some w' =>
         obtain ⟨hw, ht⟩ := Returns.pure hr
         subst ht hw
         obtain ⟨h1, h2, h3, h4, h5⟩ := hq.1 _ e (hrec _ rfl)
         exact ⟨hq, Ext.refl _, h1, h2, fun hp => absurd hp h3, .inl ⟨h5, h4⟩,
           fun W hW => hW.add (.inl h4)⟩
       | none => exact cont _ (fun z => by first | exact Or.inl rfl | exact Or.inr (Or.inl ⟨by simp_all, rfl⟩) | exact Or.inr (Or.inr rfl)) rfl hr hq)

/-! ## The step's own cases: a bound variable, a literal, a library operator -/

theorem pureLiteral_good (args : Array Lean.Expr) (hint : String) (named : Bool) :
    Good ctx inputs B P V (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?; good

theorem pureLiteral_cls (args : Array Lean.Expr) (hint : String) (named : Bool)
    (W : String → Prop) :
    Cls ctx inputs B P V W (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?; cls

/-- A bound variable the term uses: its wire, declared at the variable's
width, in `V`; nothing changes. -/
theorem input_spec {rec : TranslateFn} {id : FVarId} {v₀ : Value} {hint : String} {named : Bool}
    (hi : inputs id = some v₀) (hB : B id) :
    Spec ctx inputs B P V (.fvar id)
      (translateStepWith translateFallback rec (.fvar id) hint false named) := by
  refine step_spec rfl (Good.lookupVar id) (fun W => Cls.lookupVar id) ?_ ?_
  · intro s t z hr hq
    obtain ⟨hz, rfl⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns (id := id) hr
    obtain ⟨z', hbound, hd, hpz⟩ := hq.2.1 id v₀ hi
    rw [hbound] at hz
    cases hz
    refine ⟨fun v hv => ?_, fun _ => hq.2.2.2.2.1 id z hB hbound, .inr ⟨id, rfl, hbound, hpz⟩,
      fun h => by cases h⟩
    have : v = v₀ := hv.deterministic (.input rfl hi)
    rw [this]
    exact hd
  · intro s t hq hr
    obtain ⟨hv, -⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns (id := id) hr
    obtain ⟨z, hbound, -⟩ := hq.2.1 id v₀ hi
    rw [hbound] at hv
    cases hv

/-- A `Signal.pure` literal the core lowers. -/
theorem literal_step_spec {rec : TranslateFn} {e c : Lean.Expr} {us : List Level} {n v : Nat}
    {hint : String} {named : Bool}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (back : e.getAppArgs.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (hn : canonicalConcat? e = none) (hm : ∀ x, Meaning inputs e x → x.kind.width = n) :
    Spec ctx inputs B P V e (translateStepWith translateFallback rec e hint false named) := by
  have hcore : translateCore rec e hint false named =
      translateSignalPureLiteral? e.getAppArgs hint named := by
    unfold translateCore
    split
    · simp [Lean.Expr.getAppFn] at fn
    · rw [fn]; simp only [beq_self_eq_true, if_true]
  refine step_spec hn (by rw [hcore]; exact pureLiteral_good _ _ _)
    (fun W => by rw [hcore]; exact pureLiteral_cls _ _ _ W) ?_ ?_
  · intro s t z hr hq
    rw [hcore] at hr
    unfold translateSignalPureLiteral? at hr
    rw [back] at hr
    simp only [Option.bind_some, lit] at hr
    obtain ⟨w, sm, mk, rest⟩ := Returns.bind hr
    obtain ⟨u, se, em, rest⟩ := Returns.bind rest
    obtain ⟨hres, rfl⟩ := Returns.pure rest
    cases hres
    obtain ⟨-, -, hnp, hd⟩ := makeWire_facts mk hq
    have ht := emitAssign_returns em
    subst ht
    have hdr : ∃ rhs, Stmt.assign z rhs ∈ (CircuitM.emitAssign z (.const v n) sm).2.module.body :=
      ⟨_, by rw [emitAssign_body_cons]; exact List.mem_cons_self ..⟩
    exact ⟨fun x hx => by rw [hm x hx]; exact hd.mono (emitAssign_ext _ _ _).1.2,
      fun hp => absurd hp hnp, .inl ⟨isFVar_false_of_const fn, hdr⟩, fun _ => ⟨hnp, hdr⟩⟩
  · intro s t hq hr
    rw [hcore] at hr
    obtain ⟨w', hw'⟩ := literal_payload_some back lit hr
    cases hw'

/-- The Bool literal: the core declines, the fallback emits it under the
validated cache. -/
theorem bool_literal_spec {rec : TranslateFn} {dom : Lean.Expr} {hint : String} {named : Bool}
    (b : Bool) (hn : canonicalConcat? (literalE dom b) = none)
    (hm : ∀ x, Meaning inputs (literalE dom b) x → x.kind.width = 1) :
    Spec ctx inputs B P V (literalE dom b)
      (translateStepWith translateFallback rec (literalE dom b) hint false named) := by
  refine step_spec hn (by rw [literal_core]; exact Good.pure _)
    (fun W => by rw [literal_core]; exact Cls.pure _) ?_ ?_
  · intro s t z hr
    rw [literal_core] at hr
    cases (Returns.pure hr).1
  · intro s t hq hr
    rw [translateFallback_bool rec _ hint false named (by cases b <;> rfl)]
    refine Spec.cached (SpecA.of_arm (N := 1) ?_ hn (by cases b <;> rfl) hm)
    show Arm ctx inputs B P V 1 (translateBoolUncachedWith rec _ _ hint false named)
    rw [literal_uncached]
    refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold emitBoolLiteral emitBoolResult
    · good
    · exact Last.emit (ty := .bit)
    · drives
    · cls

/-- A canonical library operator: the result wire, the two operands, the assign. -/
theorem binary_step_spec {rec : TranslateFn} {e : Lean.Expr} {m : Name} {us : List Level}
    {hint : String} {named : Bool} {n : Nat} (op : Binary)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (hn : canonicalConcat? e = none) (hm : ∀ x, Meaning inputs e x → x.kind.width = n)
    (oa : GoodR ctx inputs B P V (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false))
    (ob : GoodR ctx inputs B P V (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false)) :
    Spec ctx inputs B P V e (translateStepWith translateFallback rec e hint false named) := by
  have hbin : Arm ctx inputs B P V n
      (translateCanonicalSignalBinary rec e op.operator e.getAppArgs true true hint named) := by
    refine ⟨?_, ?_, ?_, fun W => ?_⟩ <;> unfold translateCanonicalSignalBinary <;>
      simp only [width, if_true]
    · good
    · intro s t r hr hq
      obtain ⟨ty, sm, h1, h2⟩ := Returns.bind hr
      obtain ⟨rfl, rfl⟩ := Returns.pure h1
      refine Last.makeFirst (ty := .bitVector n) (fun r hr => ?_) (fun r => ?_) _ t r h2 hq
      · good
      · exact Ret.bind (fun _ => Ret.bind (fun _ => Ret.bind (fun _ => Ret.pure r)))
    · drives
    · cls
  refine step_spec hn ?_ ?_ ?_ ?_
  · intro s t r hr hq
    obtain ⟨w, -, lower⟩ := core_binary_returns fn hop kinds width hr
    exact hbin.1 s t w lower hq
  · intro W s t r hr hq hW
    obtain ⟨w, -, lower⟩ := core_binary_returns fn hop kinds width hr
    exact (hbin.2.2.2 W s t w lower hq hW).weaken (fun _ hx => Or.inl hx)
  · intro s t z hr hq
    obtain ⟨w, hw, lower⟩ := core_binary_returns fn hop kinds width hr
    cases hw
    obtain ⟨hd, hnp⟩ := hbin.2.1 s t z lower hq
    have hdr := hbin.2.2.1 s t z lower
    exact ⟨fun x hx => by rw [hm x hx]; exact hd, fun hp => absurd hp hnp,
      .inl ⟨isFVar_false_of_const fn, hdr⟩, fun _ => ⟨hnp, hdr⟩⟩
  · intro s t hq hr
    obtain ⟨w, hw, -⟩ := core_binary_returns fn hop kinds width hr
    cases hw

/-! ## The variables a term uses -/

/-- The Bool variables in `ub` and the BitVec variables in `uv` are the only
ones the term mentions. (Shaped like `Term.WF`, component for component.) -/
def Uses (ub uv : Nat → Prop) : {s : SType} → Term s → Prop
  | _, .boolInput j => ub j
  | _, .bitsInput _ j => uv j ∧ True ∧ True
  | _, .boolLit _ => True
  | _, .bitsLit _ _ => True
  | _, .bitsNum _ _ => True
  | _, .binary _ a b => Uses ub uv a ∧ Uses ub uv b
  | _, .compare _ a b => Uses ub uv a ∧ Uses ub uv b
  | _, .boolBinary _ a b => Uses ub uv a ∧ Uses ub uv b
  | _, .boolNot a => Uses ub uv a
  | _, .boolEq a b => Uses ub uv a ∧ Uses ub uv b
  | _, .mux c a b => Uses ub uv c ∧ Uses ub uv a ∧ Uses ub uv b
  | _, .setw _ a => Uses ub uv a ∧ True
  | _, .appCompare _ a b => Uses ub uv a ∧ Uses ub uv b
  | _, .appBool _ a b => Uses ub uv a ∧ Uses ub uv b
  | _, .appBool2 _ a b => Uses ub uv a ∧ Uses ub uv b
  | _, .slice _ _ _ a => Uses ub uv a ∧ True ∧ True
  | _, .concat a b => Uses ub uv a ∧ Uses ub uv b
  | _, .concatLitHi _ _ b => Uses ub uv b ∧ True ∧ True
  | _, .concatLitLo a _ _ => Uses ub uv a ∧ True ∧ True
  | _, .zextMap _ _ a => Uses ub uv a ∧ True
  | _, .sliceF _ _ _ a => Uses ub uv a ∧ True ∧ True

/-- Every term uses only "any variable". -/
theorem Uses.top : ∀ {s : SType} (e : Term s), Uses (fun _ => True) (fun _ => True) e
  | _, .boolInput _ => trivial
  | _, .bitsInput _ _ => ⟨trivial, trivial, trivial⟩
  | _, .boolLit _ => trivial
  | _, .bitsLit _ _ => trivial
  | _, .bitsNum _ _ => trivial
  | _, .binary _ a b => ⟨Uses.top a, Uses.top b⟩
  | _, .compare _ a b => ⟨Uses.top a, Uses.top b⟩
  | _, .boolBinary _ a b => ⟨Uses.top a, Uses.top b⟩
  | _, .boolNot a => Uses.top a
  | _, .boolEq a b => ⟨Uses.top a, Uses.top b⟩
  | _, .mux c a b => ⟨Uses.top c, Uses.top a, Uses.top b⟩
  | _, .setw _ a => ⟨Uses.top a, trivial⟩
  | _, .appCompare _ a b => ⟨Uses.top a, Uses.top b⟩
  | _, .appBool _ a b => ⟨Uses.top a, Uses.top b⟩
  | _, .appBool2 _ a b => ⟨Uses.top a, Uses.top b⟩
  | _, .slice _ _ _ a => ⟨Uses.top a, trivial, trivial⟩
  | _, .concat a b => ⟨Uses.top a, Uses.top b⟩
  | _, .concatLitHi _ _ b => ⟨Uses.top b, trivial, trivial⟩
  | _, .concatLitLo a _ _ => ⟨Uses.top a, trivial, trivial⟩
  | _, .zextMap _ _ a => ⟨Uses.top a, trivial⟩
  | _, .sliceF _ _ _ a => ⟨Uses.top a, trivial, trivial⟩

/-! ## The fuel induction -/

section Fuel
variable {dom : Lean.Expr} {bi vi : Nat → FVarId}

local notation "Q(" e ")" =>
  quote dom (fun j => Lean.Expr.fvar (bi j)) (fun j => Lean.Expr.fvar (vi j)) e

set_option maxHeartbeats 1000000 in
/-- **The translator leaves the spine, the declarations and the order facts**,
at every fuel, for every quoted well-formed term using only the variables in
`B`. -/
theorem fuel_spine (fuel : Nat) {kb kv : Nat} {vw : Nat → Nat} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w} {ub uv : Nat → Prop}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j))))
    (hub : ∀ j, ub j → B (bi j)) (huv : ∀ j, uv j → B (vi j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → Uses ub uv e → ∀ hint named,
      Spec ctx inputs B P V Q(e) (translateFuelFix translateStep fuel Q(e) hint false named) := by
  induction fuel with
  | zero =>
    intro s e he hu hint named s' t w hr hq
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hu hint named
    change Spec ctx inputs B P V _ (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named)
    have hmw : ∀ v, Meaning inputs Q(e) v → v.kind.width = s.width := fun v hv' => by
      have := hv'.deterministic (meaning_quote (dom := dom) hb hv e he)
      rw [this]
      cases s <;> rfl
    cases e with
    | boolInput j => exact input_spec (hb j he) (hub j hu)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact input_spec (hv j hj) (huv j hu.1)
    | boolLit b => exact bool_literal_spec b (by cases b <;> rfl) hmw
    | bitsLit w v =>
      exact literal_step_spec (us := [.zero]) rfl
        (show (quoteF dom w (fun j => Lean.Expr.fvar (vi j)) (.lit v)).getAppArgs.back? =
          some (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) from rfl)
        (litValue_natE w v he.1) rfl hmw
    | bitsNum w v =>
      exact literal_step_spec (us := [.zero]) rfl
        (show (numSigE dom w v).getAppArgs.back? = some (numLitE w v) from rfl)
        (litValue_numLitE w v he.1) rfl hmw
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      have ck := op_checks op dom Q(a) Q(b) w
      refine binary_step_spec op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 (by cases op <;> rfl) hmw ?_ ?_
      · show GoodR ctx inputs B P V (translateFuelFix translateStep fuel
          (binE dom w op Q(a) Q(b)).getAppArgs[(binE dom w op Q(a) Q(b)).getAppArgs.size - 2]!
          "op_a" false false)
        rw [ck.2.2.2.2.1]; exact (ih a ha ua "op_a" false).goodR
      · show GoodR ctx inputs B P V (translateFuelFix translateStep fuel
          (binE dom w op Q(a) Q(b)).getAppArgs[(binE dom w op Q(a) Q(b)).getAppArgs.size - 1]!
          "op_b" false false)
        rw [ck.2.2.2.2.2.1]; exact (ih b hb' ub' "op_b" false).goodR
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (compareE le dom w Q(a) Q(b)) hint false named)
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      apply Spec.cached
      refine SpecA.of_arm ?_ (by cases le <;> rfl) (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateBoolUncachedWith _ _ (compareE le dom w Q(a) Q(b)) hint false named)
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_arm (ih a ha ua "a" false).goodR (ih b hb' ub' "b" false).goodR
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolBinE kind dom Q(a) Q(b)) hint false named)
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      apply Spec.cached
      refine SpecA.of_arm ?_ (by cases kind <;> rfl) (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateBoolUncachedWith _ _ (boolBinE kind dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_arm (ih a ha ua "a" false).goodR (ih b hb' ub' "b" false).goodR
    | appCompare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appCompareE le dom w Q(a) Q(b)) hint false named)
      rw [appCompare_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appCompareE _ _ _ _ _)]
      apply Spec.cached
      refine SpecA.of_arm ?_ (by cases le <;> rfl) (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateBoolUncachedWith _ _ (appCompareE le dom w Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appCompare]
      exact appCompare_arm (ih a ha ua "app_arg" false).goodR (ih b hb' ub' "app_arg" false).goodR
    | appBool kind a b =>
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appBoolE kind dom Q(a) Q(b)) hint false named)
      rw [appBool_step, translateFallback_bool _ _ hint false named (isBoolControl_appBoolE _ _ _ _)]
      apply Spec.cached
      refine SpecA.of_arm ?_ (by cases kind <;> rfl) (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateBoolUncachedWith _ _ (appBoolE kind dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appBool]
      exact appBool_arm (ih a ha ua "app_arg" false).goodR (ih b hb' ub' "app_arg" false).goodR
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appBool2E f dom Q(a) Q(b)) hint false named)
      rw [appBool2_step, translateFallback_bool _ _ hint false named (isBoolControl_appBool2E _ _ _ _)]
      apply Spec.cached
      refine SpecA.of_arm ?_ (by cases f <;> rfl) (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateBoolUncachedWith _ _ (appBool2E f dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appBool2]
      exact appBool2_arm (ih a ha ua "app_arg" false).goodR (ih b hb' ub' "app_arg" false).goodR
    | boolNot a =>
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolNotE dom Q(a)) hint false named)
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateSignalCompare (translateFuelFix translateStep fuel) .eq Q(a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named)
      exact compare_arm (ih a he hu "a" false).goodR (ih (.boolLit false) trivial trivial "b" false).goodR
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolEqE dom Q(a) Q(b)) hint false named)
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateSignalCompare (translateFuelFix translateStep fuel) .eq Q(a) Q(b)
        hint named)
      exact compare_arm (ih a ha ua "a" false).goodR (ih b hb' ub' "b" false).goodR
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      obtain ⟨uc, ua, ub'⟩ := hu
      cases s with
      | bool =>
        show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
          (boolMuxE dom Q(c) Q(a) Q(b)) hint false named)
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply Spec.cached
        refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
        show Arm ctx inputs B P V _ (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named)
        exact mux_arm (ih c hc uc "mux_cond" false).goodR (ih a ha ua "mux_then" false).goodR
          (ih b hb' ub' "mux_else" false).goodR
      | bits w =>
        show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) Q(c) Q(a) Q(b)) hint false named)
        rw [vector_step]
        apply Spec.cached
        refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
        show Arm ctx inputs B P V _ (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) Q(c) Q(a) Q(b)) hint false named)
        rw [vectorMuxUncached_muxE]
        exact mux_arm (ih c hc uc "mux_cond" false).goodR (ih a ha ua "mux_then" false).goodR
          (ih b hb' ub' "mux_else" false).goodR
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      obtain ⟨ua, -⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (setwE dom w w' Q(a)) hint false named)
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' Q(a)) hint false named)
      rw [setwUncached_setwE]
      exact setw_arm (ih a ha ua "s" false).goodR
    | slice nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      obtain ⟨ua, -, -⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (sliceE dom nm w start len Q(a)) hint false named)
      rw [slice_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateSliceUncachedWith (translateFuelFix translateStep fuel) start len
        (sliceE dom nm w start len Q(a)) hint false named)
      rw [sliceUncached_sliceE]
      exact slice_arm (ih a ha ua "s" false).goodR
    | concat a b =>
      rename_i m n
      obtain ⟨ha, hb'⟩ := he
      obtain ⟨ua, ub'⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatE dom m n Q(a) Q(b)) hint false named)
      rw [concat_step _ _ _ _ _ _ _ _ _ (a.wf_pos ha) (b.wf_pos hb')]
      apply Spec.cached
      show SpecA ctx inputs B P V _ (translateConcatUncachedWith (translateFuelFix translateStep fuel) m n
        (concatE dom m n Q(a) Q(b)) hint false named)
      rw [concatUncached_concatE]
      exact concat_spec (canonicalConcat?_concatE dom _ _ (a.wf_pos ha) (b.wf_pos hb'))
        ⟨_, meaning_quote (dom := dom) hb hv a ha, rfl⟩ hmw
        (ih a ha ua "concat_hi" false) (ih b hb' ub' "concat_lo" false)
    | concatLitHi k v b =>
      rename_i n
      obtain ⟨hb', hk, hlt⟩ := he
      obtain ⟨ub', -, -⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatLitHiE dom k v n Q(b)) hint false named)
      rw [concatLitHi_step _ _ _ _ _ _ _ _ _ hk hlt (b.wf_pos hb')]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        true k v n (concatLitHiE dom k v n Q(b)) hint false named)
      rw [concatLitUncached_hiE]
      exact concatActs_arm concatConst_arm.goodR (ih b hb' ub' "concat_lo" false).goodR
    | concatLitLo a k v =>
      rename_i m
      obtain ⟨ha, hk, hlt⟩ := he
      obtain ⟨ua, -, -⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatLitLoE dom m k v Q(a)) hint false named)
      rw [concatLitLo_step _ _ _ _ _ _ _ _ _ hk hlt (a.wf_pos ha)]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        false k v m (concatLitLoE dom m k v Q(a)) hint false named)
      rw [concatLitUncached_loE]
      exact concatActs_arm (ih a ha ua "concat_hi" false).goodR concatConst_arm.goodR
    | zextMap nm k a =>
      rename_i n
      obtain ⟨ha, hk⟩ := he
      obtain ⟨ua, -⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (zextMapE dom nm k n Q(a)) hint false named)
      rw [zextMap_step _ _ _ _ _ _ _ _ _ hk (a.wf_pos ha)]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) n
        (k + n) (zextMapE dom nm k n Q(a)) hint false named)
      rw [setwUncached_zextMapE]
      exact setw_arm (ih a ha ua "s" false).goodR
    | sliceF nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      obtain ⟨ua, -, -⟩ := hu
      show Spec ctx inputs B P V _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (sliceFE dom nm w start len Q(a)) hint false named)
      rw [sliceF_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply Spec.cached
      refine SpecA.of_arm ?_ rfl (by first | rfl | (rename_i x; cases x <;> rfl)) hmw
      show Arm ctx inputs B P V _ (translateSliceFUncachedWith (translateFuelFix translateStep fuel)
        start len (sliceFE dom nm w start len Q(a)) hint false named)
      rw [sliceFUncached_sliceFE]
      exact slice_arm (ih a ha ua "a" false).goodR

/-- The real translator leaves the spine, the declarations and the order facts. -/
theorem translateExprToWire_spine {kb kv : Nat} {vw : Nat → Nat} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w} {ub uv : Nat → Prop}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j))))
    (hub : ∀ j, ub j → B (bi j)) (huv : ∀ j, uv j → B (vi j))
    {s : SType} (e : Term s) (he : e.WF kb kv vw) (hu : Uses ub uv e) (hint : String)
    (named : Bool) :
    Spec ctx inputs B P V Q(e) (translateExprToWire Q(e) hint false named) :=
  fuel_spine translateFuelLimit hb hv hub huv e he hu hint named

end Fuel

end Tools.ShippingUnifiedSpine
