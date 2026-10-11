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

/-- `n` links from `w`, following the expression `e`: while `e` is a canonical
concatenation `hi ++ lo` (the compiler's `canonicalConcat?`), `w` is driven by
a concat statement `{x, y}`, `x` is declared at `hi`'s width, and `y` has the
links of `lo`. -/
def SpineQ (wires : List Port) (body : List Stmt) : Nat → Lean.Expr → String → Prop
  | 0, _, _ => True
  | n + 1, e, w => ∀ m k a b, canonicalConcat? e = some (m, k, a, b) →
      ∃ x y, link w x y ∈ body ∧ Decl wires x m ∧ SpineQ wires body n b y

theorem SpineQ.mono {wires wires' : List Port} {body body' : List Stmt}
    (hw : ∀ p ∈ wires, p ∈ wires') (hb : ∀ st ∈ body, st ∈ body') :
    ∀ {n : Nat} {e : Lean.Expr} {w : String}, SpineQ wires body n e w → SpineQ wires' body' n e w
  | 0, _, _, _ => trivial
  | _ + 1, _, _, hs => fun m k a b he =>
    let ⟨x, y, hm, hd, hr⟩ := hs m k a b he
    ⟨x, y, hb _ hm, hd.mono hw, SpineQ.mono hw hb hr⟩

theorem SpineQ.of_none {wires : List Port} {body : List Stmt} {e : Lean.Expr} {w : String}
    (h : canonicalConcat? e = none) : ∀ n, SpineQ wires body n e w
  | 0 => trivial
  | _ + 1 => fun m k a b he => by rw [h] at he; cases he

/-- Statements and declarations are kept. -/
def Kept (s t : CircuitState) : Prop :=
  (∀ st ∈ s.module.body, st ∈ t.module.body) ∧ ∀ p ∈ s.module.wires, p ∈ t.module.wires

theorem Kept.refl (s : CircuitState) : Kept s s := ⟨fun _ h => h, fun _ h => h⟩
theorem Kept.trans {s t u : CircuitState} (h : Kept s t) (k : Kept t u) : Kept s u :=
  ⟨fun st hs => k.1 st (h.1 st hs), fun p hp => k.2 p (h.2 p hp)⟩

/-- **The record invariant**: every recorded wire has the links of the
expression it is recorded for, and is declared at the width of the value that
expression means. -/
def RecQ (inputs : FVarId → Option Value) (s : CircuitState) : Prop :=
  ∀ w e, s.translateRecord.get? w = some e →
    (∀ n, SpineQ s.module.wires s.module.body n e w) ∧
    ∀ v, Meaning inputs e v → Decl s.module.wires w v.kind.width

theorem RecQ.empty {inputs} {s : CircuitState} (h : s.translateRecord = {}) : RecQ inputs s := by
  intro w e he; simp [h] at he

/-- The state invariant: the record invariant; every input variable is bound
to a wire declared at its value's width (so translating one returns that wire
and changes nothing); and the PROTECTED names `P` (the input ports) are in use
— so no wire made from here on is one of them — and no statement drives one. -/
def St (ctx : CompilerState) (inputs : FVarId → Option Value) (P : String → Prop)
    (s : CircuitState) : Prop :=
  RecQ inputs s ∧
    (∀ id v, inputs id = some v → ∃ z, visible ctx s.sourceBindings id = some z ∧
      Decl s.module.wires z v.kind.width) ∧
    (∀ x, P x → s.usedNames.contains x = true) ∧
    (∀ l r, Stmt.assign l r ∈ s.module.body → ¬ P l)

/-- What every action does to the state: statements and declarations kept,
bindings unchanged, names in use stay in use. -/
def Ext (s t : CircuitState) : Prop :=
  Kept s t ∧ t.sourceBindings = s.sourceBindings ∧
    ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true

theorem Ext.refl (s : CircuitState) : Ext s s := ⟨Kept.refl s, rfl, fun _ h => h⟩
theorem Ext.trans {s t u : CircuitState} (h : Ext s t) (k : Ext t u) : Ext s u :=
  ⟨h.1.trans k.1, k.2.1.trans h.2.1, fun z hz => k.2.2 z (h.2.2 z hz)⟩

theorem St.transfer {ctx inputs P} {s t : CircuitState} (h : St ctx inputs P s)
    (hr : t.translateRecord = s.translateRecord) (hx : Ext s t)
    (hb : ∀ l r, Stmt.assign l r ∈ t.module.body → Stmt.assign l r ∈ s.module.body ∨ ¬ P l) :
    St ctx inputs P t :=
  ⟨fun w e he => ⟨fun n => ((h.1 w e (hr ▸ he)).1 n).mono hx.1.2 hx.1.1,
      fun v hv => ((h.1 w e (hr ▸ he)).2 v hv).mono hx.1.2⟩,
    fun id v hi => by
      obtain ⟨z, hz, hd⟩ := h.2.1 id v hi
      exact ⟨z, by rw [hx.2.1]; exact hz, hd.mono hx.1.2⟩,
    fun x hx' => hx.2.2 x (h.2.2.1 x hx'),
    fun l r hm => (hb l r hm).elim (h.2.2.2 l r) id⟩

/-- An action keeps the state invariant, the statements and the bindings. -/
def Good (ctx : CompilerState) (inputs : FVarId → Option Value) (P : String → Prop) {α : Type}
    (a : CompilerM α) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs P s → St ctx inputs P t ∧ Ext s t

variable {ctx : CompilerState} {inputs : FVarId → Option Value} {P : String → Prop}

theorem Good.pure {α : Type} (a : α) : Good ctx inputs P (Pure.pure a : CompilerM α) := by
  intro s t r hr hq
  obtain ⟨-, rfl⟩ := Returns.pure hr
  exact ⟨hq, Ext.refl _⟩

theorem Good.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    (hm : Good ctx inputs P m) (hf : ∀ a, Good ctx inputs P (f a)) : Good ctx inputs P (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, k1⟩ := hm s sm a h1 hq
  obtain ⟨q2, k2⟩ := hf a sm t r h2 q1
  exact ⟨q2, k1.trans k2⟩

theorem Good.throw {α : Type} (e : Exception) : Good ctx inputs P (throw e : CompilerM α) :=
  fun _ _ _ hr _ => (Returns.throw hr).elim

theorem Good.liftMetaM {α : Type} (x : MetaM α) : Good ctx inputs P (CompilerM.liftMetaM x) := by
  intro s t r hr hq
  obtain rfl := Returns.liftMetaM hr
  exact ⟨hq, Ext.refl _⟩

/-- What `makeWire` does: a name not in use before (so not a protected one),
declared at the given type; nothing else that the invariant reads. -/
theorem makeWire_facts {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {s t : CircuitState} {r : String}
    (hr : Returns (CompilerM.makeWire hint ty named) ctx s r t) (hq : St ctx inputs P s) :
    St ctx inputs P t ∧ Ext s t ∧ ¬ P r ∧ Decl t.module.wires r ty.bitWidth := by
  obtain ⟨hn, ht⟩ := makeWire_returns hr
  obtain ⟨hf, hu, hb, hw⟩ := CircuitM.makeWire_spec hint ty named s
  rw [← hn] at hf hu hw
  subst ht
  have hx : Ext s (CircuitM.makeWire hint ty named s).2 :=
    ⟨⟨fun st hs => by rw [hb]; exact hs, fun p hp => by rw [hw]; exact List.mem_cons_of_mem _ hp⟩,
      CircuitM.makeWire_sourceBindings _ _ _ _,
      fun z hz => by rw [hu]; simp [Std.HashSet.contains_insert, hz]⟩
  refine ⟨hq.transfer (CircuitM.makeWire_translateRecord _ _ _ _) hx
    (fun l r' hm => Or.inl (hb ▸ hm)), hx, fun hp => ?_, ty, by rw [hw]; exact List.mem_cons_self .., rfl⟩
  have := hq.2.2.1 r hp
  rw [hf] at this
  cases this

theorem Good.makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    Good ctx inputs P (CompilerM.makeWire hint ty named) :=
  fun _ _ _ hr hq => ⟨(makeWire_facts hr hq).1, (makeWire_facts hr hq).2.1⟩

/-- A bind of `makeWire`: the wire it returns is not a protected name. -/
theorem Good.bindMake {β : Type} {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {f : String → CompilerM β} (hf : ∀ r, ¬ P r → Good ctx inputs P (f r)) :
    Good ctx inputs P (CompilerM.makeWire hint ty named >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, k1, hp, -⟩ := makeWire_facts h1 hq
  obtain ⟨q2, k2⟩ := hf a hp sm t r h2 q1
  exact ⟨q2, k1.trans k2⟩

theorem emitAssign_ext (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    Ext s (CircuitM.emitAssign lhs rhs s).2 :=
  ⟨⟨fun st hs => by rw [emitAssign_body_cons]; exact List.mem_cons_of_mem _ hs,
      fun p hp => by rw [emitAssign_wires]; exact hp⟩, rfl,
    fun z hz => by rw [emitAssign_usedNames]; exact hz⟩

/-- An assignment to a name that is not protected. -/
theorem Good.emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) (hl : ¬ P lhs) :
    Good ctx inputs P (CompilerM.emitAssign lhs rhs) := by
  intro s t r hr hq
  have ht := emitAssign_returns hr
  subst ht
  refine ⟨hq.transfer (emitAssign_translateRecord _ _ _) (emitAssign_ext _ _ _) (fun l r' hm => ?_),
    emitAssign_ext _ _ _⟩
  rw [emitAssign_body_cons] at hm
  rcases List.mem_cons.mp hm with heq | hin
  · cases heq; exact Or.inr hl
  · exact Or.inl hin

theorem Good.lookupVar (id : FVarId) : Good ctx inputs P (CompilerM.lookupVar id) := by
  intro s t r hr hq
  obtain ⟨-, rfl⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns hr
  exact ⟨hq, Ext.refl _⟩

/-- The wire an action returns is declared at width `N`. -/
def Last (ctx : CompilerState) (inputs : FVarId → Option Value) (P : String → Prop) (N : Nat)
    (a : CompilerM String) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx inputs P s → Decl t.module.wires r N

theorem Last.bind {α : Type} {N : Nat} {m : CompilerM α} {f : α → CompilerM String}
    (hm : Good ctx inputs P m) (hf : ∀ a, Last ctx inputs P N (f a)) :
    Last ctx inputs P N (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  exact hf a sm t r h2 (hm s sm a h1 hq).1

/-- A result wire made, assigned and returned. -/
theorem Last.emit {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {rhs : String → Sparkle.IR.AST.Expr} :
    Last ctx inputs P ty.bitWidth (CompilerM.makeWire hint ty named >>= fun r =>
      CompilerM.emitAssign r (rhs r) >>= fun _ => Pure.pure r) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨u, sn, h3, h4⟩ := Returns.bind h2
  obtain ⟨rfl, rfl⟩ := Returns.pure h4
  obtain ⟨-, -, -, hd⟩ := makeWire_facts h1 hq
  have ht := emitAssign_returns h3
  subst ht
  exact hd.mono (emitAssign_ext _ _ _).1.2

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
    {f : String → CompilerM String} (hf : ∀ r, ¬ P r → Good ctx inputs P (f r))
    (hret : ∀ r, Ret ctx r (f r)) :
    Last ctx inputs P ty.bitWidth (CompilerM.makeWire hint ty named >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, -, hp, hd⟩ := makeWire_facts h1 hq
  obtain rfl := hret a sm t r h2
  exact hd.mono (hf _ hp sm t _ h2 q1).2.1.2

-- (the rules are matched on the operations' names: unfolding them while
-- unifying a rule with another program is what makes a failed match slow)
attribute [local irreducible] CompilerM.makeWire CompilerM.emitAssign CompilerM.lookupVar

/-- The walk: binds, `pure`, the builder's operations, branches, and the
hypotheses in scope. -/
macro "good" : tactic => `(tactic| repeat (first
  | assumption
  | exact Good.pure _
  | exact Good.makeWire _ _ _
  | exact Good.emitAssign _ _ (by assumption)
  | refine Good.bindMake (fun _ _ => ?_)
  | exact Good.liftMetaM _
  | exact Good.lookupVar _
  | exact Good.throw _
  | refine Good.bind ?_ (fun _ => ?_)
  | split
  | intro _))

/-- The declared width of the result: skip to the final emit. -/
macro "last" : tactic => `(tactic| repeat (first
  | exact Last.emit
  | refine Last.bind (by assumption) (fun _ => ?_)))

/-- An arm: it keeps the invariant, and its result is declared at width `N`. -/
def Arm (ctx : CompilerState) (inputs : FVarId → Option Value) (P : String → Prop) (N : Nat)
    (a : CompilerM String) : Prop :=
  Good ctx inputs P a ∧ Last ctx inputs P N a

/-! ## The arms that are not a concatenation -/

section Arms
variable {rec : TranslateFn} {ae be ce : Lean.Expr} {hint : String} {named : Bool}

theorem compare_arm {le : SignalCompareKind}
    (oa : Good ctx inputs P (rec ae "a" false false)) (ob : Good ctx inputs P (rec be "b" false false)) :
    Arm ctx inputs P 1 (translateSignalCompare rec le ae be hint named) := by
  constructor <;> unfold translateSignalCompare emitCompareResult emitBoolResult
  · good
  · last

theorem appCompare_arm {le : SignalCompareKind}
    (oa : Good ctx inputs P (rec ae "app_arg" false false))
    (ob : Good ctx inputs P (rec be "app_arg" false false)) :
    Arm ctx inputs P 1 (translateAppCompare rec le ae be hint named) := by
  constructor <;> unfold translateAppCompare emitCompareResult emitBoolResult
  · good
  · last

theorem boolBin_arm {kind : SignalBoolBinKind}
    (oa : Good ctx inputs P (rec ae "a" false false)) (ob : Good ctx inputs P (rec be "b" false false)) :
    Arm ctx inputs P 1 (translateBoolBinary rec kind ae be hint named) := by
  constructor <;> unfold translateBoolBinary emitBoolResult
  · good
  · last

theorem appBool_arm {kind : SignalBoolBinKind}
    (oa : Good ctx inputs P (rec ae "app_arg" false false))
    (ob : Good ctx inputs P (rec be "app_arg" false false)) :
    Arm ctx inputs P 1 (translateAppBoolBinary rec kind ae be hint named) := by
  constructor <;> unfold translateAppBoolBinary emitBoolResult
  · good
  · last

theorem emitBool_good (rhs : Sparkle.IR.AST.Expr) (hint : String) (named : Bool) :
    Good ctx inputs P (emitBoolResult rhs hint named) := by
  unfold emitBoolResult; good

theorem appBool2_arm {f : AppBool2}
    (oa : Good ctx inputs P (rec ae "app_arg" false false))
    (ob : Good ctx inputs P (rec be "app_arg" false false)) :
    Arm ctx inputs P 1 (translateAppBool2 rec f ae be hint named) := by
  constructor
  · unfold translateAppBool2 emitBoolResult; good
  · unfold translateAppBool2
    refine Last.bind oa (fun _ => Last.bind ob (fun _ => Last.bind (emitBool_good _ _ _) (fun _ => ?_)))
    unfold emitBoolResult
    exact Last.emit

theorem mux_arm {ty : Sparkle.IR.Type.HWType}
    (oc : Good ctx inputs P (rec ce "mux_cond" false false))
    (oa : Good ctx inputs P (rec ae "mux_then" false false))
    (ob : Good ctx inputs P (rec be "mux_else" false false)) :
    Arm ctx inputs P ty.bitWidth (translateMuxWith rec (pure ty) ce ae be hint named) := by
  constructor <;> unfold translateMuxWith emitMuxResult
  · good
  · refine Last.bind oc (fun _ => Last.bind oa (fun _ => Last.bind ob (fun _ => ?_)))
    intro s t r hr hq
    obtain ⟨x, sm, h1, h2⟩ := Returns.bind hr
    obtain ⟨rfl, rfl⟩ := Returns.pure h1
    exact Last.emit _ _ _ h2 hq

theorem setw_arm {ws wt : Nat} (oa : Good ctx inputs P (rec ae "s" false false)) :
    Arm ctx inputs P wt (do
      let sw ← rec ae "s" false false
      emitCastResult (setwRhs ws wt sw) wt hint named) := by
  constructor <;> unfold emitCastResult
  · good
  · exact Last.bind oa (fun _ => Last.emit (ty := .bitVector wt))

theorem hwTypeFromWidth_bitWidth (len : Nat) :
    (Sparkle.IR.Type.hwTypeFromWidth len).bitWidth = len := by
  unfold Sparkle.IR.Type.hwTypeFromWidth
  split
  · rename_i h; simp at h; subst h; rfl
  · rfl

theorem slice_arm {hd : String} {start len : Nat} (oa : Good ctx inputs P (rec ae hd false false)) :
    Arm ctx inputs P len (do
      let sw ← rec ae hd false false
      emitSliceResult (sliceRhs start len sw) len hint named) := by
  constructor <;> unfold emitSliceResult
  · good
  · have := Last.bind (N := (Sparkle.IR.Type.hwTypeFromWidth len).bitWidth) oa
      (fun sw => Last.emit (ctx := ctx) (inputs := inputs) (P := P) (hint := hint)
        (ty := Sparkle.IR.Type.hwTypeFromWidth len) (named := named)
        (rhs := fun _ => sliceRhs start len sw))
    rw [hwTypeFromWidth_bitWidth] at this
    exact this

theorem concatConst_good {k v : Nat} : Good ctx inputs P (emitConcatConst k v) := by
  unfold emitConcatConst emitCastResult; good

theorem concatActs_arm {wd : Nat} {hiAct loAct : CompilerM String}
    (oa : Good ctx inputs P hiAct) (ob : Good ctx inputs P loAct) :
    Arm ctx inputs P wd (translateConcatActs wd hiAct loAct hint named) := by
  constructor <;> unfold translateConcatActs
  · good
  · refine Last.makeFirst (ty := .bitVector wd) (fun r hr => ?_) (fun r => ?_)
    · good
    · exact Ret.bind (fun _ => Ret.bind (fun _ => Ret.bind (fun _ => Ret.pure r)))

end Arms

/-! ## The result's links and declaration -/

/-- An action for the expression `e`: it keeps the invariant, the statements
and the bindings; the wire it returns has the links of `e` and is declared at
the width of the value `e` means. -/
def Spec (ctx : CompilerState) (inputs : FVarId → Option Value) (P : String → Prop)
    (e : Lean.Expr) (a : CompilerM String) : Prop :=
  ∀ s t w, Returns a ctx s w t → St ctx inputs P s →
    St ctx inputs P t ∧ Ext s t ∧ (∀ n, SpineQ t.module.wires t.module.body n e w) ∧
      ∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width

theorem Spec.good {e : Lean.Expr} {a : CompilerM String} (h : Spec ctx inputs P e a) :
    Good ctx inputs P a :=
  fun s t r hr hq => ⟨(h s t r hr hq).1, (h s t r hr hq).2.1⟩

/-- For an expression that is not a canonical concatenation: the arm, and the
width its value has. -/
theorem Spec.of_arm {e : Lean.Expr} {a : CompilerM String} {N : Nat} (ha : Arm ctx inputs P N a)
    (hn : canonicalConcat? e = none) (hm : ∀ v, Meaning inputs e v → v.kind.width = N) :
    Spec ctx inputs P e a :=
  fun s t r hr hq => ⟨(ha.1 s t r hr hq).1, (ha.1 s t r hr hq).2, SpineQ.of_none hn,
    fun v hv => by rw [hm v hv]; exact ha.2 s t r hr hq⟩

/-- A record of the result keeps the record invariant: the result has its
links and its declaration. -/
theorem St.record {s : CircuitState} {e : Lean.Expr} {w : String} (h : St ctx inputs P s)
    (hw : ∀ n, SpineQ s.module.wires s.module.body n e w)
    (hd : ∀ v, Meaning inputs e v → Decl s.module.wires w v.kind.width) :
    St ctx inputs P { s with translateRecord := s.translateRecord.insert w e } := by
  refine ⟨fun w' e' he' => ?_, h.2⟩
  rw [Std.HashMap.get?_insert] at he'
  split at he'
  · rename_i hww
    cases he'
    rw [← (beq_iff_eq.mp hww)]
    exact ⟨hw, hd⟩
  · exact h.1 w' e' he'

/-- **The validated cache wrapper**: a hit returns a recorded wire — it has
its links and declaration by the record invariant; a miss lowers and records
the result. -/
theorem Spec.cached {lower : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (h : Spec ctx inputs P e (lower e hint top named)) :
    Spec ctx inputs P e (translateControlCachedWith lower e hint top named) := by
  intro s t w hr hq
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hrec⟩ := cacheLookupValidated_returns hit
    subst hs
    exact ⟨hq, Ext.refl _, (hq.1 w e (hrec w rfl)).1, (hq.1 w e (hrec w rfl)).2⟩
  · obtain ⟨q, k, sp, sd⟩ := h s sm w miss hq
    have ht := recordTranslation_returns record
    subst ht
    exact ⟨q.record sp sd, k, sp, sd⟩

/-- **The concat arm**: the result wire is driven by `{hi, lo}`; `hi` is
declared at the high operand's width; `lo` has the links of the low operand;
the result is declared at the sum. -/
theorem concat_spec {e a b : Lean.Expr} {m k : Nat} {hint : String} {named : Bool}
    {hiAct loAct : CompilerM String} (he : canonicalConcat? e = some (m, k, a, b))
    (hma : ∃ v, Meaning inputs a v ∧ v.kind.width = m)
    (hm : ∀ v, Meaning inputs e v → v.kind.width = m + k)
    (oa : Spec ctx inputs P a hiAct) (ob : Spec ctx inputs P b loAct) :
    Spec ctx inputs P e (translateConcatActs (m + k) hiAct loAct hint named) := by
  intro s t w hr hq
  have harm := concatActs_arm (hint := hint) (named := named) (wd := m + k) oa.good ob.good
  have hg := harm.1 s t w hr hq
  refine ⟨hg.1, hg.2, ?_, fun v hv => by rw [hm v hv]; exact harm.2 s t w hr hq⟩
  unfold translateConcatActs at hr
  obtain ⟨res, sA, hmk, rest⟩ := Returns.bind hr
  obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
  obtain ⟨wb, sC, hb', rest⟩ := Returns.bind rest
  obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
  obtain ⟨hwv, ht⟩ := Returns.pure ret
  subst ht
  subst hwv
  obtain ⟨qA, -⟩ := Good.makeWire (ctx := ctx) (inputs := inputs) (P := P) _ _ _ s sA w hmk hq
  obtain ⟨qB, -, -, hda⟩ := oa sA sB wa ha qA
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
    refine ⟨wa, wb, by rw [emitAssign_body_cons]; exact List.mem_cons_self .., ?_, ?_⟩
    · rw [← hwa]
      exact (hda va hva).mono (xBC.1.trans xCD.1).2
    · exact (spb n).mono xCD.1.2 xCD.1.1

/-! ## One step of the knot, for an expression that is not a concatenation -/

/-- **The step**, for `e` not a canonical concatenation: the validated lookup
(a hit changes nothing), the core, the record of its result, or the fallback
when the core declines. -/
theorem step_spec {rec : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (hn : canonicalConcat? e = none)
    (hcore : Good ctx inputs P (translateCore rec e hint top named))
    (hres : ∀ s t z, Returns (translateCore rec e hint top named) ctx s (some z) t →
      St ctx inputs P s → ∀ v, Meaning inputs e v → Decl t.module.wires z v.kind.width)
    (hfb : ∀ s t, St ctx inputs P s → Returns (translateCore rec e hint top named) ctx s none t →
      Spec ctx inputs P e (translateFallback rec e hint top named)) :
    Spec ctx inputs P e (translateStepWith translateFallback rec e hint top named) := by
  have cont : ∀ {s t w} {K : Option String → CompilerM String} (c : Bool),
      (∀ z, K (some z) = Pure.pure z ∨
        K (some z) = (recordTranslation e z c >>= fun _ => Pure.pure z) ∨
        K (some z) = (if e.isFVar = true then Pure.pure z
          else recordTranslation e z c >>= fun _ => Pure.pure z)) →
      K none = translateFallback rec e hint top named →
      Returns (translateCore rec e hint top named >>= K) ctx s w t → St ctx inputs P s →
      St ctx inputs P t ∧ Ext s t ∧ (∀ n, SpineQ t.module.wires t.module.body n e w) ∧
        ∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width := by
    intro s t w K c hsome hnone hr hq
    obtain ⟨r, sc, hc, rest⟩ := Returns.bind hr
    obtain ⟨qc, kc⟩ := hcore s sc r hc hq
    cases r with
    | some z =>
      have hdz := hres s sc z hc hq
      have hp : ∀ {t w}, Returns (Pure.pure z : CompilerM String) ctx sc w t →
          St ctx inputs P t ∧ Ext s t ∧ (∀ n, SpineQ t.module.wires t.module.body n e w) ∧
            ∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width := by
        intro t w h
        obtain ⟨rfl, rfl⟩ := Returns.pure h
        exact ⟨qc, kc, SpineQ.of_none hn, hdz⟩
      have hrc : ∀ {t w}, Returns (recordTranslation e z c >>= fun _ => (Pure.pure z : CompilerM String))
          ctx sc w t → St ctx inputs P t ∧ Ext s t ∧
            (∀ n, SpineQ t.module.wires t.module.body n e w) ∧
            ∀ v, Meaning inputs e v → Decl t.module.wires w v.kind.width := by
        intro t w h
        obtain ⟨u, sr, record, ret⟩ := Returns.bind h
        obtain ⟨rfl, rfl⟩ := Returns.pure ret
        have hs := recordTranslation_returns record
        subst hs
        exact ⟨qc.record (SpineQ.of_none hn) hdz, kc.trans ⟨Kept.refl _, rfl, fun _ h => h⟩,
          SpineQ.of_none hn, hdz⟩
      rcases hsome z with hk | hk | hk <;> rw [hk] at rest
      · exact hp rest
      · exact hrc rest
      · split at rest
        · exact hp rest
        · exact hrc rest
    | none =>
      rw [hnone] at rest
      obtain ⟨q, k, sp, sd⟩ := hfb s sc hq hc sc t w rest qc
      exact ⟨q, kc.trans k, sp, sd⟩
  intro s t w hr hq
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  all_goals first
    | exact cont _ (fun z => by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) rfl hr hq
    | (obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
       obtain ⟨hs, hrec⟩ := cacheLookupValidated_returns rh
       subst hs
       cases hit with
       | some w' =>
         obtain ⟨hw, ht⟩ := Returns.pure hr
         subst ht hw
         exact ⟨hq, Ext.refl _, (hq.1 _ e (hrec _ rfl)).1, (hq.1 _ e (hrec _ rfl)).2⟩
       | none => exact cont _ (fun z => by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) rfl hr hq)

/-! ## The step's own cases: a bound variable, a literal, a library operator -/

theorem pureLiteral_good (args : Array Lean.Expr) (hint : String) (named : Bool) :
    Good ctx inputs P (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?; good

/-- A bound variable: its wire, declared at the variable's width; nothing changes. -/
theorem input_spec {rec : TranslateFn} {id : FVarId} {v₀ : Value} {hint : String} {named : Bool}
    (hi : inputs id = some v₀) :
    Spec ctx inputs P (.fvar id) (translateStepWith translateFallback rec (.fvar id) hint false named) := by
  refine step_spec rfl (Good.lookupVar id) ?_ ?_
  · intro s t z hr hq v hv
    obtain ⟨hz, rfl⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns (id := id) hr
    obtain ⟨z', hbound, hd⟩ := hq.2.1 id v₀ hi
    rw [hbound] at hz
    cases hz
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
    Spec ctx inputs P e (translateStepWith translateFallback rec e hint false named) := by
  have hcore : translateCore rec e hint false named =
      translateSignalPureLiteral? e.getAppArgs hint named := by
    unfold translateCore
    split
    · simp [Lean.Expr.getAppFn] at fn
    · rw [fn]; simp only [beq_self_eq_true, if_true]
  refine step_spec hn (by rw [hcore]; exact pureLiteral_good _ _ _) ?_ ?_
  · intro s t z hr hq x hx
    rw [hm x hx]
    rw [hcore] at hr
    unfold translateSignalPureLiteral? at hr
    rw [back] at hr
    simp only [Option.bind_some, lit] at hr
    obtain ⟨w, sm, mk, rest⟩ := Returns.bind hr
    obtain ⟨u, se, em, rest⟩ := Returns.bind rest
    obtain ⟨hres, rfl⟩ := Returns.pure rest
    cases hres
    obtain ⟨-, -, -, hd⟩ := makeWire_facts mk hq
    have ht := emitAssign_returns em
    subst ht
    exact hd.mono (emitAssign_ext _ _ _).1.2
  · intro s t hq hr
    rw [hcore] at hr
    obtain ⟨w', hw'⟩ := literal_payload_some back lit hr
    cases hw'

/-- The Bool literal: the core declines, the fallback emits it under the
validated cache. -/
theorem bool_literal_spec {rec : TranslateFn} {dom : Lean.Expr} {hint : String} {named : Bool}
    (b : Bool) (hn : canonicalConcat? (literalE dom b) = none)
    (hm : ∀ x, Meaning inputs (literalE dom b) x → x.kind.width = 1) :
    Spec ctx inputs P (literalE dom b)
      (translateStepWith translateFallback rec (literalE dom b) hint false named) := by
  refine step_spec hn (by rw [literal_core]; exact Good.pure _) ?_ ?_
  · intro s t z hr
    rw [literal_core] at hr
    cases (Returns.pure hr).1
  · intro s t hq hr
    rw [translateFallback_bool rec _ hint false named (by cases b <;> rfl)]
    refine Spec.cached (Spec.of_arm (N := 1) ?_ hn hm)
    show Arm ctx inputs P 1 (translateBoolUncachedWith rec _ _ hint false named)
    rw [literal_uncached]
    constructor <;> unfold emitBoolLiteral emitBoolResult
    · good
    · exact Last.emit (ty := .bit)

/-- A canonical library operator: the result wire, the two operands, the assign. -/
theorem binary_step_spec {rec : TranslateFn} {e : Lean.Expr} {m : Name} {us : List Level}
    {hint : String} {named : Bool} {n : Nat} (op : Binary)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (hn : canonicalConcat? e = none) (hm : ∀ x, Meaning inputs e x → x.kind.width = n)
    (oa : Good ctx inputs P (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false))
    (ob : Good ctx inputs P (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false)) :
    Spec ctx inputs P e (translateStepWith translateFallback rec e hint false named) := by
  have hbin : Arm ctx inputs P n
      (translateCanonicalSignalBinary rec e op.operator e.getAppArgs true true hint named) := by
    constructor <;> unfold translateCanonicalSignalBinary <;> simp only [width, if_true]
    · good
    · intro s t r hr hq
      obtain ⟨ty, sm, h1, h2⟩ := Returns.bind hr
      obtain ⟨rfl, rfl⟩ := Returns.pure h1
      refine Last.makeFirst (ty := .bitVector n) (fun r hr => ?_) (fun r => ?_) _ t r h2 hq
      · good
      · exact Ret.bind (fun _ => Ret.bind (fun _ => Ret.bind (fun _ => Ret.pure r)))
  refine step_spec hn ?_ ?_ ?_
  · intro s t r hr hq
    obtain ⟨w, -, lower⟩ := core_binary_returns fn hop kinds width hr
    exact hbin.1 s t w lower hq
  · intro s t z hr hq x hx
    obtain ⟨w, hw, lower⟩ := core_binary_returns fn hop kinds width hr
    cases hw
    rw [hm x hx]
    exact hbin.2 s t z lower hq
  · intro s t hq hr
    obtain ⟨w, hw, -⟩ := core_binary_returns fn hop kinds width hr
    cases hw

/-! ## The fuel induction -/

section Fuel
variable {dom : Lean.Expr} {bi vi : Nat → FVarId}

local notation "Q(" e ")" =>
  quote dom (fun j => Lean.Expr.fvar (bi j)) (fun j => Lean.Expr.fvar (vi j)) e

set_option maxHeartbeats 1000000 in
/-- **The translator leaves the spine and the declarations**, at every fuel,
for every quoted well-formed term: it keeps the invariant, the statements and
the bindings; the wire it returns has the links of the term's expression and
is declared at the term's width. -/
theorem fuel_spine (fuel : Nat) {kb kv : Nat} {vw : Nat → Nat} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → ∀ hint named,
      Spec ctx inputs P Q(e) (translateFuelFix translateStep fuel Q(e) hint false named) := by
  induction fuel with
  | zero =>
    intro s e he hint named s' t w hr hq
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hint named
    change Spec ctx inputs P _ (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named)
    have hmw : ∀ v, Meaning inputs Q(e) v → v.kind.width = s.width := fun v hv' => by
      have := hv'.deterministic (meaning_quote (dom := dom) hb hv e he)
      rw [this]
      cases s <;> rfl
    cases e with
    | boolInput j => exact input_spec (hb j he)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact input_spec (hv j hj)
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
      have ck := op_checks op dom Q(a) Q(b) w
      refine binary_step_spec op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 (by cases op <;> rfl) hmw ?_ ?_
      · show Good ctx inputs P (translateFuelFix translateStep fuel
          (binE dom w op Q(a) Q(b)).getAppArgs[(binE dom w op Q(a) Q(b)).getAppArgs.size - 2]!
          "op_a" false false)
        rw [ck.2.2.2.2.1]; exact (ih a ha "op_a" false).good
      · show Good ctx inputs P (translateFuelFix translateStep fuel
          (binE dom w op Q(a) Q(b)).getAppArgs[(binE dom w op Q(a) Q(b)).getAppArgs.size - 1]!
          "op_b" false false)
        rw [ck.2.2.2.2.2.1]; exact (ih b hb' "op_b" false).good
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (compareE le dom w Q(a) Q(b)) hint false named)
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      apply Spec.cached
      refine Spec.of_arm ?_ (by cases le <;> rfl) hmw
      show Arm ctx inputs P _ (translateBoolUncachedWith _ _ (compareE le dom w Q(a) Q(b)) hint false named)
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_arm (ih a ha "a" false).good (ih b hb' "b" false).good
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolBinE kind dom Q(a) Q(b)) hint false named)
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      apply Spec.cached
      refine Spec.of_arm ?_ (by cases kind <;> rfl) hmw
      show Arm ctx inputs P _ (translateBoolUncachedWith _ _ (boolBinE kind dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_arm (ih a ha "a" false).good (ih b hb' "b" false).good
    | appCompare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appCompareE le dom w Q(a) Q(b)) hint false named)
      rw [appCompare_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appCompareE _ _ _ _ _)]
      apply Spec.cached
      refine Spec.of_arm ?_ (by cases le <;> rfl) hmw
      show Arm ctx inputs P _ (translateBoolUncachedWith _ _ (appCompareE le dom w Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appCompare]
      exact appCompare_arm (ih a ha "app_arg" false).good (ih b hb' "app_arg" false).good
    | appBool kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appBoolE kind dom Q(a) Q(b)) hint false named)
      rw [appBool_step, translateFallback_bool _ _ hint false named (isBoolControl_appBoolE _ _ _ _)]
      apply Spec.cached
      refine Spec.of_arm ?_ (by cases kind <;> rfl) hmw
      show Arm ctx inputs P _ (translateBoolUncachedWith _ _ (appBoolE kind dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appBool]
      exact appBool_arm (ih a ha "app_arg" false).good (ih b hb' "app_arg" false).good
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appBool2E f dom Q(a) Q(b)) hint false named)
      rw [appBool2_step, translateFallback_bool _ _ hint false named (isBoolControl_appBool2E _ _ _ _)]
      apply Spec.cached
      refine Spec.of_arm ?_ (by cases f <;> rfl) hmw
      show Arm ctx inputs P _ (translateBoolUncachedWith _ _ (appBool2E f dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appBool2]
      exact appBool2_arm (ih a ha "app_arg" false).good (ih b hb' "app_arg" false).good
    | boolNot a =>
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolNotE dom Q(a)) hint false named)
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateSignalCompare (translateFuelFix translateStep fuel) .eq Q(a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named)
      exact compare_arm (ih a he "a" false).good (ih (.boolLit false) trivial "b" false).good
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolEqE dom Q(a) Q(b)) hint false named)
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateSignalCompare (translateFuelFix translateStep fuel) .eq Q(a) Q(b)
        hint named)
      exact compare_arm (ih a ha "a" false).good (ih b hb' "b" false).good
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
          (boolMuxE dom Q(c) Q(a) Q(b)) hint false named)
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply Spec.cached
        refine Spec.of_arm ?_ rfl hmw
        show Arm ctx inputs P _ (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named)
        exact mux_arm (ih c hc "mux_cond" false).good (ih a ha "mux_then" false).good
          (ih b hb' "mux_else" false).good
      | bits w =>
        show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) Q(c) Q(a) Q(b)) hint false named)
        rw [vector_step]
        apply Spec.cached
        refine Spec.of_arm ?_ rfl hmw
        show Arm ctx inputs P _ (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) Q(c) Q(a) Q(b)) hint false named)
        rw [vectorMuxUncached_muxE]
        exact mux_arm (ih c hc "mux_cond" false).good (ih a ha "mux_then" false).good
          (ih b hb' "mux_else" false).good
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (setwE dom w w' Q(a)) hint false named)
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' Q(a)) hint false named)
      rw [setwUncached_setwE]
      exact setw_arm (ih a ha "s" false).good
    | slice nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (sliceE dom nm w start len Q(a)) hint false named)
      rw [slice_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateSliceUncachedWith (translateFuelFix translateStep fuel) start len
        (sliceE dom nm w start len Q(a)) hint false named)
      rw [sliceUncached_sliceE]
      exact slice_arm (ih a ha "s" false).good
    | concat a b =>
      rename_i m n
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatE dom m n Q(a) Q(b)) hint false named)
      rw [concat_step _ _ _ _ _ _ _ _ _ (a.wf_pos ha) (b.wf_pos hb')]
      apply Spec.cached
      show Spec ctx inputs P _ (translateConcatUncachedWith (translateFuelFix translateStep fuel) m n
        (concatE dom m n Q(a) Q(b)) hint false named)
      rw [concatUncached_concatE]
      exact concat_spec (canonicalConcat?_concatE dom _ _ (a.wf_pos ha) (b.wf_pos hb'))
        ⟨_, meaning_quote (dom := dom) hb hv a ha, rfl⟩ hmw
        (ih a ha "concat_hi" false) (ih b hb' "concat_lo" false)
    | concatLitHi k v b =>
      rename_i n
      obtain ⟨hb', hk, hlt⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatLitHiE dom k v n Q(b)) hint false named)
      rw [concatLitHi_step _ _ _ _ _ _ _ _ _ hk hlt (b.wf_pos hb')]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        true k v n (concatLitHiE dom k v n Q(b)) hint false named)
      rw [concatLitUncached_hiE]
      exact concatActs_arm concatConst_good (ih b hb' "concat_lo" false).good
    | concatLitLo a k v =>
      rename_i m
      obtain ⟨ha, hk, hlt⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatLitLoE dom m k v Q(a)) hint false named)
      rw [concatLitLo_step _ _ _ _ _ _ _ _ _ hk hlt (a.wf_pos ha)]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        false k v m (concatLitLoE dom m k v Q(a)) hint false named)
      rw [concatLitUncached_loE]
      exact concatActs_arm (ih a ha "concat_hi" false).good concatConst_good
    | zextMap nm k a =>
      rename_i n
      obtain ⟨ha, hk⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (zextMapE dom nm k n Q(a)) hint false named)
      rw [zextMap_step _ _ _ _ _ _ _ _ _ hk (a.wf_pos ha)]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) n
        (k + n) (zextMapE dom nm k n Q(a)) hint false named)
      rw [setwUncached_zextMapE]
      exact setw_arm (ih a ha "s" false).good
    | sliceF nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show Spec ctx inputs P _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (sliceFE dom nm w start len Q(a)) hint false named)
      rw [sliceF_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply Spec.cached
      refine Spec.of_arm ?_ rfl hmw
      show Arm ctx inputs P _ (translateSliceFUncachedWith (translateFuelFix translateStep fuel)
        start len (sliceFE dom nm w start len Q(a)) hint false named)
      rw [sliceFUncached_sliceFE]
      exact slice_arm (ih a ha "a" false).good

/-- The real translator leaves the spine and the declarations. -/
theorem translateExprToWire_spine {kb kv : Nat} {vw : Nat → Nat} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j))))
    {s : SType} (e : Term s) (he : e.WF kb kv vw) (hint : String) (named : Bool) :
    Spec ctx inputs P Q(e) (translateExprToWire Q(e) hint false named) :=
  fuel_spine translateFuelLimit hb hv e he hint named

end Fuel


end Tools.ShippingUnifiedSpine
