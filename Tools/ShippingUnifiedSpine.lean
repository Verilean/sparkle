import Tools.ShippingUnifiedProtection

/-! # The concatenation spine of the translator's output

`closeLets` walks, from the packed wire, one `assign w = {a, b}` per `let`
port. This file proves the translator leaves those statements: a structural
invariant on the builder state, alongside the semantic contract and the order
invariant of `Tools/ShippingUnifiedProtection.lean`.

* The cache is the real one: `translateRecord : wire → Lean.Expr`. The
  invariant (`RecQ`) says every recorded wire has the links of the expression
  it is recorded for (`SpineQ`): while the expression is a canonical
  concatenation — by the compiler's own recognizer `canonicalConcat?`, the
  one `fallbackKind` dispatches on — the wire is driven by a concat statement
  whose low operand has the links of the low operand expression.
* Membership, not position: statements are only ever added (`Kept`). That a
  wire has ONE driver is the order invariant's (`Acyclic`), used where the
  spine is read off the final body.
* Every path is covered: a fresh concat (`concat_spec`), a validated-cache
  hit and a miss with its record (`Spec.cached`), an overwrite of a record
  (`St.record`: the new record's wire has its expression's links), a bound
  variable returning an existing wire, and every arm that is not a
  concatenation (`Good`, by a walk of its code). -/
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

/-- The low operand of a canonical concatenation — by the compiler's own
recognizer (`canonicalConcat?`), the one `fallbackKind` dispatches on. -/
def concatLo? (e : Lean.Expr) : Option Lean.Expr := (canonicalConcat? e).map (·.2.2.2)

/-- `n` links from `w`, following the expression `e`: while `e` is a canonical
concatenation, `w` is driven by a concat statement whose low operand wire has
the links of `e`'s low operand. -/
def SpineQ (body : List Stmt) : Nat → Lean.Expr → String → Prop
  | 0, _, _ => True
  | n + 1, e, w => ∀ b, concatLo? e = some b → ∃ x y, link w x y ∈ body ∧ SpineQ body n b y

theorem SpineQ.mono {body body' : List Stmt} (h : ∀ st ∈ body, st ∈ body') :
    ∀ {n : Nat} {e : Lean.Expr} {w : String}, SpineQ body n e w → SpineQ body' n e w
  | 0, _, _, _ => trivial
  | _ + 1, _, _, hs => fun b hb =>
    let ⟨x, y, hm, hr⟩ := hs b hb
    ⟨x, y, h _ hm, SpineQ.mono h hr⟩

theorem SpineQ.of_none {body : List Stmt} {e : Lean.Expr} {w : String} (h : concatLo? e = none) :
    ∀ n, SpineQ body n e w
  | 0 => trivial
  | _ + 1 => fun b hb => by rw [h] at hb; cases hb

/-- Statements are kept. -/
def Kept (s t : CircuitState) : Prop := ∀ st ∈ s.module.body, st ∈ t.module.body

theorem Kept.refl (s : CircuitState) : Kept s s := fun _ h => h
theorem Kept.trans {s t u : CircuitState} (h : Kept s t) (k : Kept t u) : Kept s u :=
  fun st hs => k st (h st hs)

/-- **The record invariant**: every recorded wire has the links of the
expression it is recorded for. -/
def RecQ (s : CircuitState) : Prop :=
  ∀ w e, s.translateRecord.get? w = some e → ∀ n, SpineQ s.module.body n e w

theorem RecQ.empty {s : CircuitState} (h : s.translateRecord = {}) : RecQ s := by
  intro w e he; simp [h] at he

/-- The state invariant: the record invariant, and the variables `B` are bound
(so translating one of them returns its wire and changes nothing). -/
def St (ctx : CompilerState) (B : FVarId → Prop) (s : CircuitState) : Prop :=
  RecQ s ∧ ∀ id, B id → ∃ v, visible ctx s.sourceBindings id = some v

/-- What every action does to the state: statements kept, bindings unchanged. -/
def Ext (s t : CircuitState) : Prop :=
  Kept s t ∧ t.sourceBindings = s.sourceBindings

theorem Ext.refl (s : CircuitState) : Ext s s := ⟨Kept.refl s, rfl⟩
theorem Ext.trans {s t u : CircuitState} (h : Ext s t) (k : Ext t u) : Ext s u :=
  ⟨h.1.trans k.1, k.2.trans h.2⟩

theorem St.transfer {ctx B} {s t : CircuitState} (h : St ctx B s)
    (hr : t.translateRecord = s.translateRecord) (hx : Ext s t) : St ctx B t :=
  ⟨fun w e he n => (h.1 w e (hr ▸ he) n).mono hx.1, fun id hid => by rw [hx.2]; exact h.2 id hid⟩

/-- An action keeps the state invariant, the statements and the bindings. -/
def Good (ctx : CompilerState) (B : FVarId → Prop) {α : Type} (a : CompilerM α) : Prop :=
  ∀ s t r, Returns a ctx s r t → St ctx B s → St ctx B t ∧ Ext s t

/-- An action that writes no record, keeps the statements and the bindings. -/
def Quiet (ctx : CompilerState) {α : Type} (a : CompilerM α) : Prop :=
  ∀ s t r, Returns a ctx s r t → t.translateRecord = s.translateRecord ∧ Ext s t

variable {ctx : CompilerState} {B : FVarId → Prop}

theorem Quiet.good {α : Type} {a : CompilerM α} (h : Quiet ctx a) : Good ctx B a :=
  fun s t r hr hq => ⟨hq.transfer (h s t r hr).1 (h s t r hr).2, (h s t r hr).2⟩

theorem Good.pure {α : Type} (a : α) : Good ctx B (Pure.pure a : CompilerM α) := by
  intro s t r hr hq
  obtain ⟨-, rfl⟩ := Returns.pure hr
  exact ⟨hq, Ext.refl _⟩

theorem Good.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    (hm : Good ctx B m) (hf : ∀ a, Good ctx B (f a)) : Good ctx B (m >>= f) := by
  intro s t r hr hq
  obtain ⟨a, sm, h1, h2⟩ := Returns.bind hr
  obtain ⟨q1, k1⟩ := hm s sm a h1 hq
  obtain ⟨q2, k2⟩ := hf a sm t r h2 q1
  exact ⟨q2, k1.trans k2⟩

theorem Good.throw {α : Type} (e : Exception) : Good ctx B (throw e : CompilerM α) :=
  fun _ _ _ hr _ => (Returns.throw hr).elim

theorem Good.liftMetaM {α : Type} (x : MetaM α) : Good ctx B (CompilerM.liftMetaM x) := by
  intro s t r hr hq
  obtain rfl := Returns.liftMetaM hr
  exact ⟨hq, Ext.refl _⟩

theorem Good.makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    Good ctx B (CompilerM.makeWire hint ty named) := by
  apply Quiet.good
  intro s t r hr
  obtain ⟨-, ht⟩ := makeWire_returns hr
  obtain ⟨-, -, hb, -⟩ := CircuitM.makeWire_spec hint ty named s
  subst ht
  exact ⟨CircuitM.makeWire_translateRecord _ _ _ _, fun st hs => by rw [hb]; exact hs,
    CircuitM.makeWire_sourceBindings _ _ _ _⟩

theorem Good.emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    Good ctx B (CompilerM.emitAssign lhs rhs) := by
  apply Quiet.good
  intro s t r hr
  have ht := emitAssign_returns hr
  subst ht
  exact ⟨emitAssign_translateRecord _ _ _, fun st hs => by
    rw [emitAssign_body_cons]; exact List.mem_cons_of_mem _ hs, rfl⟩

theorem Good.lookupVar (id : FVarId) : Good ctx B (CompilerM.lookupVar id) := by
  intro s t r hr hq
  obtain ⟨-, rfl⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns hr
  exact ⟨hq, Ext.refl _⟩

/-- The walk: binds, `pure`, the builder's operations, branches, and the
hypotheses in scope. -/
macro "good" : tactic => `(tactic| repeat (first
  | assumption
  | exact Good.pure _
  | exact Good.makeWire _ _ _
  | exact Good.emitAssign _ _
  | exact Good.liftMetaM _
  | exact Good.lookupVar _
  | exact Good.throw _
  | refine Good.bind ?_ (fun _ => ?_)
  | split
  | intro _))

/-! ## The arms that are not a concatenation -/

section Arms
variable {rec : TranslateFn} {ae be ce : Lean.Expr} {hint : String} {named : Bool}

theorem compare_good {le : SignalCompareKind}
    (oa : Good ctx B (rec ae "a" false false)) (ob : Good ctx B (rec be "b" false false)) :
    Good ctx B (translateSignalCompare rec le ae be hint named) := by
  unfold translateSignalCompare emitCompareResult emitBoolResult; good

theorem appCompare_good {le : SignalCompareKind}
    (oa : Good ctx B (rec ae "app_arg" false false)) (ob : Good ctx B (rec be "app_arg" false false)) :
    Good ctx B (translateAppCompare rec le ae be hint named) := by
  unfold translateAppCompare emitCompareResult emitBoolResult; good

theorem boolBin_good {kind : SignalBoolBinKind}
    (oa : Good ctx B (rec ae "a" false false)) (ob : Good ctx B (rec be "b" false false)) :
    Good ctx B (translateBoolBinary rec kind ae be hint named) := by
  unfold translateBoolBinary emitBoolResult; good

theorem appBool_good {kind : SignalBoolBinKind}
    (oa : Good ctx B (rec ae "app_arg" false false)) (ob : Good ctx B (rec be "app_arg" false false)) :
    Good ctx B (translateAppBoolBinary rec kind ae be hint named) := by
  unfold translateAppBoolBinary emitBoolResult; good

theorem appBool2_good {f : AppBool2}
    (oa : Good ctx B (rec ae "app_arg" false false)) (ob : Good ctx B (rec be "app_arg" false false)) :
    Good ctx B (translateAppBool2 rec f ae be hint named) := by
  unfold translateAppBool2 emitBoolResult; good

theorem mux_good {ty : Sparkle.IR.Type.HWType}
    (oc : Good ctx B (rec ce "mux_cond" false false))
    (oa : Good ctx B (rec ae "mux_then" false false))
    (ob : Good ctx B (rec be "mux_else" false false)) :
    Good ctx B (translateMuxWith rec (pure ty) ce ae be hint named) := by
  unfold translateMuxWith emitMuxResult; good

theorem setw_good {ws wt : Nat} (oa : Good ctx B (rec ae "s" false false)) :
    Good ctx B (do
      let sw ← rec ae "s" false false
      emitCastResult (setwRhs ws wt sw) wt hint named) := by
  unfold emitCastResult; good

theorem slice_good {hd : String} {start len : Nat} (oa : Good ctx B (rec ae hd false false)) :
    Good ctx B (do
      let sw ← rec ae hd false false
      emitSliceResult (sliceRhs start len sw) len hint named) := by
  unfold emitSliceResult; good

theorem concatConst_good {k v : Nat} : Good ctx B (emitConcatConst k v) := by
  unfold emitConcatConst emitCastResult; good

theorem concatActs_good {wd : Nat} {hiAct loAct : CompilerM String}
    (oa : Good ctx B hiAct) (ob : Good ctx B loAct) :
    Good ctx B (translateConcatActs wd hiAct loAct hint named) := by
  unfold translateConcatActs; good

end Arms

/-! ## The result's links -/

/-- An action for the expression `e`: it keeps the invariant, the statements
and the bindings, and the wire it returns has the links of `e`. -/
def Spec (ctx : CompilerState) (B : FVarId → Prop) (e : Lean.Expr) (a : CompilerM String) : Prop :=
  ∀ s t w, Returns a ctx s w t → St ctx B s →
    St ctx B t ∧ Ext s t ∧ ∀ n, SpineQ t.module.body n e w

theorem Spec.good {e : Lean.Expr} {a : CompilerM String} (h : Spec ctx B e a) : Good ctx B a :=
  fun s t r hr hq => ⟨(h s t r hr hq).1, (h s t r hr hq).2.1⟩

/-- For an expression that is not a canonical concatenation there is nothing
to say about the result. -/
theorem Spec.of_good {e : Lean.Expr} {a : CompilerM String} (hg : Good ctx B a)
    (hn : concatLo? e = none) : Spec ctx B e a :=
  fun s t r hr hq => ⟨(hg s t r hr hq).1, (hg s t r hr hq).2, SpineQ.of_none hn⟩

/-- A record of the result keeps the record invariant: the result has its links. -/
theorem St.record {s : CircuitState} {e : Lean.Expr} {w : String} (h : St ctx B s)
    (hw : ∀ n, SpineQ s.module.body n e w) :
    St ctx B { s with translateRecord := s.translateRecord.insert w e } := by
  refine ⟨fun w' e' he' n => ?_, h.2⟩
  rw [Std.HashMap.get?_insert] at he'
  split at he'
  · rename_i hww
    cases he'
    rw [← (beq_iff_eq.mp hww)]
    exact hw n
  · exact h.1 w' e' he' n

/-- **The validated cache wrapper**: a hit returns a recorded wire — it has
its links by the record invariant; a miss lowers and records the result. -/
theorem Spec.cached {lower : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (h : Spec ctx B e (lower e hint top named)) :
    Spec ctx B e (translateControlCachedWith lower e hint top named) := by
  intro s t w hr hq
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hrec⟩ := cacheLookupValidated_returns hit
    subst hs
    exact ⟨hq, Ext.refl _, hq.1 w e (hrec w rfl)⟩
  · obtain ⟨q, k, sp⟩ := h s sm w miss hq
    have ht := recordTranslation_returns record
    subst ht
    exact ⟨q.record sp, k, sp⟩

/-- **The concat arm**: the result wire is driven by `{hi, lo}`, and `lo` has
the links of the low operand. -/
theorem concat_spec {e b : Lean.Expr} {wd : Nat} {hint : String} {named : Bool}
    {hiAct loAct : CompilerM String} (he : concatLo? e = some b)
    (oa : Good ctx B hiAct) (ob : Spec ctx B b loAct) :
    Spec ctx B e (translateConcatActs wd hiAct loAct hint named) := by
  intro s t w hr hq
  have hg := concatActs_good (hint := hint) (named := named) (wd := wd) oa ob.good s t w hr hq
  refine ⟨hg.1, hg.2, ?_⟩
  unfold translateConcatActs at hr
  obtain ⟨res, sA, hmk, rest⟩ := Returns.bind hr
  obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
  obtain ⟨wb, sC, hb', rest⟩ := Returns.bind rest
  obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
  obtain ⟨hwv, ht⟩ := Returns.pure ret
  subst ht
  subst hwv
  obtain ⟨qA, -⟩ := Good.makeWire (ctx := ctx) (B := B) _ _ _ s sA w hmk hq
  obtain ⟨qB, -⟩ := oa sA sB wa ha qA
  obtain ⟨-, -, spb⟩ := ob sB sC wb hb' qB
  have hD := emitAssign_returns hem
  have hbody : t.module.body = .assign w (.concat [.ref wa, .ref wb]) :: sC.module.body := by
    rw [hD, emitAssign_body_cons]
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    intro b' hb2
    rw [he] at hb2
    cases hb2
    refine ⟨wa, wb, by rw [hbody]; exact List.mem_cons_self .., ?_⟩
    exact (spb n).mono (fun st hs => by rw [hbody]; exact List.mem_cons_of_mem _ hs)

/-! ## One step of the knot, for an expression that is not a concatenation -/

/-- Recording a result for an expression that is not a canonical
concatenation: nothing to check (also when it overwrites a record). -/
theorem Good.record {e : Lean.Expr} (hn : concatLo? e = none) (w : String) (c : Bool) :
    Good ctx B (recordTranslation e w c) := by
  intro s t r hr hq
  have ht := recordTranslation_returns hr
  subst ht
  exact ⟨hq.record (SpineQ.of_none hn), fun _ h => h, rfl⟩

theorem Good.apply {α : Type} {a : CompilerM α} (h : Good ctx B a) {s t : CircuitState} {r : α}
    (hr : Returns a ctx s r t) (hq : St ctx B s) : St ctx B t ∧ Ext s t := h s t r hr hq

/-- **The step**, for `e` not a canonical concatenation: the validated lookup
(a hit changes nothing), the core, the record of its result, or the fallback
when the core declines. -/
theorem step_spec {rec : TranslateFn} {e : Lean.Expr} {hint : String} {top named : Bool}
    (hn : concatLo? e = none)
    (hcore : Good ctx B (translateCore rec e hint top named))
    (hfb : ∀ s t, St ctx B s → Returns (translateCore rec e hint top named) ctx s none t →
      Good ctx B (translateFallback rec e hint top named)) :
    Spec ctx B e (translateStepWith translateFallback rec e hint top named) := by
  apply Spec.of_good _ hn
  have cont : ∀ {s t w} {K : Option String → CompilerM String},
      (∀ z, Good ctx B (K (some z))) → K none = translateFallback rec e hint top named →
      Returns (translateCore rec e hint top named >>= K) ctx s w t → St ctx B s →
      St ctx B t ∧ Ext s t := by
    intro s t w K hsome hnone hr hq
    obtain ⟨r, sc, hc, rest⟩ := Returns.bind hr
    obtain ⟨qc, kc⟩ := hcore s sc r hc hq
    cases r with
    | some z =>
      obtain ⟨q, k⟩ := hsome z sc t w rest qc
      exact ⟨q, kc.trans k⟩
    | none =>
      rw [hnone] at rest
      obtain ⟨q, k⟩ := hfb s sc hq hc sc t w rest qc
      exact ⟨q, kc.trans k⟩
  have hrec := fun (z : String) (c : Bool) => Good.record (ctx := ctx) (B := B) hn z c
  have ksome : ∀ (c : Bool) (z : String), Good ctx B (do
      unless e.isFVar do recordTranslation e z c
      pure z : CompilerM String) := by
    intro c z
    show Good ctx B (if e.isFVar = true then pure z else recordTranslation e z c >>= fun _ => pure z)
    split
    · exact Good.pure _
    · exact Good.bind (hrec z c) (fun _ => Good.pure _)
  intro s t w hr hq
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst ht
      exact ⟨hq, Ext.refl _⟩
    · exact cont (fun z => ksome _ z) rfl hr hq
  · exact cont (fun z => ksome _ z) rfl hr hq

/-! ## The step's own cases: a bound variable, a literal, a library operator -/

theorem pureLiteral_good (args : Array Lean.Expr) (hint : String) (named : Bool) :
    Good ctx B (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?; good

/-- A bound variable: its wire, nothing changes. -/
theorem input_spec {rec : TranslateFn} {id : FVarId} {hint : String} {named : Bool} (hB : B id) :
    Spec ctx B (.fvar id) (translateStepWith translateFallback rec (.fvar id) hint false named) := by
  refine step_spec rfl (Good.lookupVar id) ?_
  intro s t hq hr
  obtain ⟨hv, -⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns (id := id) hr
  obtain ⟨v, hbound⟩ := hq.2 id hB
  rw [hbound] at hv
  cases hv

/-- A `Signal.pure` literal the core lowers. -/
theorem literal_step_spec {rec : TranslateFn} {e c : Lean.Expr} {us : List Level} {n v : Nat}
    {hint : String} {named : Bool}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (back : e.getAppArgs.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (hn : concatLo? e = none) :
    Spec ctx B e (translateStepWith translateFallback rec e hint false named) := by
  have hcore : translateCore rec e hint false named =
      translateSignalPureLiteral? e.getAppArgs hint named := by
    unfold translateCore
    split
    · simp [Lean.Expr.getAppFn] at fn
    · rw [fn]; simp only [beq_self_eq_true, if_true]
  refine step_spec hn (by rw [hcore]; exact pureLiteral_good _ _ _) ?_
  intro s t hq hr
  rw [hcore] at hr
  obtain ⟨w', hw'⟩ := literal_payload_some back lit hr
  cases hw'

/-- The Bool literal: the core declines, the fallback emits it under the
validated cache. -/
theorem bool_literal_spec {rec : TranslateFn} {dom : Lean.Expr} {hint : String} {named : Bool}
    (b : Bool) (hn : concatLo? (literalE dom b) = none) :
    Spec ctx B (literalE dom b)
      (translateStepWith translateFallback rec (literalE dom b) hint false named) := by
  refine step_spec hn (by rw [literal_core]; exact Good.pure _) ?_
  intro s t hq hr
  rw [translateFallback_bool rec _ hint false named (by cases b <;> rfl)]
  refine (Spec.cached (Spec.of_good ?_ hn)).good
  show Good ctx B (translateBoolUncachedWith rec _ _ hint false named)
  rw [literal_uncached]
  unfold emitBoolLiteral emitBoolResult; good

/-- A canonical library operator: the result wire, the two operands, the assign. -/
theorem binary_step_spec {rec : TranslateFn} {e : Lean.Expr} {m : Name} {us : List Level}
    {hint : String} {named : Bool} {n : Nat} (op : Binary)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (hn : concatLo? e = none)
    (oa : Good ctx B (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false))
    (ob : Good ctx B (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false)) :
    Spec ctx B e (translateStepWith translateFallback rec e hint false named) := by
  have hbin : Good ctx B
      (translateCanonicalSignalBinary rec e op.operator e.getAppArgs true true hint named) := by
    unfold translateCanonicalSignalBinary
    simp only [width, if_true]
    good
  refine step_spec hn ?_ ?_
  · intro s t r hr hq
    obtain ⟨w, -, lower⟩ := core_binary_returns fn hop kinds width hr
    exact hbin s t w lower hq
  · intro s t hq hr
    obtain ⟨w, hw, -⟩ := core_binary_returns fn hop kinds width hr
    cases hw

/-! ## The fuel induction -/

/-- The low operand of a quoted concatenation, by the compiler's recognizer. -/
theorem concatLo?_concatE (dom a b : Lean.Expr) {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    concatLo? (concatE dom m n a b) = some b := by
  unfold concatLo?
  rw [canonicalConcat?_concatE dom a b hm hn]
  rfl

section Fuel
variable {dom : Lean.Expr} {bi vi : Nat → FVarId}

local notation "Q(" e ")" =>
  quote dom (fun j => Lean.Expr.fvar (bi j)) (fun j => Lean.Expr.fvar (vi j)) e

set_option maxHeartbeats 1000000 in
/-- **The translator leaves the spine**, at every fuel, for every quoted
well-formed term: it keeps the record invariant, the statements and the
bindings, and the wire it returns has the links of the term's expression. -/
theorem fuel_spine (fuel : Nat) {kb kv : Nat} {vw : Nat → Nat}
    (hb : ∀ j, j < kb → B (bi j)) (hv : ∀ j, j < kv → B (vi j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → ∀ hint named,
      Spec ctx B Q(e) (translateFuelFix translateStep fuel Q(e) hint false named) := by
  induction fuel with
  | zero =>
    intro s e he hint named s' t w hr hq
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hint named
    change Spec ctx B _ (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named)
    cases e with
    | boolInput j => exact input_spec (hb j he)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact input_spec (hv j hj)
    | boolLit b => exact bool_literal_spec b (by cases b <;> rfl)
    | bitsLit w v =>
      exact literal_step_spec (us := [.zero]) rfl
        (show (quoteF dom w (fun j => Lean.Expr.fvar (vi j)) (.lit v)).getAppArgs.back? =
          some (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) from rfl)
        (litValue_natE w v he.1) rfl
    | bitsNum w v =>
      exact literal_step_spec (us := [.zero]) rfl
        (show (numSigE dom w v).getAppArgs.back? = some (numLitE w v) from rfl)
        (litValue_numLitE w v he.1) rfl
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom Q(a) Q(b) w
      refine binary_step_spec op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 (by cases op <;> rfl) ?_ ?_
      · show Good ctx B (translateFuelFix translateStep fuel
          (binE dom w op Q(a) Q(b)).getAppArgs[(binE dom w op Q(a) Q(b)).getAppArgs.size - 2]!
          "op_a" false false)
        rw [ck.2.2.2.2.1]; exact (ih a ha "op_a" false).good
      · show Good ctx B (translateFuelFix translateStep fuel
          (binE dom w op Q(a) Q(b)).getAppArgs[(binE dom w op Q(a) Q(b)).getAppArgs.size - 1]!
          "op_b" false false)
        rw [ck.2.2.2.2.2.1]; exact (ih b hb' "op_b" false).good
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (compareE le dom w Q(a) Q(b)) hint false named)
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      apply Spec.cached
      refine Spec.of_good ?_ (by cases le <;> rfl)
      show Good ctx B (translateBoolUncachedWith _ _ (compareE le dom w Q(a) Q(b)) hint false named)
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_good (ih a ha "a" false).good (ih b hb' "b" false).good
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolBinE kind dom Q(a) Q(b)) hint false named)
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      apply Spec.cached
      refine Spec.of_good ?_ (by cases kind <;> rfl)
      show Good ctx B (translateBoolUncachedWith _ _ (boolBinE kind dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_good (ih a ha "a" false).good (ih b hb' "b" false).good
    | appCompare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appCompareE le dom w Q(a) Q(b)) hint false named)
      rw [appCompare_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appCompareE _ _ _ _ _)]
      apply Spec.cached
      refine Spec.of_good ?_ (by cases le <;> rfl)
      show Good ctx B (translateBoolUncachedWith _ _ (appCompareE le dom w Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appCompare]
      exact appCompare_good (ih a ha "app_arg" false).good (ih b hb' "app_arg" false).good
    | appBool kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appBoolE kind dom Q(a) Q(b)) hint false named)
      rw [appBool_step, translateFallback_bool _ _ hint false named (isBoolControl_appBoolE _ _ _ _)]
      apply Spec.cached
      refine Spec.of_good ?_ (by cases kind <;> rfl)
      show Good ctx B (translateBoolUncachedWith _ _ (appBoolE kind dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appBool]
      exact appBool_good (ih a ha "app_arg" false).good (ih b hb' "app_arg" false).good
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (appBool2E f dom Q(a) Q(b)) hint false named)
      rw [appBool2_step, translateFallback_bool _ _ hint false named (isBoolControl_appBool2E _ _ _ _)]
      apply Spec.cached
      refine Spec.of_good ?_ (by cases f <;> rfl)
      show Good ctx B (translateBoolUncachedWith _ _ (appBool2E f dom Q(a) Q(b)) hint false named)
      rw [translateBoolUncachedWith_appBool2]
      exact appBool2_good (ih a ha "app_arg" false).good (ih b hb' "app_arg" false).good
    | boolNot a =>
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolNotE dom Q(a)) hint false named)
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateSignalCompare (translateFuelFix translateStep fuel) .eq Q(a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named)
      exact compare_good (ih a he "a" false).good (ih (.boolLit false) trivial "b" false).good
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolEqE dom Q(a) Q(b)) hint false named)
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateSignalCompare (translateFuelFix translateStep fuel) .eq Q(a) Q(b)
        hint named)
      exact compare_good (ih a ha "a" false).good (ih b hb' "b" false).good
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
          (boolMuxE dom Q(c) Q(a) Q(b)) hint false named)
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply Spec.cached
        refine Spec.of_good ?_ rfl
        show Good ctx B (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named)
        exact mux_good (ih c hc "mux_cond" false).good (ih a ha "mux_then" false).good
          (ih b hb' "mux_else" false).good
      | bits w =>
        show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) Q(c) Q(a) Q(b)) hint false named)
        rw [vector_step]
        apply Spec.cached
        refine Spec.of_good ?_ rfl
        show Good ctx B (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) Q(c) Q(a) Q(b)) hint false named)
        rw [vectorMuxUncached_muxE]
        exact mux_good (ih c hc "mux_cond" false).good (ih a ha "mux_then" false).good
          (ih b hb' "mux_else" false).good
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (setwE dom w w' Q(a)) hint false named)
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' Q(a)) hint false named)
      rw [setwUncached_setwE]
      exact setw_good (ih a ha "s" false).good
    | slice nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (sliceE dom nm w start len Q(a)) hint false named)
      rw [slice_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateSliceUncachedWith (translateFuelFix translateStep fuel) start len
        (sliceE dom nm w start len Q(a)) hint false named)
      rw [sliceUncached_sliceE]
      exact slice_good (ih a ha "s" false).good
    | concat a b =>
      rename_i m n
      obtain ⟨ha, hb'⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatE dom m n Q(a) Q(b)) hint false named)
      rw [concat_step _ _ _ _ _ _ _ _ _ (a.wf_pos ha) (b.wf_pos hb')]
      apply Spec.cached
      show Spec ctx B _ (translateConcatUncachedWith (translateFuelFix translateStep fuel) m n
        (concatE dom m n Q(a) Q(b)) hint false named)
      rw [concatUncached_concatE]
      exact concat_spec (concatLo?_concatE dom _ _ (a.wf_pos ha) (b.wf_pos hb'))
        (ih a ha "concat_hi" false).good (ih b hb' "concat_lo" false)
    | concatLitHi k v b =>
      rename_i n
      obtain ⟨hb', hk, hlt⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatLitHiE dom k v n Q(b)) hint false named)
      rw [concatLitHi_step _ _ _ _ _ _ _ _ _ hk hlt (b.wf_pos hb')]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        true k v n (concatLitHiE dom k v n Q(b)) hint false named)
      rw [concatLitUncached_hiE]
      exact concatActs_good concatConst_good (ih b hb' "concat_lo" false).good
    | concatLitLo a k v =>
      rename_i m
      obtain ⟨ha, hk, hlt⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (concatLitLoE dom m k v Q(a)) hint false named)
      rw [concatLitLo_step _ _ _ _ _ _ _ _ _ hk hlt (a.wf_pos ha)]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        false k v m (concatLitLoE dom m k v Q(a)) hint false named)
      rw [concatLitUncached_loE]
      exact concatActs_good (ih a ha "concat_hi" false).good concatConst_good
    | zextMap nm k a =>
      rename_i n
      obtain ⟨ha, hk⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (zextMapE dom nm k n Q(a)) hint false named)
      rw [zextMap_step _ _ _ _ _ _ _ _ _ hk (a.wf_pos ha)]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) n
        (k + n) (zextMapE dom nm k n Q(a)) hint false named)
      rw [setwUncached_zextMapE]
      exact setw_good (ih a ha "s" false).good
    | sliceF nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show Spec ctx B _ (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (sliceFE dom nm w start len Q(a)) hint false named)
      rw [sliceF_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply Spec.cached
      refine Spec.of_good ?_ rfl
      show Good ctx B (translateSliceFUncachedWith (translateFuelFix translateStep fuel)
        start len (sliceFE dom nm w start len Q(a)) hint false named)
      rw [sliceFUncached_sliceFE]
      exact slice_good (ih a ha "a" false).good

/-- The real translator leaves the spine. -/
theorem translateExprToWire_spine {kb kv : Nat} {vw : Nat → Nat}
    (hb : ∀ j, j < kb → B (bi j)) (hv : ∀ j, j < kv → B (vi j))
    {s : SType} (e : Term s) (he : e.WF kb kv vw) (hint : String) (named : Bool) :
    Spec ctx B Q(e) (translateExprToWire Q(e) hint false named) :=
  fuel_spine translateFuelLimit hb hv e he hint named

end Fuel

end Tools.ShippingUnifiedSpine
