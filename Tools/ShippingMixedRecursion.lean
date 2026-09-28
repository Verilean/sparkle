import Tools.ShippingMixedBinarySoundness

/-! Structural and semantic contracts for closing the actual shipping fuel
recursion. The final synthesis-entry and source-to-RTL connection is separate. -/
namespace Tools.ShippingMixedRecursion
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedLiteralSoundness Tools.ShippingMixedBinarySoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingBoolLiteralSoundness Tools.ShippingBoolMuxSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingPostSoundness Sparkle.IR.OptCheck
open Tools.ShippingTypedExprSoundness Tools.ShippingScalarSoundness
open Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness

/-- Unlike a child contract, this covers every top/named flag and hint. -/
structure Contract (rec : TranslateFn) (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (we : WEnv) (mems : MEnv) (initial : Env) (e : Lean.Expr) (width value : Nat) : Prop where
  frame : ∀ hint top named s t w, Lookup ctx ρ β s →
    Returns (rec e hint top named) ctx s w t → Frame s t
  sem : ∀ hint top named s t w prior, MixedInv ctx ρ β we mems initial s prior →
    ScalarWidthsAgree we t → Returns (rec e hint top named) ctx s w t →
    Outcome ctx ρ β we mems initial prior s t w width value

theorem Contract.child {rec ctx ρ β we mems initial e n v}
    (h : Contract rec ctx ρ β we mems initial e n v) (hint : String) :
    Child rec ctx ρ β we mems initial e hint n v :=
  ⟨h.frame hint false false, h.sem hint false false⟩

theorem bits_input_contract {rec ctx ρ β we mems initial id n} {x : BitVec n}
    (hi : β id = some ⟨n, x⟩) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial (.fvar id) n x.toNat := by
  constructor
  · intro hint top named s t w lookup hr
    obtain ⟨v, bound, _⟩ := lookup.bits id n x hi
    obtain ⟨_, ht⟩ := translateStep_fvar_returns bound hr
    subst t; exact Frame.refl s
  · intro hint top named s t w prior h widths hr
    exact translateStep_bits_input_mixed h hi hr

theorem bool_input_contract {rec ctx ρ β we mems initial id b}
    (hi : ρ id = some b) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial (.fvar id) 1 (encodeBool b) := by
  constructor
  · intro hint top named s t w lookup hr
    obtain ⟨v, bound, _⟩ := lookup.bool id b hi
    obtain ⟨_, ht⟩ := translateStep_fvar_returns bound hr
    subst t; exact Frame.refl s
  · intro hint top named s t w prior h widths hr
    exact translateStep_bool_input_mixed h hi hr

/-- The old literal structural lemma already preserves existing Bool wires;
only its semantic conclusion used the old BitVec-only invariant. -/
theorem bits_core_frame {rec ctx β s t e us hint top named r n} {x : BitVec n}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (hr : Returns (translateCore rec e hint top named) ctx s r t) :
    ∃ w, r = some w ∧ Frame s t ∧ s.usedNames.contains w = false := by
  unfold translateCore at hr
  split at hr
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at hr
    simp only [beq_self_eq_true, if_true] at hr
    obtain ⟨w, he, ⟨growth, bindings, records, fresh, emits⟩, _⟩ := translateSignalPureLiteral_branch
      (we := fun _ => 0) (mems := fun _ _ => 0) (initial := fun _ => 0) fn hd hr
    refine ⟨w, he, ⟨growth.2.1, growth.1, bindings,
      fun _ _ hr => Or.inl (by rw [records] at hr; exact hr), growth.2.2.1, fun hs p hp => by
        rcases growth.2.2.2.2.wireTypes p hp with old | new
        · exact hs p old
        · exact Or.inr new, emits.1, emits.2.1, ?_, growth.2.2.2.2.parameters, growth.2.2.2.2.primitive, growth.2.2.2.2.wireNames⟩, fresh⟩
    intro hs stmt hmem
    obtain ⟨pre, eq, simple⟩ := emits.2.2
    rw [eq] at hmem
    rcases List.mem_append.mp hmem with hp | hp
    · obtain ⟨l, rhs, eq, shape, _⟩ := simple stmt hp
      exact ⟨l, rhs, eq, shape.simple⟩
    · exact hs stmt hp

theorem bits_recorded_frame {rec ctx β s t e us hint top named w n cacheable}
    {x : BitVec n} {K : Option String → CompilerM String}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (hk : ∀ v, K (some v) = (recordTranslation e v cacheable >>= fun _ => pure v))
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) : Frame s t := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  obtain ⟨v, he, growth, fresh⟩ := bits_core_frame fn hd core
  rw [he, hk] at rest
  obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
  obtain ⟨hw, ht⟩ := Returns.pure rest
  subst w t
  exact growth.record_new fresh record

theorem bits_literal_contract {rec ctx ρ β we mems initial e us n} {x : BitVec n}
    (hn : 0 < n) (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (hd : Denotes β e n x) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial e n x.toNat := by
  constructor
  · intro hint top named s t w lookup hr
    have nf := isFVar_false_of_const fn
    unfold translateStepWith at hr
    dsimp only at hr
    split at hr
    · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
      have hs := (cacheLookupValidated_returns rh).1
      subst sh
      split at hr
      · obtain ⟨hw, ht⟩ := Returns.pure hr
        subst w t; exact Frame.refl s
      · apply bits_recorded_frame (cacheable := !named && !e.isFVar && !top) fn hd ?_ hr
        intro v; simp only [nf, Bool.false_eq_true, if_false]
    · apply bits_recorded_frame (cacheable := !named && !e.isFVar && !top) fn hd ?_ hr
      intro v; simp only [nf, Bool.false_eq_true, if_false]
  · intro hint top named s t w prior h widths hr
    exact (Tools.ShippingMixedLiteralSoundness.translateStep_literal_mixed h hn fn hd widths hr).2

/-- BitVec recursive translation is now closed in arbitrary mixed states.
There is no operand-correctness or legacy-handler premise. -/
theorem bits_fuel_contract (fuel : Nat) {ctx ρ β we mems initial e n} {x : BitVec n}
    (hn : 0 < n) (hd : Denotes β e n x) :
    Contract (translateFuelFix translateStep fuel) ctx ρ β we mems initial e n x.toNat := by
  induction fuel generalizing e n with
  | zero =>
    constructor
    · intro hint top named s t w lookup hr; exact (Returns.throw hr).elim
    · intro hint top named s t w prior h widths hr; exact (Returns.throw hr).elim
  | succ fuel ih =>
    change Contract (translateStepWith translateFallback (translateFuelFix translateStep fuel)) _ _ _ _ _ _ _ _ _
    cases hd with
    | fvar hi => exact bits_input_contract hi
    | pureLit fn back lit => exact bits_literal_contract hn fn (.pureLit fn back lit)
    | @binary e m us op n x y fn hop kinds width da db =>
      have ca := (ih hn da).child "op_a"
      have cb := (ih hn db).child "op_b"
      constructor
      · intro hint top named s t w lookup hr
        exact translateStep_binary_frame op lookup fn hop kinds width ca cb hr
      · intro hint top named s t w prior h widths hr
        exact (translateStep_binary_mixed op x y hn h fn hop kinds width da db ca cb widths hr).2

structure ActionSpec (action : CompilerM String) (ctx : CompilerState)
    (ρ : BoolValuation) (β : Valuation) (we : WEnv) (mems : MEnv) (initial : Env)
    (width value : Nat) : Prop where
  frame : ∀ s t w, Lookup ctx ρ β s → Returns action ctx s w t → Frame s t
  sem : ∀ s t w prior, MixedInv ctx ρ β we mems initial s prior → ScalarWidthsAgree we t →
    Returns action ctx s w t → Outcome ctx ρ β we mems initial prior s t w width value

structure FreshAction (action : CompilerM String) (ctx : CompilerState)
    (ρ : BoolValuation) (β : Valuation) (we : WEnv) (mems : MEnv) (initial : Env)
    (width value : Nat) : Prop extends ActionSpec action ctx ρ β we mems initial width value where
  fresh : ∀ s t w, Lookup ctx ρ β s → Returns action ctx s w t → s.usedNames.contains w = false

theorem emit_bool_frame {ctx s t w rhs hint named}
    (shape : simpleRhs rhs = true)
    (hr : Returns (emitBoolResult rhs hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨hw, ht⟩ := emitBoolResult_returns hr
  have hm := CircuitM.makeWire_spec hint .bit named s
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp; rw [ht, emitAssign_wires, hm.2.2.2]; exact List.mem_cons_of_mem _ hp
  · intro z hz; rw [ht, emitAssign_usedNames, hm.2.1]; simp [Std.HashSet.contains_insert, hz]
  · rw [ht, emitAssign_sourceBindings, CircuitM.makeWire_sourceBindings]
  · intro z ex he; left
    rw [ht, emitAssign_translateRecord, CircuitM.makeWire_translateRecord] at he
    exact he
  · intro hok
    apply (WiresOk.fresh hm.1 hm.2.1 hm.2.2.2 hok).congr
    · rw [ht, emitAssign_wires]
    · rw [ht, emitAssign_usedNames]
  · intro hs p hp
    rw [ht, emitAssign_wires, hm.2.2.2] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl rfl
    · exact hs p hp
  · rw [ht, emitAssign_outputs, makeWire_outputs]
  · rw [ht, emitAssign_inputs, makeWire_inputs]
  · intro hs stmt hmem
    rw [ht, emitAssign_body_cons, hm.2.2.1] at hmem
    rcases List.mem_cons.mp hmem with rfl | hp
    · exact ⟨_, _, rfl, shape⟩
    · exact hs stmt hp
  · rw [ht]; change (CircuitM.makeWire hint .bit named s).2.module.parameters = _
    rw [makeWire_module]; rfl
  · rw [ht]; change (CircuitM.makeWire hint .bit named s).2.module.isPrimitive = _
    rw [makeWire_module]; rfl
  · intro p hp
    rw [ht, emitAssign_wires, hm.2.2.2] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr (CircuitM.makeWire_allocated hint .bit named s)
    · exact Or.inl hp
  · rw [hw]; exact hm.1

theorem cached_action {ctx ρ β we mems initial lower e hint top named b}
    (hd : BoolDenotes ρ β e b)
    (node : FreshAction (lower e hint top named) ctx ρ β we mems initial 1 (encodeBool b)) :
    ActionSpec (translateControlCachedWith lower e hint top named) ctx ρ β we mems initial 1 (encodeBool b) := by
  constructor
  · intro s t w lookup hr
    rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
    · have ht := (cacheLookupValidated_returns hit).1
      subst t; exact Frame.refl s
    · exact (node.frame s sm w lookup miss).record_new (node.fresh s sm w lookup miss) record
  · intro s t w prior h widths hr
    exact translateControlCachedWith_mixed h hd widths (fun sm r wm miss => node.sem s sm r prior h wm miss) hr

theorem literal_fresh {ctx ρ β we mems initial hint named} (b : Bool) :
    FreshAction (emitBoolLiteral b hint named) ctx ρ β we mems initial 1 (encodeBool b) := by
  refine ⟨⟨fun _ _ _ _ hr => (emit_bool_frame rfl hr).1, ?_⟩,
    fun _ _ _ _ hr => (emit_bool_frame rfl hr).2⟩
  intro s t w prior h widths hr
  apply emitBoolResult_mixed h (.const _ 1 (by decide)) ?_ widths hr
  have he := evalExpr_const_lt we prior (encodeBool b) 1 (encodeBool_lt b)
  cases b <;> simpa [encodeBool] using he

theorem bool_literal_contract {rec ctx ρ β we mems initial dom} (b : Bool) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (literalE dom b) 1 (encodeBool b) := by
  have fallback : ∀ hint top named, ActionSpec
      (translateFallback rec (literalE dom b) hint top named) ctx ρ β we mems initial 1 (encodeBool b) := by
    intro hint top named
    rw [translateFallback_bool rec _ hint top named (by cases b <;> rfl)]
    apply cached_action (BoolDenotes.quotePure dom b)
    change FreshAction (translateBoolUncachedWith rec _ (literalE dom b) hint top named)
      ctx ρ β we mems initial 1 (encodeBool b)
    rw [literal_uncached]; exact literal_fresh b
  constructor
  · intro hint top named s t w lookup hr
    unfold translateStepWith at hr
    dsimp only at hr
    split at hr
    · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
      have hs := (cacheLookupValidated_returns rh).1
      subst sh
      split at hr
      · obtain ⟨hw, ht⟩ := Returns.pure hr
        subst w t; exact Frame.refl s
      · rw [literal_core] at hr
        obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
        obtain ⟨hv, hs⟩ := Returns.pure rv
        subst v sc
        exact (fallback hint top named).frame s t w lookup hr
    · rw [literal_core] at hr
      obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hv, hs⟩ := Returns.pure rv
      subst v sc
      exact (fallback hint top named).frame s t w lookup hr
  · intro hint top named s t w prior h widths hr
    exact Tools.ShippingMixedInvariant.translateStep_literal_mixed rec b h widths hr

/-- Structural comparison sequence: both children, then fresh Bool allocation. -/
theorem compare_shape {ctx ρ β we mems initial rec ae be le hint named n va vb s t w}
    (ca : Child rec ctx ρ β we mems initial ae "a" n va)
    (cb : Child rec ctx ρ β we mems initial be "b" n vb)
    (lookup : Lookup ctx ρ β s)
    (hr : Returns (translateSignalCompare rec le ae be hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateSignalCompare_returns hr
  have fa := ca.frame s sa a lookup ra
  have fb := cb.frame sa sb b (lookup.transfer fa) rb
  obtain ⟨fe, fresh⟩ := emit_bool_frame (by cases le <;> rfl) re
  refine ⟨(fa.trans fb).trans fe, ?_⟩
  cases hu : s.usedNames.contains w
  · rfl
  · have := fb.used w (fa.used w hu); simp [fresh] at this

theorem compare_fresh {ctx ρ β we mems initial rec ae be le hint named n}
    (x y : BitVec n) (hn : 0 < n)
    (ca : Child rec ctx ρ β we mems initial ae "a" n x.toNat)
    (cb : Child rec ctx ρ β we mems initial be "b" n y.toNat) :
    FreshAction (translateSignalCompare rec le ae be hint named) ctx ρ β we mems initial
      1 (encodeBool (compareValue le x y)) := by
  refine ⟨⟨fun _ _ _ lookup hr => (compare_shape ca cb lookup hr).1, ?_⟩,
    fun _ _ _ lookup hr => (compare_shape ca cb lookup hr).2⟩
  intro s t w prior h widths hr
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateSignalCompare_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases le <;> rfl) re).1
  have aout := ca.sem s sa a prior h ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va, ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb b va ia (fe.decls.widths widths) rb
  obtain ⟨vb, ib, bv, bf⟩ := bout.execution
  have step := emitBoolResult_mixed ib
    (typed_compare_refs le hn aout.width_eq bout.width_eq)
    (compare_rhs_correct le x y we vb a b ((bf a aout.used).trans av) bv aout.width_eq bout.width_eq) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨step.used, step.width_eq, fun z hz => step.grows z (fb.used z (fa.used z hz)),
    result, inv, val, fun z hz => (frame z (fb.used z (fa.used z hz))).trans
      ((bf z (fa.used z hz)).trans (af z hz))⟩

theorem compare_step (rec : TranslateFn) (dom ae be : Lean.Expr) (n : Nat) (le : SignalCompareKind)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (compareE le dom n ae be)
      hint top named = translateFallback rec (compareE le dom n ae be)
      hint top named := by
  have shape : translateCoreShape (compareE le dom n ae be) = false := by cases le <;> rfl
  have core : translateCore rec (compareE le dom n ae be) hint top named = pure none := by cases le <;> rfl
  simp [translateStepWith, shape, core]
  rfl

theorem compare_contract {rec ctx ρ β we mems initial dom ae be n le}
    (x y : BitVec n) (hn : 0 < n) (da : Denotes β ae n x) (db : Denotes β be n y)
    (ca : Child rec ctx ρ β we mems initial ae "a" n x.toNat)
    (cb : Child rec ctx ρ β we mems initial be "b" n y.toNat) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (compareE le dom n ae be) 1 (encodeBool (compareValue le x y)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (compareE le dom n ae be)
        hint top named) ctx ρ β we mems initial 1 (encodeBool (compareValue le x y)) := by
    intro hint top named
    rw [compare_step, translateFallback_bool rec _ hint top named (by cases le <;> rfl)]
    apply cached_action (BoolDenotes.quoteCompare dom ae be le da db)
    rw [translateBoolUncachedWith_compare]
    exact compare_fresh x y hn ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem translateBoolUncachedWith_boolBin (rec legacy : TranslateFn) (kind : SignalBoolBinKind)
    (dom ae be : Lean.Expr) (hint : String) (top named : Bool) :
    translateBoolUncachedWith rec legacy (boolBinE kind dom ae be) hint top named =
      translateBoolBinary rec kind ae be hint named := by cases kind <;> rfl

theorem translateBoolBinary_returns {rec : TranslateFn} {kind : SignalBoolBinKind} {a b : Lean.Expr}
    {hint w : String} {named : Bool} {ctx : CompilerState} {s t : CircuitState}
    (h : Returns (translateBoolBinary rec kind a b hint named) ctx s w t) :
    ∃ aw bw sa sb, Returns (rec a "a" false false) ctx s aw sa ∧
      Returns (rec b "b" false false) ctx sa bw sb ∧
      Returns (emitBoolResult (.op (signalBoolBinOp kind) [.ref aw, .ref bw]) hint named) ctx sb w t := by
  unfold translateBoolBinary at h
  obtain ⟨aw, sa, ha, h⟩ := Returns.bind h
  obtain ⟨bw, sb, hb, he⟩ := Returns.bind h
  exact ⟨aw, bw, sa, sb, ha, hb, he⟩

theorem typed_bool_bin {we : WEnv} (kind : SignalBoolBinKind) (a b : String)
    (wa : we a = 1) (wb : we b = 1) :
    TypedExpr we (.op (signalBoolBinOp kind) [.ref a, .ref b]) 1 := by
  have ha : TypedExpr we (.ref a) 1 := wa ▸ TypedExpr.ref a (by omega)
  have hb : TypedExpr we (.ref b) 1 := wb ▸ TypedExpr.ref b (by omega)
  cases kind
  · exact .bin .and ha hb rfl
  · exact .bin .or ha hb rfl
  · exact .bin .xor ha hb rfl

theorem bool_bin_rhs (kind : SignalBoolBinKind) (we : WEnv) (env : Env)
    (a b : String) (x y : Bool) (ha : env a = encodeBool x) (hb : env b = encodeBool y)
    (wa : we a = 1) (wb : we b = 1) :
    evalExpr we env (.op (signalBoolBinOp kind) [.ref a, .ref b]) =
      some (encodeBool (boolBinValue kind x y)) := by
  cases kind <;> cases x <;> cases y <;>
    simp [signalBoolBinOp, boolBinValue, evalExpr, evalList, evalOp, widthOf, ha, hb, wa, wb, encodeBool, mask]

theorem boolBin_shape {ctx ρ β we mems initial rec ae be kind hint named n va vb s t w}
    (ca : Child rec ctx ρ β we mems initial ae "a" n va)
    (cb : Child rec ctx ρ β we mems initial be "b" n vb)
    (lookup : Lookup ctx ρ β s)
    (hr : Returns (translateBoolBinary rec kind ae be hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateBoolBinary_returns hr
  have fa := ca.frame s sa a lookup ra
  have fb := cb.frame sa sb b (lookup.transfer fa) rb
  obtain ⟨fe, fresh⟩ := emit_bool_frame (by cases kind <;> rfl) re
  refine ⟨(fa.trans fb).trans fe, ?_⟩
  cases hu : s.usedNames.contains w
  · rfl
  · have := fb.used w (fa.used w hu); simp [fresh] at this

theorem boolBin_fresh {ctx ρ β we mems initial rec ae be kind hint named}
    (x y : Bool)
    (ca : Child rec ctx ρ β we mems initial ae "a" 1 (encodeBool x))
    (cb : Child rec ctx ρ β we mems initial be "b" 1 (encodeBool y)) :
    FreshAction (translateBoolBinary rec kind ae be hint named) ctx ρ β we mems initial
      1 (encodeBool (boolBinValue kind x y)) := by
  refine ⟨⟨fun _ _ _ lookup hr => (boolBin_shape ca cb lookup hr).1, ?_⟩,
    fun _ _ _ lookup hr => (boolBin_shape ca cb lookup hr).2⟩
  intro s t w prior h widths hr
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateBoolBinary_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases kind <;> rfl) re).1
  have aout := ca.sem s sa a prior h ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va, ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb b va ia (fe.decls.widths widths) rb
  obtain ⟨vb, ib, bv, bf⟩ := bout.execution
  have step := emitBoolResult_mixed ib
    (typed_bool_bin kind a b aout.width_eq bout.width_eq)
    (bool_bin_rhs kind we vb a b x y ((bf a aout.used).trans av) bv aout.width_eq bout.width_eq) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨step.used, step.width_eq, fun z hz => step.grows z (fb.used z (fa.used z hz)),
    result, inv, val, fun z hz => (frame z (fb.used z (fa.used z hz))).trans
      ((bf z (fa.used z hz)).trans (af z hz))⟩

theorem boolBin_step (rec : TranslateFn) (kind : SignalBoolBinKind) (dom ae be : Lean.Expr)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (boolBinE kind dom ae be) hint top named =
      translateFallback rec (boolBinE kind dom ae be) hint top named := by
  have hf : (boolBinE kind dom ae be).getAppFn =
      .const (signalBoolBinName kind) [.zero, .zero, .zero] := rfl
  have shape : translateCoreShape (boolBinE kind dom ae be) = false := by
    simp only [translateCoreShape, hf, boolBin_width_none]
    cases kind <;> simp [signalBoolBinName, signalBinOpOf]
  have core : translateCore rec (boolBinE kind dom ae be) hint top named = pure none := by
    unfold translateCore
    change (if signalBoolBinName kind == ``Sparkle.Core.Signal.Signal.pure then _ else _) = _
    rw [boolBin_width_none]
    cases kind <;> simp [signalBoolBinName, signalBinOpOf]
  simp [translateStepWith, shape, core]
  rfl

theorem boolBin_contract {rec ctx ρ β we mems initial dom ae be}
    (kind : SignalBoolBinKind) (a b : Bool)
    (da : BoolDenotes ρ β ae a) (db : BoolDenotes ρ β be b)
    (ca : Child rec ctx ρ β we mems initial ae "a" 1 (encodeBool a))
    (cb : Child rec ctx ρ β we mems initial be "b" 1 (encodeBool b)) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (boolBinE kind dom ae be) 1 (encodeBool (boolBinValue kind a b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolBinE kind dom ae be) hint top named)
      ctx ρ β we mems initial 1 (encodeBool (boolBinValue kind a b)) := by
    intro hint top named
    rw [boolBin_step, translateFallback_bool rec _ hint top named (by cases kind <;> rfl)]
    apply cached_action (BoolDenotes.quoteBoolBin kind dom ae be da db)
    rw [translateBoolUncachedWith_boolBin]
    exact boolBin_fresh a b ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem boolEq_step (rec : TranslateFn) (dom ae be : Lean.Expr)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (boolEqE dom ae be) hint top named =
      translateFallback rec (boolEqE dom ae be) hint top named := by
  have shape : translateCoreShape (boolEqE dom ae be) = false := rfl
  have core : translateCore rec (boolEqE dom ae be) hint top named = pure none := rfl
  simp [translateStepWith, shape, core]
  rfl

theorem boolEq_contract {rec ctx ρ β we mems initial dom ae be}
    (a b : Bool) (da : BoolDenotes ρ β ae a) (db : BoolDenotes ρ β be b)
    (ca : Child rec ctx ρ β we mems initial ae "a" 1 (encodeBool a))
    (cb : Child rec ctx ρ β we mems initial be "b" 1 (encodeBool b)) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (boolEqE dom ae be) 1 (encodeBool (a == b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolEqE dom ae be) hint top named)
      ctx ρ β we mems initial 1 (encodeBool (a == b)) := by
    intro hint top named
    rw [boolEq_step, translateFallback_bool rec _ hint top named rfl]
    apply cached_action (BoolDenotes.quoteBoolEq dom ae be da db)
    change FreshAction (translateSignalCompare rec .eq ae be hint named)
      ctx ρ β we mems initial 1 (encodeBool (a == b))
    have av : (BitVec.ofNat 1 (encodeBool a)).toNat = encodeBool a := by cases a <;> rfl
    have bv : (BitVec.ofNat 1 (encodeBool b)).toNat = encodeBool b := by cases b <;> rfl
    have val : compareValue .eq (BitVec.ofNat 1 (encodeBool a)) (BitVec.ofNat 1 (encodeBool b)) =
        (a == b) := by cases a <;> cases b <;> rfl
    rw [← val]
    apply compare_fresh _ _ (by decide)
    · simpa only [av] using ca
    · simpa only [bv] using cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem boolNot_step (rec : TranslateFn) (dom ae : Lean.Expr)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (boolNotE dom ae) hint top named =
      translateFallback rec (boolNotE dom ae) hint top named := by
  have shape : translateCoreShape (boolNotE dom ae) = false := rfl
  have core : translateCore rec (boolNotE dom ae) hint top named = pure none := rfl
  simp [translateStepWith, shape, core]
  rfl

theorem boolNot_contract {rec ctx ρ β we mems initial dom ae}
    (a : Bool) (da : BoolDenotes ρ β ae a)
    (ca : Child rec ctx ρ β we mems initial ae "a" 1 (encodeBool a))
    (cb : Child rec ctx ρ β we mems initial
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])) "b" 1 0) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (boolNotE dom ae) 1 (encodeBool (!a)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolNotE dom ae) hint top named)
      ctx ρ β we mems initial 1 (encodeBool (!a)) := by
    intro hint top named
    rw [boolNot_step, translateFallback_bool rec _ hint top named rfl]
    apply cached_action (BoolDenotes.quoteBoolNot dom ae da)
    change FreshAction (translateSignalCompare rec .eq ae
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])) hint named) ctx ρ β we mems initial 1 (encodeBool (!a))
    have av : (BitVec.ofNat 1 (encodeBool a)).toNat = encodeBool a := by cases a <;> rfl
    have val : compareValue .eq (BitVec.ofNat 1 (encodeBool a)) (0#1) = !a := by cases a <;> rfl
    rw [← val]
    apply compare_fresh _ _ (by decide)
    · simpa only [av] using ca
    · exact cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem mux_shape {ctx ρ β we mems initial rec ce ae be hint named vc va vb s t w}
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 vc)
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" 1 va)
    (cb : Child rec ctx ρ β we mems initial be "mux_else" 1 vb)
    (lookup : Lookup ctx ρ β s)
    (hr : Returns (translateMuxWith rec (pure .bit) ce ae be hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨c, a, b, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have fc := cc.frame s sc c lookup rc
  have fa := ca.frame sc sa a (lookup.transfer fc) ra
  have fb := cb.frame sa sb b ((lookup.transfer fc).transfer fa) rb
  obtain ⟨fe, fresh⟩ := emit_bool_frame rfl re
  refine ⟨((fc.trans fa).trans fb).trans fe, ?_⟩
  cases hu : s.usedNames.contains w
  · rfl
  · have := fb.used w (fa.used w (fc.used w hu)); simp [fresh] at this

theorem mux_fresh {ctx ρ β we mems initial rec ce ae be hint named}
    (c a b : Bool)
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 (encodeBool c))
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" 1 (encodeBool a))
    (cb : Child rec ctx ρ β we mems initial be "mux_else" 1 (encodeBool b)) :
    FreshAction (translateMuxWith rec (pure .bit) ce ae be hint named) ctx ρ β we mems initial
      1 (encodeBool (if c then a else b)) := by
  refine ⟨⟨fun _ _ _ lookup hr => (mux_shape cc ca cb lookup hr).1, ?_⟩,
    fun _ _ _ lookup hr => (mux_shape cc ca cb lookup hr).2⟩
  intro s t w prior h widths hr
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have lookup := Lookup.ofInputs h.inputs
  have fc := cc.frame s sc cw lookup rc
  have fa := ca.frame sc sa aw (lookup.transfer fc) ra
  have fb := cb.frame sa sb bw ((lookup.transfer fc).transfer fa) rb
  have fe := (emit_bool_frame rfl re).1
  have cout := cc.sem s sc cw prior h (((fa.decls.trans fb.decls).trans fe.decls).widths widths) rc
  obtain ⟨vc, ic, cv, cf⟩ := cout.execution
  have aout := ca.sem sc sa aw vc ic ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va, ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb bw va ia (fe.decls.widths widths) rb
  obtain ⟨vb, ib, bv, bf⟩ := bout.execution
  have cv' : vb cw = encodeBool c := (bf cw (fa.used cw cout.used)).trans ((af cw cout.used).trans cv)
  have av' : vb aw = encodeBool a := (bf aw aout.used).trans av
  have step := emitBoolResult_mixed ib
    (.mux (cout.width_eq ▸ TypedExpr.ref (we := we) cw (by rw [cout.width_eq]; decide))
      (aout.width_eq ▸ TypedExpr.ref (we := we) aw (by rw [aout.width_eq]; decide))
      (bout.width_eq ▸ TypedExpr.ref (we := we) bw (by rw [bout.width_eq]; decide)))
    (bool_mux_rhs we vb cw aw bw c a b cv' av' bv) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => fb.used z (fa.used z (fc.used z hz))
  exact ⟨step.used, step.width_eq, fun z hz => step.grows z (mono z hz), result, inv, val,
    fun z hz => (frame z (mono z hz)).trans ((bf z (fa.used z (fc.used z hz))).trans
      ((af z (fc.used z hz)).trans (cf z hz)))⟩

theorem mux_contract {rec ctx ρ β we mems initial dom ce ae be}
    (c a b : Bool) (dc : BoolDenotes ρ β ce c) (da : BoolDenotes ρ β ae a) (db : BoolDenotes ρ β be b)
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 (encodeBool c))
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" 1 (encodeBool a))
    (cb : Child rec ctx ρ β we mems initial be "mux_else" 1 (encodeBool b)) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (boolMuxE dom ce ae be) 1 (encodeBool (if c then a else b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolMuxE dom ce ae be) hint top named)
      ctx ρ β we mems initial 1 (encodeBool (if c then a else b)) := by
    intro hint top named
    rw [boolMux_step, translateFallback_bool rec _ hint top named rfl]
    apply cached_action (BoolDenotes.quoteMux dom ce ae be dc da db)
    change FreshAction (translateMuxWith rec (pure .bit) ce ae be hint named)
      ctx ρ β we mems initial 1 (encodeBool (if c then a else b))
    exact mux_fresh c a b cc ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

/-- Closed fuel induction for quoted Bool expressions with arbitrary nesting
of comparisons, arithmetic operands and Bool muxes. Inputs use actual fvars. -/
theorem bool_fuel_contract (fuel : Nat) {ctx ρ β we mems initial dom n kb kv}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n)
    (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩) :
    ∀ e, e.WF kb kv n → Contract (translateFuelFix translateStep fuel) ctx ρ β we mems initial
      (quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)
      1 (encodeBool (evalB n bools bits e)) := by
  have bd : ∀ j, j < kb → BoolDenotes ρ β (.fvar (binp j)) (bools j) := fun j hj => .fvar (hb j hj)
  have vd : ∀ j, j < kv → Denotes β (.fvar (vinp j)) n (bits j) := fun j hj => .fvar (hv j hj)
  induction fuel with
  | zero =>
    intro e he
    constructor
    · intro hint top named s t w lookup hr; exact (Returns.throw hr).elim
    · intro hint top named s t w prior h widths hr; exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro e he
    change Contract (translateStepWith translateFallback (translateFuelFix translateStep fuel)) _ _ _ _ _ _ _ _ _
    cases e with
    | inp j => exact bool_input_contract (hb j he)
    | lit b => exact bool_literal_contract b
    | compare le a b =>
      obtain ⟨ha, hb'⟩ := he
      have da := denotesF_inputs (dom := dom) vd a ha
      have db := denotesF_inputs (dom := dom) vd b hb'
      exact compare_contract _ _ hn da db ((bits_fuel_contract fuel hn da).child "a")
        ((bits_fuel_contract fuel hn db).child "b")
    | boolBin k a b =>
      obtain ⟨ha, hb'⟩ := he
      exact boolBin_contract k _ _ (denotesB_quote (dom := dom) bd vd a ha)
        (denotesB_quote (dom := dom) bd vd b hb') ((ih a ha).child "a") ((ih b hb').child "b")
    | boolNot a =>
      exact boolNot_contract _ (denotesB_quote (dom := dom) bd vd a he)
        ((ih a he).child "a") ((ih (.lit false) trivial).child "b")
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      exact boolEq_contract _ _ (denotesB_quote (dom := dom) bd vd a ha)
        (denotesB_quote (dom := dom) bd vd b hb') ((ih a ha).child "a") ((ih b hb').child "b")
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      exact mux_contract _ _ _ (denotesB_quote (dom := dom) bd vd c hc)
        (denotesB_quote (dom := dom) bd vd a ha) (denotesB_quote (dom := dom) bd vd b hb')
        ((ih c hc).child "mux_cond") ((ih a ha).child "mux_then") ((ih b hb').child "mux_else")

/-- Shipping translation now needs no recursive-child premise for this mixed
quoted fragment. Entry invariants and final widths still have to be supplied. -/
theorem translateExprToWire_bool_contract {ctx ρ β we mems initial dom n kb kv}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩)
    (e : BExpr) (he : e.WF kb kv n) :
    Contract (fun e hint top named => translateExprToWire e hint top named) ctx ρ β we mems initial
      (quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)
      1 (encodeBool (evalB n bools bits e)) :=
  bool_fuel_contract translateFuelLimit hn hb hv e he

end Tools.ShippingMixedRecursion
