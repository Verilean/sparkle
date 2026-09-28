import Tools.ShippingUnifiedInvariant

/-! Recursive translation contracts for the unified Bool/BitVec source domain.
Each node of the actual shipping fuel translator preserves the unified
invariant; the reserved-parent hypotheses of `Inv.emit_reserved` are derived
from child frames rather than assumed. The entry/output connection and the
dependency-order theorem are separate modules. -/
namespace Tools.ShippingUnifiedRecursion
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires binary_returns core_binary_returns)
open Tools.ShippingMixedRecursion (emit_bool_frame compare_step boolBin_step boolEq_step
  boolNot_step translateBoolUncachedWith_boolBin translateBoolBinary_returns typed_bool_bin
  bool_bin_rhs bits_core_frame bits_recorded_frame)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingVectorMuxRecursion (emit_vector_frame vector_step vectorMuxUncached_muxE)

@[simp] theorem toNat_bool (b : Bool) : (Value.bool b).toNat = encodeBool b := rfl
@[simp] theorem toNat_bits (n : Nat) (v : BitVec n) : (Value.bits n v).toNat = v.toNat := rfl
@[simp] theorem kindWidth_bool (b : Bool) : (Value.bool b).kind.width = 1 := rfl
@[simp] theorem kindWidth_bits (n : Nat) (v : BitVec n) : (Value.bits n v).kind.width = n := rfl

/-- Environment-free binding facts, enough for structural child properties. -/
structure Lookup (ctx : CompilerState) (inputs : FVarId → Option Value)
    (s : CircuitState) : Prop where
  lookup : ∀ id v, inputs id = some v → ∃ w, visible ctx s.sourceBindings id = some w ∧
    s.usedNames.contains w = true

theorem Lookup.ofInputs {ctx inputs we s env} (h : Inputs ctx inputs we s env) :
    Lookup ctx inputs s := by
  refine ⟨fun id v hi => ?_⟩
  obtain ⟨w, bound, used, _, _⟩ := h.lookup id v hi
  exact ⟨w, bound, used⟩

theorem Lookup.transfer {ctx inputs s t} (h : Lookup ctx inputs s) (f : Frame s t) :
    Lookup ctx inputs t := by
  refine ⟨fun id v hi => ?_⟩
  obtain ⟨w, bound, used⟩ := h.lookup id v hi
  exact ⟨w, by rw [f.bindings]; exact bound, f.used w used⟩

/-- Structure is available without a semantic or final-width premise; the
semantic half then uses widths transported back from a later sibling. -/
structure Child (rec : TranslateFn) (ctx : CompilerState) (inputs : FVarId → Option Value)
    (we : WEnv) (mems : MEnv) (initial : Env) (e : Lean.Expr) (hint : String)
    (v : Value) : Prop where
  frame : ∀ s t w, Lookup ctx inputs s → Returns (rec e hint false false) ctx s w t → Frame s t
  sem : ∀ s t w prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
    Returns (rec e hint false false) ctx s w t →
    Outcome ctx inputs we mems initial prior s t w v

/-- Unlike a child contract, this covers every top/named flag and hint. -/
structure Contract (rec : TranslateFn) (ctx : CompilerState) (inputs : FVarId → Option Value)
    (we : WEnv) (mems : MEnv) (initial : Env) (e : Lean.Expr) (v : Value) : Prop where
  frame : ∀ hint top named s t w, Lookup ctx inputs s →
    Returns (rec e hint top named) ctx s w t → Frame s t
  sem : ∀ hint top named s t w prior, Inv ctx inputs we mems initial s prior →
    ScalarWidthsAgree we t → Returns (rec e hint top named) ctx s w t →
    Outcome ctx inputs we mems initial prior s t w v

theorem Contract.child {rec ctx inputs we mems initial e v}
    (h : Contract rec ctx inputs we mems initial e v) (hint : String) :
    Child rec ctx inputs we mems initial e hint v :=
  ⟨h.frame hint false false, h.sem hint false false⟩

structure ActionSpec (action : CompilerM String) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (we : WEnv) (mems : MEnv) (initial : Env)
    (v : Value) : Prop where
  frame : ∀ s t w, Lookup ctx inputs s → Returns action ctx s w t → Frame s t
  sem : ∀ s t w prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
    Returns action ctx s w t → Outcome ctx inputs we mems initial prior s t w v

structure FreshAction (action : CompilerM String) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (we : WEnv) (mems : MEnv) (initial : Env)
    (v : Value) : Prop extends ActionSpec action ctx inputs we mems initial v where
  fresh : ∀ s t w, Lookup ctx inputs s → Returns action ctx s w t →
    s.usedNames.contains w = false

/-- Allocate a fresh scalar result and immediately assign it. The reserved
hypotheses of `Inv.emit_reserved` follow from freshness at the pre-state. -/
theorem allocate_assign_outcome {ctx inputs we mems initial s t prior hint named w ty rhs}
    {v : Value} (h : Inv ctx inputs we mems initial s prior)
    (hw : w = (CircuitM.makeWire hint ty named s).1)
    (hs : t = (CircuitM.emitAssign w rhs (CircuitM.makeWire hint ty named s).2).2)
    (tyw : ty.bitWidth = v.kind.width)
    (typed : TypedExpr we rhs v.kind.width) (ev : evalExpr we prior rhs = some v.toNat)
    (widths : ScalarWidthsAgree we t) :
    Outcome ctx inputs we mems initial prior s t w v := by
  have hm := CircuitM.makeWire_spec hint ty named s
  have fresh : s.usedNames.contains w = false := by rw [hw]; exact hm.1
  have used : t.usedNames = s.usedNames.insert w := by
    rw [hs, emitAssign_usedNames, hm.2.1, ← hw]
  have decl : ({name := w, ty := ty} : Port) ∈ t.module.wires := by
    rw [hs, emitAssign_wires, hm.2.2.2, hw]; simp
  have width : we w = v.kind.width := by rw [widths _ decl]; exact tyw
  have grows : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true := by
    intro z hz; simp [used, Std.HashSet.contains_insert, hz]
  have ia : Inv ctx inputs we mems initial (CircuitM.makeWire hint ty named s).2 prior :=
    h.allocate hint ty named
  have inputSafe : ∀ id u, inputs id = some u →
      visible ctx (CircuitM.makeWire hint ty named s).2.sourceBindings id ≠ some w := by
    intro id u hi bound
    rw [CircuitM.makeWire_sourceBindings] at bound
    obtain ⟨z, hz, hu, _, _⟩ := h.inputs.lookup id u hi
    have eq : z = w := Option.some.inj (hz.symm.trans bound)
    subst z; simp [fresh] at hu
  have recordSafe : ∀ e u, (CircuitM.makeWire hint ty named s).2.translateRecord.get? w = some e →
      ¬ Meaning inputs e u := by
    intro e u record
    rw [CircuitM.makeWire_translateRecord] at record
    exact fun meaning => fresh_not_recorded h.records fresh meaning record
  have final := ia.emit_reserved inputSafe recordSafe (width ▸ typed) ev
  rw [← hs] at final
  refine ⟨by simp [used], width, grows, write prior w v.toNat, final, by simp [write], ?_⟩
  intro z hz
  have ne : z ≠ w := by intro eq; subst z; simp [fresh] at hz
  simp [write, ne]

/-- Shared Bool emission preserves the unified invariant. This applies to
literals, comparisons, Bool logic and Bool muxes. -/
theorem emit_bool_outcome {ctx inputs we mems initial s t prior rhs hint named w b}
    (h : Inv ctx inputs we mems initial s prior)
    (typed : TypedExpr we rhs 1) (value : evalExpr we prior rhs = some (encodeBool b))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitBoolResult rhs hint named) ctx s w t) :
    Outcome ctx inputs we mems initial prior s t w (.bool b) := by
  obtain ⟨hw, ht⟩ := emitBoolResult_returns hr
  exact allocate_assign_outcome h hw ht rfl typed value widths

/-- Fresh vector-mux emission at the requested literal width. -/
theorem emit_vector_outcome {ctx inputs we mems initial s t prior cw aw bw hint named w n}
    {x : BitVec n} (h : Inv ctx inputs we mems initial s prior)
    (typed : TypedExpr we (.op .mux [.ref cw, .ref aw, .ref bw]) n)
    (ev : evalExpr we prior (.op .mux [.ref cw, .ref aw, .ref bw]) = some x.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitMuxResult cw aw bw hint named (.bitVector n)) ctx s w t) :
    Outcome ctx inputs we mems initial prior s t w (.bits n x) := by
  obtain ⟨hw, ht⟩ := emitMuxResult_returns hr
  exact allocate_assign_outcome h hw ht rfl typed ev widths

/-- Input leaves for either sort in one case: the real fvar step returns the
prepared binding without touching the state. -/
theorem input_contract {rec ctx inputs we mems initial id v} (hi : inputs id = some v) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial (.fvar id) v := by
  constructor
  · intro hint top named s t w lookup hr
    obtain ⟨z, bound, _⟩ := lookup.lookup id v hi
    obtain ⟨_, ht⟩ := translateStep_fvar_returns bound hr
    subst t; exact Frame.refl s
  · intro hint top named s t w prior h widths hr
    obtain ⟨z, bound, used, val, width⟩ := h.inputs.lookup id v hi
    obtain ⟨hw, ht⟩ := translateStep_fvar_returns bound hr
    subst w t
    exact ⟨used, width, fun _ hz => hz, prior, h, val, fun _ _ => rfl⟩

/-- The cached-wrapper step for one meaningful node: a validated hit reuses
the recorded wire; a miss lowers, records and preserves every prior wire. -/
theorem cached_widths_outcome {ctx inputs we mems initial s t prior e w v lower hint top named}
    (h : Inv ctx inputs we mems initial s prior) (meaning : Meaning inputs e v)
    (widths : ScalarWidthsAgree we t)
    (node : ∀ sm r, ScalarWidthsAgree we sm → Returns (lower e hint top named) ctx s r sm →
      Outcome ctx inputs we mems initial prior s sm r v)
    (hr : Returns (translateControlCachedWith lower e hint top named) ctx s w t) :
    Outcome ctx inputs we mems initial prior s t w v := by
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · exact hit_outcome h meaning hit
  · have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
    have step := node sm w wm miss
    obtain ⟨result, inv, val, frame⟩ := step.execution
    refine ⟨?_, step.width, ?_, result,
      inv.record meaning step.used val step.width record, val, frame⟩
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows

theorem cached_action {ctx inputs we mems initial lower e hint top named v}
    (meaning : Meaning inputs e v)
    (node : FreshAction (lower e hint top named) ctx inputs we mems initial v) :
    ActionSpec (translateControlCachedWith lower e hint top named) ctx inputs we mems initial v := by
  constructor
  · intro s t w lookup hr
    rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
    · have ht := (cacheLookupValidated_returns hit).1
      subst t; exact Frame.refl s
    · exact (node.frame s sm w lookup miss).record_new (node.fresh s sm w lookup miss) record
  · intro s t w prior h widths hr
    exact cached_widths_outcome h meaning widths
      (fun sm r wm miss => node.sem s sm r prior h wm miss) hr

theorem literal_fresh {ctx inputs we mems initial hint named} (b : Bool) :
    FreshAction (emitBoolLiteral b hint named) ctx inputs we mems initial (.bool b) := by
  refine ⟨⟨fun _ _ _ _ hr => (emit_bool_frame rfl hr).1, ?_⟩,
    fun _ _ _ _ hr => (emit_bool_frame rfl hr).2⟩
  intro s t w prior h widths hr
  apply emit_bool_outcome h (.const _ 1 (by decide)) ?_ widths hr
  have he := evalExpr_const_lt we prior (encodeBool b) 1 (encodeBool_lt b)
  cases b <;> simpa [encodeBool] using he

theorem bool_literal_contract {rec ctx inputs we mems initial dom} (b : Bool) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (literalE dom b) (.bool b) := by
  have meaning : Meaning inputs (literalE dom b) (.bool b) := .value (view_boolLit dom b)
  have fallback : ∀ hint top named, ActionSpec
      (translateFallback rec (literalE dom b) hint top named) ctx inputs we mems initial (.bool b) := by
    intro hint top named
    rw [translateFallback_bool rec _ hint top named (by cases b <;> rfl)]
    apply cached_action meaning
    change FreshAction (translateBoolUncachedWith rec _ (literalE dom b) hint top named)
      ctx inputs we mems initial (.bool b)
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
    unfold translateStepWith at hr
    dsimp only at hr
    split at hr
    · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
      have hs := (cacheLookupValidated_returns rh).1
      subst sh
      split at hr
      · obtain ⟨hw, ht⟩ := Returns.pure hr
        subst w t
        exact hit_outcome h meaning rh
      · rw [literal_core] at hr
        obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
        obtain ⟨hv, hs⟩ := Returns.pure rv
        subst v sc
        exact (fallback hint top named).sem s t w prior h widths hr
    · rw [literal_core] at hr
      obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hv, hs⟩ := Returns.pure rv
      subst v sc
      exact (fallback hint top named).sem s t w prior h widths hr


theorem literal_payload_some {ctx s t args hint named r c n v}
    (back : args.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (hr : Returns (translateSignalPureLiteral? args hint named) ctx s r t) :
    ∃ w, r = some w := by
  unfold translateSignalPureLiteral? at hr
  rw [back] at hr
  simp only [Option.bind_some, lit] at hr
  obtain ⟨w, sm, mk, rest⟩ := Returns.bind hr
  obtain ⟨u, se, em, rest⟩ := Returns.bind rest
  obtain ⟨hres, _⟩ := Returns.pure rest
  exact ⟨w, hres⟩

/-- Bits literal payload: fresh allocation and constant assignment. -/
theorem literal_payload_outcome {ctx inputs we mems initial s t prior args hint named r c n v}
    (h : Inv ctx inputs we mems initial s prior) (hn : 0 < n)
    (back : args.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateSignalPureLiteral? args hint named) ctx s r t) :
    ∃ w, r = some w ∧
      Outcome ctx inputs we mems initial prior s t w (.bits n (BitVec.ofNat n v)) := by
  unfold translateSignalPureLiteral? at hr
  rw [back] at hr
  simp only [Option.bind_some, lit] at hr
  obtain ⟨w, sm, mk, rest⟩ := Returns.bind hr
  obtain ⟨hw, hm⟩ := makeWire_returns mk
  obtain ⟨u, se, em, rest⟩ := Returns.bind rest
  obtain ⟨rfl, ht⟩ := Returns.pure rest
  have hs : t = (CircuitM.emitAssign w (.const v n)
      (CircuitM.makeWire hint (.bitVector n) named s).2).2 := by
    rw [ht, emitAssign_returns em, hm]
  have lt := bitVecLitValue?_lt lit
  refine ⟨w, rfl, allocate_assign_outcome h hw hs rfl (.const _ n hn) ?_ widths⟩
  have val : (Value.bits n (BitVec.ofNat n v)).toNat = v := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt]
  rw [val]
  exact evalExpr_const_lt we prior v n lt

/-- Core literal lowering plus its record write under the unified invariant. -/
theorem bits_literal_recorded {ctx inputs we mems initial s t prior e us hint named top rec w n v cacheable}
    {c : Lean.Expr} {K : Option String → CompilerM String}
    (h : Inv ctx inputs we mems initial s prior) (hn : 0 < n)
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (back : e.getAppArgs.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (meaning : Meaning inputs e (.bits n (BitVec.ofNat n v)))
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => pure z))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) :
    Outcome ctx inputs we mems initial prior s t w (.bits n (BitVec.ofNat n v)) := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  unfold translateCore at core
  split at core
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at core
    simp only [beq_self_eq_true, if_true] at core
    obtain ⟨w', hr'⟩ := literal_payload_some back lit core
    subst r
    rw [hk] at rest
    obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
    obtain ⟨hw, ht⟩ := Returns.pure rest
    subst w t
    have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
    obtain ⟨w2, hw2, step⟩ := literal_payload_outcome h hn back lit wm core
    cases Option.some.inj hw2
    obtain ⟨result, inv, val, frame⟩ := step.execution
    refine ⟨?_, step.width, ?_, result,
      inv.record meaning step.used val step.width record, val, frame⟩
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows

/-- The full step for a quoted BitVec literal, through both cache layers. -/
theorem bits_literal_contract {rec ctx inputs we mems initial dom n v}
    {vi : Nat → Lean.Expr} (hn : 0 < n) (hv : v < 2 ^ n) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (quoteF dom n vi (.lit v)) (.bits n (BitVec.ofNat n v)) := by
  have fn : (quoteF dom n vi (.lit v)).getAppFn =
      .const ``Sparkle.Core.Signal.Signal.pure [.zero] := rfl
  have hd : Denotes (fun _ => none) (quoteF dom n vi (.lit v)) n (BitVec.ofNat n v) :=
    .pureLit (us := [.zero]) (c := mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))
      rfl rfl (litValue_natE n v hv)
  have meaning : Meaning inputs (quoteF dom n vi (.lit v)) (.bits n (BitVec.ofNat n v)) :=
    .value (view_bitsLit dom n v hv vi)
  have back : (quoteF dom n vi (.lit v)).getAppArgs.back? =
      some (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) := rfl
  have lit : bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) =
      some (n, v) := litValue_natE n v hv
  have nf := isFVar_false_of_const fn
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
      · apply bits_recorded_frame (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !top)
          fn hd ?_ hr
        intro z; simp only [nf, Bool.false_eq_true, if_false]
    · apply bits_recorded_frame (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !top)
        fn hd ?_ hr
      intro z; simp only [nf, Bool.false_eq_true, if_false]
  · intro hint top named s t w prior h widths hr
    unfold translateStepWith at hr
    dsimp only at hr
    split at hr
    · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
      have hs := (cacheLookupValidated_returns rh).1
      subst sh
      split at hr
      · obtain ⟨hw, ht⟩ := Returns.pure hr
        subst w t
        exact hit_outcome h meaning rh
      · apply bits_literal_recorded (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !top)
          h hn fn back lit meaning ?_ widths hr
        intro z; simp only [nf, Bool.false_eq_true, if_false]
    · apply bits_literal_recorded (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !top)
        h hn fn back lit meaning ?_ widths hr
      intro z; simp only [nf, Bool.false_eq_true, if_false]

/-- The allocator precedes both recursive calls; the reserved parent keeps
its record-free and binding-free status across the children. -/
theorem binary_outcome {ctx inputs we mems initial s t prior rec e args hint named w n}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : Inv ctx inputs we mems initial s prior)
    (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx inputs we mems initial args[args.size - 2]! "op_a" (.bits n x))
    (cb : Child rec ctx inputs we mems initial args[args.size - 1]! "op_b" (.bits n y))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCanonicalSignalBinary rec e op.operator args true true hint named) ctx s w t) :
    Frame s t ∧ Outcome ctx inputs we mems initial prior s t w (.bits n (op.apply x y)) := by
  have lookup := Lookup.ofInputs h.inputs
  obtain ⟨sa, sb, sc, a, b, hw, hsa, ra, rb, ht⟩ := binary_returns width hr
  have alloc := CircuitM.makeWire_spec hint (.bitVector n) named s
  have fresh : s.usedNames.contains w = false := by rw [hw]; exact alloc.1
  have usedA : sa.usedNames.contains w = true := by rw [hsa, alloc.2.1, hw]; simp
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  have fb := ca.frame sa sb a (lookup.transfer fa) ra
  have fc := cb.frame sb sc b ((lookup.transfer fa).transfer fb) rb
  have fd : Frame sc t := by rw [ht]; exact Frame.emitAssign sc w _ (by cases op <;> rfl)
  have all := ((fa.trans fb).trans fc).trans fd
  have ia : Inv ctx inputs we mems initial sa prior := by
    rw [hsa]; exact h.allocate hint (.bitVector n) named
  have wa := ca.sem sa sb a prior ia ((fc.decls.trans fd.decls).widths widths) ra
  obtain ⟨vb, ib, av, aframe⟩ := wa.execution
  have wb := cb.sem sb sc b vb ib (fd.decls.widths widths) rb
  obtain ⟨vc, ic, bv, bframe⟩ := wb.execution
  have av' : vc a = x.toNat := (bframe a wa.used).trans av
  have resultWidth : we w = n := by
    apply widths ({name := w, ty := .bitVector n} : Port)
    apply fd.decls; apply fc.decls; apply fb.decls
    rw [hsa, alloc.2.2.2, hw]; simp
  have sameBindings : sc.sourceBindings = s.sourceBindings :=
    fc.bindings.trans (fb.bindings.trans fa.bindings)
  have oldRecord : ∀ ex, sc.translateRecord.get? w = some ex → s.translateRecord.get? w = some ex := by
    intro ex he
    have old := fb.record_reserved usedA (fc.record_reserved (fb.used w usedA) he)
    rw [hsa, CircuitM.makeWire_translateRecord] at old
    exact old
  have inputSafe : ∀ id u, inputs id = some u → visible ctx sc.sourceBindings id ≠ some w := by
    intro id u hi bound
    rw [sameBindings] at bound
    obtain ⟨z, hz, hu, _, _⟩ := h.inputs.lookup id u hi
    have eq : z = w := Option.some.inj (hz.symm.trans bound)
    subst z; simp [fresh] at hu
  have recordSafe : ∀ ex u, sc.translateRecord.get? w = some ex → ¬ Meaning inputs ex u := by
    intro ex u he meaning
    have hu := (h.records w ex (oldRecord ex he) u meaning).1
    simp [fresh] at hu
  have typed : TypedExpr we (.op op.operator [.ref a, .ref b]) (we w) := by
    rw [resultWidth]
    have wa' : we a = n := wa.width
    have wb' : we b = n := wb.width
    exact .bin op (wa' ▸ TypedExpr.ref (we := we) a (by rw [wa']; exact hn))
      (wb' ▸ TypedExpr.ref (we := we) b (by rw [wb']; exact hn)) (by cases op <;> rfl)
  have bv' : vc b = y.toNat := bv
  have rhs := Binary.rhs_correct op we vc a b x y wa.width wb.width av' bv'
  have final := ic.emit_reserved inputSafe recordSafe typed rhs
  rw [← ht] at final
  refine ⟨all, fd.used w (fc.used w (fb.used w usedA)), resultWidth, all.used,
    write vc w (op.apply x y).toNat, final, ?_, ?_⟩
  · simp [write]
  · intro z hz
    have ne : z ≠ w := by intro eq; subst z; simp [fresh] at hz
    simp only [write, ne, if_false]
    exact (bframe z (fb.used z (fa.used z hz))).trans (aframe z (fa.used z hz))

/-- The structural half is independent of semantic invariants and widths. -/
theorem binary_frame {ctx inputs we mems initial s t rec e args hint named w n va vb}
    (op : Binary) (lookup : Lookup ctx inputs s) (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx inputs we mems initial args[args.size - 2]! "op_a" va)
    (cb : Child rec ctx inputs we mems initial args[args.size - 1]! "op_b" vb)
    (hr : Returns (translateCanonicalSignalBinary rec e op.operator args true true hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨sa, sb, sc, a, b, hw, hsa, ra, rb, ht⟩ := binary_returns width hr
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  have fb := ca.frame sa sb a (lookup.transfer fa) ra
  have fc := cb.frame sb sc b ((lookup.transfer fa).transfer fb) rb
  have fd : Frame sc t := by rw [ht]; exact Frame.emitAssign sc w _ (by cases op <;> rfl)
  refine ⟨((fa.trans fb).trans fc).trans fd, ?_⟩
  rw [hw]; exact (CircuitM.makeWire_spec hint (.bitVector n) named s).1

theorem binary_recorded {ctx inputs we mems initial s t prior rec e m us hint named top w n cacheable}
    {K : Option String → CompilerM String} (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : Inv ctx inputs we mems initial s prior)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (meaning : Meaning inputs e (.bits n (op.apply x y)))
    (ca : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" (.bits n x))
    (cb : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" (.bits n y))
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => pure z))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) :
    Frame s t ∧ Outcome ctx inputs we mems initial prior s t w (.bits n (op.apply x y)) := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  obtain ⟨z, he, lower⟩ := core_binary_returns fn hop kinds width core
  rw [he, hk] at rest
  obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
  obtain ⟨hw, ht⟩ := Returns.pure rest
  subst w t
  have hs := recordTranslation_returns record
  have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
  obtain ⟨growth, fresh⟩ := binary_frame op (Lookup.ofInputs h.inputs) width ca cb lower
  obtain ⟨_, step⟩ := binary_outcome op x y hn h width ca cb wm lower
  obtain ⟨result, inv, val, frame⟩ := step.execution
  refine ⟨growth.record_new fresh record, ?_, step.width, ?_, result,
    inv.record meaning step.used val step.width record, val, frame⟩
  · rw [hs]; exact step.used
  · rw [hs]; exact step.grows

theorem binary_record_frame {ctx inputs we mems initial s t rec e m us hint named top w n va vb cacheable}
    {K : Option String → CompilerM String} (op : Binary) (lookup : Lookup ctx inputs s)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" va)
    (cb : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" vb)
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => pure z))
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) : Frame s t := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  obtain ⟨z, he, lower⟩ := core_binary_returns fn hop kinds width core
  rw [he, hk] at rest
  obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
  obtain ⟨hw, ht⟩ := Returns.pure rest
  subst w t
  obtain ⟨growth, fresh⟩ := binary_frame op lookup width ca cb lower
  exact growth.record_new fresh record

/-- Actual core/cache step for canonical binary nodes whose operands may
contain muxes and comparisons. -/
theorem binary_contract {rec ctx inputs we mems initial e m us n}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (meaning : Meaning inputs e (.bits n (op.apply x y)))
    (ca : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" (.bits n x))
    (cb : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" (.bits n y)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial e
      (.bits n (op.apply x y)) := by
  have nf := isFVar_false_of_const fn
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
        subst w t; exact Frame.refl _
      · apply binary_record_frame (cacheable := !named && !e.isFVar && !top)
          op lookup fn hop kinds width ca cb ?_ hr
        intro z; simp only [nf, Bool.false_eq_true, if_false]
    · apply binary_record_frame (cacheable := !named && !e.isFVar && !top)
        op lookup fn hop kinds width ca cb ?_ hr
      intro z; simp only [nf, Bool.false_eq_true, if_false]
  · intro hint top named s t w prior h widths hr
    unfold translateStepWith at hr
    dsimp only at hr
    split at hr
    · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
      have hs := (cacheLookupValidated_returns rh).1
      subst sh
      split at hr
      · obtain ⟨hw, ht⟩ := Returns.pure hr
        subst w t
        exact hit_outcome h meaning rh
      · exact (binary_recorded (cacheable := !named && !e.isFVar && !top)
          op x y hn h fn hop kinds width meaning ca cb
          (fun z => by simp only [nf, Bool.false_eq_true, if_false]) widths hr).2
    · exact (binary_recorded (cacheable := !named && !e.isFVar && !top)
        op x y hn h fn hop kinds width meaning ca cb
        (fun z => by simp only [nf, Bool.false_eq_true, if_false]) widths hr).2

/-- Structural comparison sequence: both children, then fresh Bool allocation. -/
theorem compare_shape {ctx inputs we mems initial rec ae be le hint named va vb s t w}
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb)
    (lookup : Lookup ctx inputs s)
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

/-- Comparison over any operand sort whose value and width encode the given
bit vectors. Bool operands at width one reuse the same emission. -/
theorem compare_fresh {ctx inputs we mems initial rec ae be le hint named n va vb}
    (x y : BitVec n) (hn : 0 < n)
    (hva : va.toNat = x.toNat) (hwa : va.kind.width = n)
    (hvb : vb.toNat = y.toNat) (hwb : vb.kind.width = n)
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb) :
    FreshAction (translateSignalCompare rec le ae be hint named) ctx inputs we mems initial
      (.bool (compareValue le x y)) := by
  refine ⟨⟨fun _ _ _ lookup hr => (compare_shape ca cb lookup hr).1, ?_⟩,
    fun _ _ _ lookup hr => (compare_shape ca cb lookup hr).2⟩
  intro s t w prior h widths hr
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateSignalCompare_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases le <;> rfl) re).1
  have aout := ca.sem s sa a prior h ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va', ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb b va' ia (fe.decls.widths widths) rb
  obtain ⟨vb', ib, bv, bf⟩ := bout.execution
  have wa : we a = n := by rw [aout.width, hwa]
  have wb : we b = n := by rw [bout.width, hwb]
  have av2 : vb' a = x.toNat := by rw [(bf a aout.used).trans av, hva]
  have bv2 : vb' b = y.toNat := by rw [bv, hvb]
  have step := emit_bool_outcome ib (typed_compare_refs le hn wa wb)
    (compare_rhs_correct le x y we vb' a b av2 bv2 wa wb) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨step.used, step.width, fun z hz => step.grows z (fb.used z (fa.used z hz)),
    result, inv, val, fun z hz => (frame z (fb.used z (fa.used z hz))).trans
      ((bf z (fa.used z hz)).trans (af z hz))⟩

theorem compare_contract {rec ctx inputs we mems initial dom ae be n le}
    (x y : BitVec n) (hn : 0 < n)
    (meaning : Meaning inputs (compareE le dom n ae be) (.bool (compareValue le x y)))
    (ca : Child rec ctx inputs we mems initial ae "a" (.bits n x))
    (cb : Child rec ctx inputs we mems initial be "b" (.bits n y)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (compareE le dom n ae be) (.bool (compareValue le x y)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (compareE le dom n ae be)
        hint top named) ctx inputs we mems initial (.bool (compareValue le x y)) := by
    intro hint top named
    rw [compare_step, translateFallback_bool rec _ hint top named (by cases le <;> rfl)]
    apply cached_action meaning
    rw [translateBoolUncachedWith_compare]
    exact compare_fresh x y hn rfl rfl rfl rfl ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem boolBin_shape {ctx inputs we mems initial rec ae be kind hint named va vb s t w}
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb)
    (lookup : Lookup ctx inputs s)
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

theorem boolBin_fresh {ctx inputs we mems initial rec ae be kind hint named}
    (x y : Bool)
    (ca : Child rec ctx inputs we mems initial ae "a" (.bool x))
    (cb : Child rec ctx inputs we mems initial be "b" (.bool y)) :
    FreshAction (translateBoolBinary rec kind ae be hint named) ctx inputs we mems initial
      (.bool (boolBinValue kind x y)) := by
  refine ⟨⟨fun _ _ _ lookup hr => (boolBin_shape ca cb lookup hr).1, ?_⟩,
    fun _ _ _ lookup hr => (boolBin_shape ca cb lookup hr).2⟩
  intro s t w prior h widths hr
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateBoolBinary_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases kind <;> rfl) re).1
  have aout := ca.sem s sa a prior h ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va', ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb b va' ia (fe.decls.widths widths) rb
  obtain ⟨vb', ib, bv, bf⟩ := bout.execution
  have step := emit_bool_outcome ib
    (typed_bool_bin kind a b aout.width bout.width)
    (bool_bin_rhs kind we vb' a b x y ((bf a aout.used).trans av) bv aout.width bout.width)
    widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨step.used, step.width, fun z hz => step.grows z (fb.used z (fa.used z hz)),
    result, inv, val, fun z hz => (frame z (fb.used z (fa.used z hz))).trans
      ((bf z (fa.used z hz)).trans (af z hz))⟩

theorem boolBin_contract {rec ctx inputs we mems initial dom ae be}
    (kind : SignalBoolBinKind) (a b : Bool)
    (meaning : Meaning inputs (boolBinE kind dom ae be) (.bool (boolBinValue kind a b)))
    (ca : Child rec ctx inputs we mems initial ae "a" (.bool a))
    (cb : Child rec ctx inputs we mems initial be "b" (.bool b)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (boolBinE kind dom ae be) (.bool (boolBinValue kind a b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolBinE kind dom ae be) hint top named)
      ctx inputs we mems initial (.bool (boolBinValue kind a b)) := by
    intro hint top named
    rw [boolBin_step, translateFallback_bool rec _ hint top named (by cases kind <;> rfl)]
    apply cached_action meaning
    rw [translateBoolUncachedWith_boolBin]
    exact boolBin_fresh a b ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem boolEq_contract {rec ctx inputs we mems initial dom ae be}
    (a b : Bool)
    (meaning : Meaning inputs (boolEqE dom ae be) (.bool (a == b)))
    (ca : Child rec ctx inputs we mems initial ae "a" (.bool a))
    (cb : Child rec ctx inputs we mems initial be "b" (.bool b)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (boolEqE dom ae be) (.bool (a == b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolEqE dom ae be) hint top named)
      ctx inputs we mems initial (.bool (a == b)) := by
    intro hint top named
    rw [boolEq_step, translateFallback_bool rec _ hint top named rfl]
    apply cached_action meaning
    change FreshAction (translateSignalCompare rec .eq ae be hint named)
      ctx inputs we mems initial (.bool (a == b))
    have val : compareValue .eq (BitVec.ofNat 1 (encodeBool a)) (BitVec.ofNat 1 (encodeBool b)) =
        (a == b) := by cases a <;> cases b <;> rfl
    rw [← val]
    exact compare_fresh _ _ (by decide) (by cases a <;> rfl) rfl (by cases b <;> rfl) rfl ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem boolNot_contract {rec ctx inputs we mems initial dom ae}
    (a : Bool)
    (meaning : Meaning inputs (boolNotE dom ae) (.bool (!a)))
    (ca : Child rec ctx inputs we mems initial ae "a" (.bool a))
    (cb : Child rec ctx inputs we mems initial
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])) "b" (.bool false)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (boolNotE dom ae) (.bool (!a)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolNotE dom ae) hint top named)
      ctx inputs we mems initial (.bool (!a)) := by
    intro hint top named
    rw [boolNot_step, translateFallback_bool rec _ hint top named rfl]
    apply cached_action meaning
    change FreshAction (translateSignalCompare rec .eq ae
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])) hint named) ctx inputs we mems initial (.bool (!a))
    have val : compareValue .eq (BitVec.ofNat 1 (encodeBool a)) (0#1) = !a := by cases a <;> rfl
    rw [← val]
    exact compare_fresh _ _ (by decide) (by cases a <;> rfl) rfl rfl rfl ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem mux_shape {ctx inputs we mems initial rec ce ae be hint named vc va vb s t w}
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" vc)
    (ca : Child rec ctx inputs we mems initial ae "mux_then" va)
    (cb : Child rec ctx inputs we mems initial be "mux_else" vb)
    (lookup : Lookup ctx inputs s)
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

theorem mux_fresh {ctx inputs we mems initial rec ce ae be hint named}
    (c a b : Bool)
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" (.bool c))
    (ca : Child rec ctx inputs we mems initial ae "mux_then" (.bool a))
    (cb : Child rec ctx inputs we mems initial be "mux_else" (.bool b)) :
    FreshAction (translateMuxWith rec (pure .bit) ce ae be hint named) ctx inputs we mems initial
      (.bool (if c then a else b)) := by
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
  obtain ⟨vc', ic, cv, cf⟩ := cout.execution
  have aout := ca.sem sc sa aw vc' ic ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va', ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb bw va' ia (fe.decls.widths widths) rb
  obtain ⟨vb', ib, bv, bf⟩ := bout.execution
  have cv' : vb' cw = encodeBool c := (bf cw (fa.used cw cout.used)).trans ((af cw cout.used).trans cv)
  have av' : vb' aw = encodeBool a := (bf aw aout.used).trans av
  have wc : we cw = 1 := cout.width
  have wa : we aw = 1 := aout.width
  have wb : we bw = 1 := bout.width
  have step := emit_bool_outcome ib
    (.mux (wc ▸ TypedExpr.ref (we := we) cw (by rw [wc]; decide))
      (wa ▸ TypedExpr.ref (we := we) aw (by rw [wa]; decide))
      (wb ▸ TypedExpr.ref (we := we) bw (by rw [wb]; decide)))
    (bool_mux_rhs we vb' cw aw bw c a b cv' av' bv) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => fb.used z (fa.used z (fc.used z hz))
  exact ⟨step.used, step.width, fun z hz => step.grows z (mono z hz), result, inv, val,
    fun z hz => (frame z (mono z hz)).trans ((bf z (fa.used z (fc.used z hz))).trans
      ((af z (fc.used z hz)).trans (cf z hz)))⟩

theorem mux_contract {rec ctx inputs we mems initial dom ce ae be}
    (c a b : Bool)
    (meaning : Meaning inputs (boolMuxE dom ce ae be) (.bool (if c then a else b)))
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" (.bool c))
    (ca : Child rec ctx inputs we mems initial ae "mux_then" (.bool a))
    (cb : Child rec ctx inputs we mems initial be "mux_else" (.bool b)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (boolMuxE dom ce ae be) (.bool (if c then a else b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (boolMuxE dom ce ae be) hint top named)
      ctx inputs we mems initial (.bool (if c then a else b)) := by
    intro hint top named
    rw [boolMux_step, translateFallback_bool rec _ hint top named rfl]
    apply cached_action meaning
    change FreshAction (translateMuxWith rec (pure .bit) ce ae be hint named)
      ctx inputs we mems initial (.bool (if c then a else b))
    exact mux_fresh c a b cc ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

theorem vector_shape {ctx inputs we mems initial rec ce ae be hint named n vc va vb s t w}
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" vc)
    (ca : Child rec ctx inputs we mems initial ae "mux_then" va)
    (cb : Child rec ctx inputs we mems initial be "mux_else" vb)
    (lookup : Lookup ctx inputs s)
    (hr : Returns (translateMuxWith rec (pure (.bitVector n)) ce ae be hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨c, a, b, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have fc := cc.frame s sc c lookup rc
  have fa := ca.frame sc sa a (lookup.transfer fc) ra
  have fb := cb.frame sa sb b ((lookup.transfer fc).transfer fa) rb
  obtain ⟨fe, fresh⟩ := emit_vector_frame re
  refine ⟨((fc.trans fa).trans fb).trans fe, ?_⟩
  cases hu : s.usedNames.contains w
  · rfl
  · have := fb.used w (fa.used w (fc.used w hu)); simp [fresh] at this

theorem vector_fresh {ctx inputs we mems initial rec ce ae be hint named n}
    (c : Bool) (a b : BitVec n) (hn : 0 < n)
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" (.bool c))
    (ca : Child rec ctx inputs we mems initial ae "mux_then" (.bits n a))
    (cb : Child rec ctx inputs we mems initial be "mux_else" (.bits n b)) :
    FreshAction (translateMuxWith rec (pure (.bitVector n)) ce ae be hint named)
      ctx inputs we mems initial (.bits n (if c then a else b)) := by
  refine ⟨⟨fun _ _ _ lookup hr => (vector_shape cc ca cb lookup hr).1, ?_⟩,
    fun _ _ _ lookup hr => (vector_shape cc ca cb lookup hr).2⟩
  intro s t w prior h widths hr
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have lookup := Lookup.ofInputs h.inputs
  have fc := cc.frame s sc cw lookup rc
  have fa := ca.frame sc sa aw (lookup.transfer fc) ra
  have fb := cb.frame sa sb bw ((lookup.transfer fc).transfer fa) rb
  have fe := (emit_vector_frame re).1
  have cout := cc.sem s sc cw prior h (((fa.decls.trans fb.decls).trans fe.decls).widths widths) rc
  obtain ⟨vc', ic, cv, cf⟩ := cout.execution
  have aout := ca.sem sc sa aw vc' ic ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va', ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb bw va' ia (fe.decls.widths widths) rb
  obtain ⟨vb', ib, bv, bf⟩ := bout.execution
  have cv' : vb' cw = encodeBool c := (bf cw (fa.used cw cout.used)).trans ((af cw cout.used).trans cv)
  have av' : vb' aw = a.toNat := (bf aw aout.used).trans av
  have wc : we cw = 1 := cout.width
  have wa : we aw = n := aout.width
  have wb : we bw = n := bout.width
  have step := emit_vector_outcome (x := if c then a else b) ib
    (.mux (wc ▸ TypedExpr.ref (we := we) cw (by rw [wc]; decide))
      (wa ▸ TypedExpr.ref (we := we) aw (by rw [wa]; exact hn))
      (wb ▸ TypedExpr.ref (we := we) bw (by rw [wb]; exact hn)))
    (by cases c <;> simp [evalExpr, evalList, evalOp, cv', av', bv, encodeBool]) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => fb.used z (fa.used z (fc.used z hz))
  exact ⟨step.used, step.width, fun z hz => step.grows z (mono z hz), result, inv, val,
    fun z hz => (frame z (mono z hz)).trans ((bf z (fa.used z (fc.used z hz))).trans
      ((af z (fc.used z hz)).trans (cf z hz)))⟩

theorem vector_contract {rec ctx inputs we mems initial dom ce ae be n}
    (c : Bool) (a b : BitVec n) (hn : 0 < n)
    (meaning : Meaning inputs (muxE dom (bitVecE n) ce ae be) (.bits n (if c then a else b)))
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" (.bool c))
    (ca : Child rec ctx inputs we mems initial ae "mux_then" (.bits n a))
    (cb : Child rec ctx inputs we mems initial be "mux_else" (.bits n b)) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (muxE dom (bitVecE n) ce ae be) (.bits n (if c then a else b)) := by
  have step : ∀ hint top named, ActionSpec
      (translateStepWith translateFallback rec (muxE dom (bitVecE n) ce ae be) hint top named)
      ctx inputs we mems initial (.bits n (if c then a else b)) := by
    intro hint top named
    rw [vector_step]
    apply cached_action meaning
    show FreshAction (translateVectorMuxUncachedWith rec n (muxE dom (bitVecE n) ce ae be)
      hint top named) ctx inputs we mems initial (.bits n (if c then a else b))
    rw [vectorMuxUncached_muxE]
    exact vector_fresh c a b hn cc ca cb
  exact ⟨fun hint top named => (step hint top named).frame,
    fun hint top named => (step hint top named).sem⟩

/-- Closed fuel induction for the unified mutually recursive source domain.
Mux nodes may sit under arithmetic and comparison parents and vice versa. -/
theorem fuel_contract (fuel : Nat) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {n kb kv : Nat}
    {bi vi : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n)
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits n (bits j))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv n →
      Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
        (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
        (pack n s (eval n bools bits e)) := by
  induction fuel with
  | zero =>
    intro s e he
    constructor
    · intro hint top named s' t w lookup hr; exact (Returns.throw hr).elim
    · intro hint top named s' t w prior h widths hr; exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he
    change Contract (translateStepWith translateFallback (translateFuelFix translateStep fuel)) _ _ _ _ _ _ _
    cases e with
    | boolInput j => exact input_contract (hb j he)
    | bitsInput j => exact input_contract (hv j he)
    | boolLit b => exact bool_literal_contract b
    | bitsLit v => exact bits_literal_contract hn he
    | binary op a b =>
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b) n
      have ca : Child (translateFuelFix translateStep fuel) ctx inputs we mems initial
          ((binE dom n op (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[
              (binE dom n op (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
                (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 2]!)
          "op_a" (.bits n (eval n bools bits a)) := by
        rw [ck.2.2.2.2.1]; exact (ih a ha).child "op_a"
      have cb : Child (translateFuelFix translateStep fuel) ctx inputs we mems initial
          ((binE dom n op (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[
              (binE dom n op (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
                (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 1]!)
          "op_b" (.bits n (eval n bools bits b)) := by
        rw [ck.2.2.2.2.2.1]; exact (ih b hb').child "op_b"
      exact binary_contract op _ _ hn ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1
        (meaning_quote hb hv (.binary op a b) ⟨ha, hb'⟩) ca cb
    | compare op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact compare_contract _ _ hn (meaning_quote hb hv (.compare op a b) ⟨ha, hb'⟩)
        ((ih a ha).child "a") ((ih b hb').child "b")
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact boolBin_contract op _ _ (meaning_quote hb hv (.boolBinary op a b) ⟨ha, hb'⟩)
        ((ih a ha).child "a") ((ih b hb').child "b")
    | boolNot a =>
      exact boolNot_contract _ (meaning_quote hb hv (.boolNot a) he)
        ((ih a he).child "a") ((ih (.boolLit false) trivial).child "b")
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      exact boolEq_contract _ _ (meaning_quote hb hv (.boolEq a b) ⟨ha, hb'⟩)
        ((ih a ha).child "a") ((ih b hb').child "b")
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        exact mux_contract _ _ _ (meaning_quote hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
          ((ih c hc).child "mux_cond") ((ih a ha).child "mux_then") ((ih b hb').child "mux_else")
      | bits =>
        exact vector_contract _ _ _ hn (meaning_quote hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
          ((ih c hc).child "mux_cond") ((ih a ha).child "mux_then") ((ih b hb').child "mux_else")

/-- Shipping translation needs no recursive-child premise for the unified
quoted fragment. Entry invariants and final widths remain explicit. -/
theorem translateExprToWire_contract {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {n kb kv : Nat}
    {bi vi : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n)
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits n (bits j)))
    {s : SType} (e : Term s) (he : e.WF kb kv n) :
    Contract (fun e hint top named => translateExprToWire e hint top named) ctx inputs we mems initial
      (quote dom n (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
      (pack n s (eval n bools bits e)) :=
  fuel_contract translateFuelLimit hn hb hv e he

end Tools.ShippingUnifiedRecursion
