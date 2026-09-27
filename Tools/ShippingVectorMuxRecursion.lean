import Tools.ShippingMixedOrderSoundness

/-! BitVec-result mux trees. Leaves use the established arithmetic fragment;
conditions use the established Bool fragment. This does not yet admit a mux
under an arithmetic or comparison node. -/
namespace Tools.ShippingVectorMuxRecursion
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedLiteralSoundness Tools.ShippingMixedBinarySoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingBoolLiteralSoundness Tools.ShippingBoolMuxSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingPostSoundness Sparkle.IR.OptCheck
open Tools.ShippingTypedExprSoundness Tools.ShippingScalarSoundness
open Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness
open Tools.ShippingMixedRecursion Tools.ShippingMixedOrderSoundness
open Tools.ShippingBuilderSoundness Tools.ShippingTranslationOrder Sparkle.IR.Reorder

inductive VExpr where
  | arith (e : FExpr)
  | mux (c : BExpr) (a b : VExpr)

def VExpr.WF (kb kv n : Nat) : VExpr → Prop
  | .arith e => e.WF kv n
  | .mux c a b => c.WF kb kv n ∧ a.WF kb kv n ∧ b.WF kb kv n

def evalV (n : Nat) (bools : Nat → Bool) (bits : Nat → BitVec n) : VExpr → BitVec n
  | .arith e => evalFE n bits e
  | .mux c a b => if evalB n bools bits c then evalV n bools bits a else evalV n bools bits b

def quoteV (dom : Lean.Expr) (n : Nat) (binp vinp : Nat → Lean.Expr) : VExpr → Lean.Expr
  | .arith e => quoteF dom n vinp e
  | .mux c a b => muxE dom (bitVecE n) (quoteB dom n binp vinp c)
      (quoteV dom n binp vinp a) (quoteV dom n binp vinp b)

theorem emit_vector_frame {ctx s t w cw aw bw hint named n}
    (hr : Returns (emitMuxResult cw aw bw hint named (.bitVector n)) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨hw, ht⟩ := emitMuxResult_returns hr
  refine ⟨?_, hw ▸ (CircuitM.makeWire_spec hint (.bitVector n) named s).1⟩
  rw [ht]
  exact (Frame.makeWire s hint n named).trans (Frame.emitAssign _ w _ rfl)

theorem emit_vector_mixed {ctx ρ β we mems initial s t prior cw aw bw hint named w n value}
    (h : MixedInv ctx ρ β we mems initial s prior)
    (typed : TypedExpr we (.op .mux [.ref cw, .ref aw, .ref bw]) n)
    (ev : evalExpr we prior (.op .mux [.ref cw, .ref aw, .ref bw]) = some value)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitMuxResult cw aw bw hint named (.bitVector n)) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w n value := by
  obtain ⟨hw, ht⟩ := emitMuxResult_returns hr
  have hm := CircuitM.makeWire_spec hint (.bitVector n) named s
  have frame := (emit_vector_frame hr).1
  have fresh : s.usedNames.contains w = false := hw ▸ hm.1
  have decl : ({ name := w, ty := .bitVector n } : Port) ∈ t.module.wires := by
    rw [ht, emitAssign_wires, hm.2.2.2, hw]; simp
  have width : we w = n := widths _ decl
  have used : t.usedNames.contains w = true := by
    rw [ht, emitAssign_usedNames, hm.2.1, ← hw]; simp
  have vals : ∀ z, s.usedNames.contains z = true → write prior w value z = prior z := by
    intro z hz
    have ne : z ≠ w := by intro eq; subst z; rw [fresh] at hz; cases hz
    simp [write, ne]
  refine ⟨used, width, frame.used, write prior w value,
    h.transfer ?_ ?_ frame.bindings ?_ frame.used vals, by simp [write], vals⟩
  · rw [ht]
    exact emitAssign_sound _ we mems initial prior w _ value
      (runs_of_body_eq hm.2.2.1 h.runs) ev
  · unfold TypedBody
    rw [ht, emitAssign_body_cons, hm.2.2.1]
    intro st hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨w, _, rfl, width.symm ▸ typed⟩
    · exact h.typed st hs
  · rw [ht, emitAssign_translateRecord, CircuitM.makeWire_translateRecord]

theorem vector_shape {ctx ρ β we mems initial rec ce ae be hint named n vc va vb s t w}
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 vc)
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" n va)
    (cb : Child rec ctx ρ β we mems initial be "mux_else" n vb)
    (lookup : Lookup ctx ρ β s)
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

theorem vector_fresh {ctx ρ β we mems initial rec ce ae be hint named n}
    (c : Bool) (a b : BitVec n) (hn : 0 < n)
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 (encodeBool c))
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" n a.toNat)
    (cb : Child rec ctx ρ β we mems initial be "mux_else" n b.toNat) :
    FreshAction (translateMuxWith rec (pure (.bitVector n)) ce ae be hint named) ctx ρ β we mems initial
      n (if c then a else b).toNat := by
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
  obtain ⟨vc, ic, cv, cf⟩ := cout.execution
  have aout := ca.sem sc sa aw vc ic ((fb.decls.trans fe.decls).widths widths) ra
  obtain ⟨va, ia, av, af⟩ := aout.execution
  have bout := cb.sem sa sb bw va ia (fe.decls.widths widths) rb
  obtain ⟨vb, ib, bv, bf⟩ := bout.execution
  have cv' : vb cw = encodeBool c := (bf cw (fa.used cw cout.used)).trans ((af cw cout.used).trans cv)
  have av' : vb aw = a.toNat := (bf aw aout.used).trans av
  have step := emit_vector_mixed (value := (if c then a else b).toNat) ib
    (.mux (cout.width_eq ▸ TypedExpr.ref (we := we) cw (by rw [cout.width_eq]; decide))
      (aout.width_eq ▸ TypedExpr.ref (we := we) aw (by rw [aout.width_eq]; exact hn))
      (bout.width_eq ▸ TypedExpr.ref (we := we) bw (by rw [bout.width_eq]; exact hn)))
    (by cases c <;> simp [evalExpr, evalList, evalOp, cv', av', bv, encodeBool]) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => fb.used z (fa.used z (fc.used z hz))
  exact ⟨step.used, step.width_eq, fun z hz => step.grows z (mono z hz), result, inv, val,
    fun z hz => (frame z (mono z hz)).trans ((bf z (fa.used z (fc.used z hz))).trans
      ((af z (fc.used z hz)).trans (cf z hz)))⟩

theorem emit_vector_order {ctx s t w cw aw bw hint named n}
    (hr : Returns (emitMuxResult cw aw bw hint named (.bitVector n)) ctx s w t) (order : OrderInv s)
    (refs : ∀ x ∈ refsOf (.op .mux [.ref cw, .ref aw, .ref bw]), s.usedNames.contains x = true) : OrderInv t := by
  obtain ⟨hw, ht⟩ := emitMuxResult_returns hr
  have alloc := CircuitM.makeWire_spec hint (.bitVector n) named s
  have fresh : s.usedNames.contains w = false := hw ▸ alloc.1
  have old : w ∉ footprint s.module.body := by
    intro hp; have used := order.2 w hp; rw [fresh] at used; cases used
  have noSelf : w ∉ refsOf (.op .mux [.ref cw, .ref aw, .ref bw]) := by
    intro hp; have used := refs w hp; rw [fresh] at used; cases used
  constructor
  · rw [ht, emitAssign_body_cons, alloc.2.2.1, List.reverse_cons]
    exact acyclic_snoc order.1
      (fun h => old ((footprint_reverse_mem _ _).mp h)) noSelf
  · intro x hx
    rw [ht, emitAssign_body_cons, alloc.2.2.1, footprint_cons] at hx
    rw [ht, emitAssign_usedNames, alloc.2.1, ← hw]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [Std.HashSet.contains_insert]
    · rcases List.mem_append.mp hx with hx | hx
      · simp [Std.HashSet.contains_insert, refs x hx]
      · simp [Std.HashSet.contains_insert, order.2 x hx]

theorem vector_order {ctx ρ β we mems initial rec ce ae be hint named n vc va vb}
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 vc)
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" n va)
    (cb : Child rec ctx ρ β we mems initial be "mux_else" n vb)
    (oc : ActionOrder (rec ce "mux_cond" false false) ctx ρ β we mems initial)
    (oa : ActionOrder (rec ae "mux_then" false false) ctx ρ β we mems initial)
    (ob : ActionOrder (rec be "mux_else" false false) ctx ρ β we mems initial) :
    ActionOrder (translateMuxWith rec (pure (.bitVector n)) ce ae be hint named) ctx ρ β we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have lookup := Lookup.ofInputs h.inputs
  have fc := cc.frame s sc cw lookup rc
  have fa := ca.frame sc sa aw (lookup.transfer fc) ra
  have fb := cb.frame sa sb bw ((lookup.transfer fc).transfer fa) rb
  have fe := (emit_vector_frame re).1
  have wc := ((fa.decls.trans fb.decls).trans fe.decls).widths widths
  have wa := (fb.decls.trans fe.decls).widths widths
  have wb := fe.decls.widths widths
  have cout := cc.sem s sc cw prior h wc rc
  obtain ⟨vc, ic, _, _⟩ := cout.execution
  have aout := ca.sem sc sa aw vc ic wa ra
  obtain ⟨va, ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb bw va ia wb rb
  apply emit_vector_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra ic wa (oc _ _ _ _ rc h wc order)))
  intro x hx
  have hx : x = cw ∨ x = aw ∨ x = bw := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl | rfl
  · exact fb.used _ (fa.used _ cout.used)
  · exact fb.used _ aout.used
  · exact bout.used


set_option maxHeartbeats 1000000 in
theorem vector_step (rec : TranslateFn) (dom ce ae be : Lean.Expr) (n : Nat)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (muxE dom (bitVecE n) ce ae be) hint top named =
      translateMuxWith rec (pure (.bitVector n)) ce ae be hint named := by
  have shape : translateCoreShape (muxE dom (bitVecE n) ce ae be) = false := rfl
  have core : translateCore rec (muxE dom (bitVecE n) ce ae be) hint top named = pure none := rfl
  have control : isBoolControl (muxE dom (bitVecE n) ce ae be) = false := by
    change (match canonicalMuxType? (muxE dom (bitVecE n) ce ae be) with
      | some .bit => true | _ => false) = false
    rw [canonicalMuxType?_bitVec]
  have step : translateStepWith translateFallback rec (muxE dom (bitVecE n) ce ae be)
      hint top named = translateFallback rec (muxE dom (bitVecE n) ce ae be) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, canonicalMuxType?_bitVec]
  rfl

theorem vector_contract {rec ctx ρ β we mems initial dom ce ae be n}
    (c : Bool) (a b : BitVec n) (hn : 0 < n)
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 (encodeBool c))
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" n a.toNat)
    (cb : Child rec ctx ρ β we mems initial be "mux_else" n b.toNat) :
    Contract (translateStepWith translateFallback rec) ctx ρ β we mems initial
      (muxE dom (bitVecE n) ce ae be) n (if c then a else b).toNat := by
  constructor
  · intro hint top named s t w lookup hr
    rw [vector_step] at hr
    exact (vector_shape cc ca cb lookup hr).1
  · intro hint top named s t w prior h widths hr
    rw [vector_step] at hr
    exact (vector_fresh c a b hn cc ca cb).sem s t w prior h widths hr

/-- No recursive-child or legacy-handler premise: induction follows the
shipping fuel recursion, including nested vector mux branches. -/
theorem vector_fuel_contract (fuel : Nat) {ctx ρ β we mems initial dom n kb kv}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩) :
    ∀ e, e.WF kb kv n → Contract (translateFuelFix translateStep fuel) ctx ρ β we mems initial
      (quoteV dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)
      n (evalV n bools bits e).toNat := by
  induction fuel with
  | zero =>
    intro e he
    constructor
    · intro hint top named s t w lookup hr; exact (Returns.throw hr).elim
    · intro hint top named s t w prior h widths hr; exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro e he
    cases e with
    | arith e =>
      exact bits_fuel_contract (fuel + 1) hn
        (denotesF_inputs (dom := dom) (fun j hj => .fvar (hv j hj)) e he)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      exact vector_contract _ _ _ hn ((bool_fuel_contract fuel hn hb hv c hc).child "mux_cond")
        ((ih a ha).child "mux_then") ((ih b hb').child "mux_else")

theorem vector_fuel_orders (fuel : Nat) {ctx ρ β we mems initial dom n kb kv}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩) :
    ∀ e, e.WF kb kv n → ∀ hint named,
      ActionOrder (translateFuelFix translateStep fuel
        (quoteV dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) hint false named)
        ctx ρ β we mems initial := by
  induction fuel with
  | zero =>
    intro e he hint named s t w prior hr h widths order
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro e he hint named
    cases e with
    | arith e =>
      intro s t w prior hr h widths order
      exact Tools.ShippingMixedOrderSoundness.fuel_orders (fuel + 1) _ _ _ _ _ _ _ _ _ hn
        (denotesF_inputs (dom := dom) (fun j hj => .fvar (hv j hj)) e he) hr h widths order
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      change ActionOrder (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (muxE dom (bitVecE n) _ _ _) hint false named) _ _ _ _ _ _
      rw [vector_step]
      exact vector_order ((bool_fuel_contract fuel hn hb hv c hc).child "mux_cond")
        ((vector_fuel_contract fuel hn hb hv a ha).child "mux_then")
        ((vector_fuel_contract fuel hn hb hv b hb').child "mux_else")
        (bool_fuel_orders fuel hn hb hv c hc "mux_cond" false)
        (ih a ha "mux_then" false) (ih b hb' "mux_else" false)

end Tools.ShippingVectorMuxRecursion
