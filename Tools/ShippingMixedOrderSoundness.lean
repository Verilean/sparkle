import Tools.ShippingMixedRecursion
import Tools.ShippingPendingSoundness

/-! Dependency order of the actual mixed translator. BitVec children reuse
the established pending-name protection while carrying the mixed invariant. -/
namespace Tools.ShippingMixedOrderSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingTranslationOrder
open Tools.ShippingPendingSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedBinarySoundness Tools.ShippingMixedRecursion
open Tools.ShippingCompareLoweringSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingBoolLiteralSoundness Tools.ShippingBoolMuxSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingTypedExprSoundness Tools.ShippingScalarSoundness

/-- Ordering does not require a BitVec-only body invariant. -/
def BitsOrders (rec : TranslateFn) (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (we : WEnv) (mems : MEnv) (initial : Env) : Prop :=
  ∀ e hint named n (x : BitVec n) s env0 w t, 0 < n → Denotes β e n x →
    Returns (rec e hint false named) ctx s w t →
    MixedInv ctx ρ β we mems initial s env0 → ScalarWidthsAgree we t → OrderInv s → OrderInv t

theorem binary_orders {rec : TranslateFn} {ctx ρ β we mems initial}
    (ih : ∀ e n (x : BitVec n), 0 < n → Denotes β e n x →
      Contract rec ctx ρ β we mems initial e n x.toNat) (ip : Protects rec ctx β)
    (io : BitsOrders rec ctx ρ β we mems initial)
    {e : Lean.Expr} {m : Name} {us : List Level} {op hint named n} {x : BitVec n}
    {s t : CircuitState} {w : String} {env0 : Sparkle.IR.Semantics.Env}
    (hfn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (hn : 0 < n) (hd : Denotes β e n x)
    (h : Returns (translateCanonicalSignalBinary rec e op e.getAppArgs true true hint named) ctx s w t)
    (hi : MixedInv ctx ρ β we mems initial s env0) (hw : ScalarWidthsAgree we t) (ho : OrderInv s) :
    OrderInv t := by
  cases hd with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | pureLit hfn' _ _ =>
    rw [hfn] at hfn'; cases hfn'; rw [signalBinOpOf_pure] at hop; cases hop
  | @binary _ m' us' bop _ x1 x2 hfn' hop' _ hwid hd1 hd2 =>
    rw [hfn] at hfn'; cases hfn'
    have he : op = bop.operator := by rw [hop] at hop'; exact Option.some.inj hop'
    subst he
    unfold translateCanonicalSignalBinary at h
    simp only [hwid] at h
    obtain ⟨ty, s0, hty, rest⟩ := Returns.bind h
    obtain ⟨hty, hs0⟩ := Returns.pure hty
    rw [hty] at rest
    obtain ⟨res, sA, hm, rest⟩ := Returns.bind rest
    rw [hs0] at hm
    obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
    obtain ⟨wb, sC, hb, rest⟩ := Returns.bind rest
    obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
    obtain ⟨_, ht⟩ := Returns.pure ret
    rw [ht] at hw ⊢
    obtain ⟨hres, hsA⟩ := makeWire_returns hm
    obtain ⟨hf, hu, hbody, _⟩ := CircuitM.makeWire_spec hint (.bitVector n) named s
    rw [← hres] at hf hu
    rw [← hsA] at hu hbody
    have hsb : sA.sourceBindings = s.sourceBindings := by
      rw [hsA]; exact CircuitM.makeWire_sourceBindings _ _ _ _
    have hrec : sA.translateRecord = s.translateRecord := by
      rw [hsA]; exact CircuitM.makeWire_translateRecord _ _ _ _
    have hg : ∀ z, s.usedNames.contains z = true → sA.usedNames.contains z = true := by
      intro z hz; rw [hu]; simp [Std.HashSet.contains_insert, hz]
    have hiA := hi.transfer (runs_of_body_eq hbody hi.runs)
      (by unfold TypedBody; rw [hbody]; exact hi.typed) hsb hrec hg (fun _ _ => rfl)
    obtain ⟨hoA, hpend, hused⟩ := makeWire_order hm ho
    have hpA : Protected ctx β sA res := ⟨hused, hpend,
      by rw [hsb]; exact fresh_not_bound hi.inputs.lookup hf,
      by rw [hrec]; exact fresh_not_recorded hi.records.bits hf⟩
    have ca := ih _ _ x1 hn hd1
    have cb := ih _ _ x2 hn hd2
    have ga := ca.frame "op_a" false false _ _ _ (Lookup.ofInputs hiA.inputs) ha
    have gb := cb.frame "op_b" false false _ _ _ ((Lookup.ofInputs hiA.inputs).transfer ga) hb
    have hwC : ScalarWidthsAgree we sC := by
      intro p hp
      apply hw p
      rw [emitAssign_returns hem, emitAssign_wires]
      exact hp
    have hwB := gb.decls.widths hwC
    have va := ca.sem "op_a" false false _ _ _ _ hiA hwB ha
    obtain ⟨envB, hiB, _, _⟩ := va.execution
    have vb := cb.sem "op_b" false false _ _ _ _ hiB hwC hb
    have hoB := io _ _ _ _ _ _ _ _ _ hn hd1 ha hiA hwB hoA
    have hoC := io _ _ _ _ _ _ _ _ _ hn hd2 hb hiB hwC hoB
    obtain ⟨hpa, hwa⟩ := ip _ _ _ _ _ _ _ _ res hd1 ha hiA.inputs.lookup hpA
    have hpB := hpA.transfer ga.used ga.bindings ga.records hpa
    obtain ⟨hpc, hwb⟩ := ip _ _ _ _ _ _ _ _ res hd2 hb (hiA.inputs.lookup.transfer ga.used ga.bindings) hpB
    apply emitAssign_order hem hoC hpc (gb.used res (ga.used res hused))
    · simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb]
    · intro z hz
      have hz' : z = wa ∨ z = wb := by simpa [refsOf, refsOf.refsList] using hz
      rcases hz' with rfl | rfl
      · exact gb.used _ va.used
      · exact vb.used

theorem core_orders {rec : TranslateFn} {ctx ρ β we mems initial}
    (ih : ∀ e n (x : BitVec n), 0 < n → Denotes β e n x →
      Contract rec ctx ρ β we mems initial e n x.toNat) (ip : Protects rec ctx β)
    (io : BitsOrders rec ctx ρ β we mems initial)
    {e : Lean.Expr} {hint named n} {x : BitVec n} {s t : CircuitState}
    {result : Option String} {env0 : Sparkle.IR.Semantics.Env}
    (hn : 0 < n) (hd : Denotes β e n x)
    (h : Returns (translateCore rec e hint false named) ctx s result t)
    (hi : MixedInv ctx ρ β we mems initial s env0) (ho : OrderInv s) :
    (∃ w, result = some w) ∧ (ScalarWidthsAgree we t → OrderInv t) := by
  cases hd with
  | fvar hv =>
    obtain ⟨ht, hex⟩ := core_leaf_order (.fvar hv) (Or.inl rfl) hi.inputs.lookup h ho
    exact ⟨hex, fun _ => ht⟩
  | pureLit hfn hback hlit =>
    obtain ⟨ht, hex⟩ := core_leaf_order (.pureLit hfn hback hlit)
      (Or.inr ⟨_, hfn⟩) hi.inputs.lookup h ho
    exact ⟨hex, fun _ => ht⟩
  | @binary _ m us bop _ x1 x2 hfn hop hk hwid hd1 hd2 =>
    have hd := Denotes.binary hfn hop hk hwid hd1 hd2
    unfold translateCore at h
    split at h
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at h
      have hm : (m == ``Sparkle.Core.Signal.Signal.pure) = false := by
        cases hh : (m == ``Sparkle.Core.Signal.Signal.pure) with
        | false => rfl
        | true =>
          have he : m = ``Sparkle.Core.Signal.Signal.pure := by simpa using hh
          rw [he, signalBinOpOf_pure] at hop; cases hop
      simp only [hm, Bool.false_eq_true, if_false, hop, hk, hwid] at h
      obtain ⟨w, sd, htr, ret⟩ := Returns.bind h
      obtain ⟨hr, ht⟩ := Returns.pure ret
      refine ⟨⟨w, hr⟩, ?_⟩
      rw [ht]
      intro hw
      exact binary_orders ih ip io hfn hop hn hd htr hi hw ho

theorem core_continuation_orders {rec : TranslateFn} {ctx ρ β we mems initial}
    (ih : ∀ e n (x : BitVec n), 0 < n → Denotes β e n x →
      Contract rec ctx ρ β we mems initial e n x.toNat) (ip : Protects rec ctx β)
    (io : BitsOrders rec ctx ρ β we mems initial)
    {e : Lean.Expr} {hint named c n} {x : BitVec n} {s t : CircuitState}
    {K : Option String → CompilerM String} {result : String} {env0 : Sparkle.IR.Semantics.Env}
    (hK : ∀ name, K (some name) = if e.isFVar = true then pure name else
      (recordTranslation e name c >>= fun _ => pure name))
    (hn : 0 < n) (hd : Denotes β e n x)
    (h : Returns (translateCore rec e hint false named >>= K) ctx s result t)
    (hi : MixedInv ctx ρ β we mems initial s env0) (hw : ScalarWidthsAgree we t) (ho : OrderInv s) :
    OrderInv t := by
  obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
  obtain ⟨⟨w, hr⟩, horder⟩ := core_orders ih ip io hn hd hc hi ho
  rw [hr, hK] at hk
  split at hk
  · have ht := (Returns.pure hk).2
    rw [ht] at hw ⊢; exact horder hw
  · obtain ⟨_, sr, hrec, ret⟩ := Returns.bind hk
    have hs := recordTranslation_returns hrec
    have ht := (Returns.pure ret).2
    rw [ht, hs] at hw ⊢
    exact horder hw

theorem step_orders {fallback : TranslateFn → TranslateFn} {rec : TranslateFn}
    {ctx ρ β we mems initial}
    (ih : ∀ e n (x : BitVec n), 0 < n → Denotes β e n x →
      Contract rec ctx ρ β we mems initial e n x.toNat) (ip : Protects rec ctx β)
    (io : BitsOrders rec ctx ρ β we mems initial) :
    BitsOrders (translateStepWith fallback rec) ctx ρ β we mems initial := by
  intro e hint named n x s env0 result t hn hd h hi hw ho
  unfold translateStepWith at h
  dsimp only at h
  by_cases hc : ((!named && !e.isFVar && !false) && translateCoreShape e) = true
  · rw [if_pos hc] at h
    obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
    have hs := (cacheLookupValidated_returns hc).1
    split at hk
    · rw [(Returns.pure hk).2, hs]; exact ho
    · rw [hs] at hk
      exact core_continuation_orders ih ip io (fun _ => rfl) hn hd hk hi hw ho
  · rw [if_neg hc] at h
    exact core_continuation_orders ih ip io (fun _ => rfl) hn hd h hi hw ho

theorem fuel_orders {ctx ρ β we mems initial} :
    ∀ fuel, BitsOrders (translateFuelFix translateStep fuel) ctx ρ β we mems initial
  | 0 => by
    intro e hint named n x s env0 w t hn hd h hi hw ho
    exact False.elim (Returns.throw h)
  | k + 1 => step_orders (fun _ _ _ hn hd => bits_fuel_contract k hn hd)
      (Tools.ShippingPendingSoundness.fuel_protects (we := we) (mems := mems) (initial := initial) k).2
      (fuel_orders k)

/-- Order obligation for one recursive/action call, alongside the existing
semantic contract used to establish operand reservations. -/
def ActionOrder (action : CompilerM String) (ctx : CompilerState)
    (ρ : BoolValuation) (β : Valuation) (we : WEnv) (mems : MEnv) (initial : Env) : Prop :=
  ∀ s t w prior, Returns action ctx s w t → MixedInv ctx ρ β we mems initial s prior →
    ScalarWidthsAgree we t → OrderInv s → OrderInv t

theorem emit_bool_order {ctx s t w rhs hint named}
    (hr : Returns (emitBoolResult rhs hint named) ctx s w t) (order : OrderInv s)
    (refs : ∀ x ∈ refsOf rhs, s.usedNames.contains x = true) : OrderInv t := by
  obtain ⟨hw, ht⟩ := emitBoolResult_returns hr
  have alloc := CircuitM.makeWire_spec hint .bit named s
  have fresh : s.usedNames.contains w = false := hw ▸ alloc.1
  have old : w ∉ footprint s.module.body := by
    intro hp; have used := order.2 w hp; rw [fresh] at used; cases used
  have noSelf : w ∉ refsOf rhs := by
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

theorem cached_order {ctx ρ β we mems initial lower e hint top named}
    (node : ActionOrder (lower e hint top named) ctx ρ β we mems initial) :
    ActionOrder (translateControlCachedWith lower e hint top named) ctx ρ β we mems initial := by
  intro s t w prior hr h widths order
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · rw [(cacheLookupValidated_returns hit).1]; exact order
  · have hs := recordTranslation_returns record
    have width : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
    have ho := node s sm w prior miss h width order
    rw [hs]
    exact ho

theorem literal_order {rec ctx ρ β we mems initial dom hint named} (b : Bool) :
    ActionOrder (translateStepWith translateFallback rec (literalE dom b) hint false named)
      ctx ρ β we mems initial := by
  have fallback : ActionOrder (translateFallback rec (literalE dom b) hint false named)
      ctx ρ β we mems initial := by
    rw [translateFallback_bool rec _ hint false named (by cases b <;> rfl)]
    apply cached_order
    rw [literal_uncached]
    intro s t w prior hr h widths order
    exact emit_bool_order hr order (by simp [refsOf])
  intro s t w prior hr h widths order
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t; exact order
    · rw [literal_core] at hr
      obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hv, hs⟩ := Returns.pure rv
      subst v sc
      exact fallback s t w prior hr h widths order
  · rw [literal_core] at hr
    obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
    obtain ⟨hv, hs⟩ := Returns.pure rv
    subst v sc
    exact fallback s t w prior hr h widths order

theorem compare_order {ctx ρ β we mems initial rec ae be le hint named n va vb}
    (ca : Child rec ctx ρ β we mems initial ae "a" n va)
    (cb : Child rec ctx ρ β we mems initial be "b" n vb)
    (oa : ActionOrder (rec ae "a" false false) ctx ρ β we mems initial)
    (ob : ActionOrder (rec be "b" false false) ctx ρ β we mems initial) :
    ActionOrder (translateUnsignedCompare rec le ae be hint named) ctx ρ β we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateUnsignedCompare_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases le <;> rfl) re).1
  have wa := (fb.decls.trans fe.decls).widths widths
  have wb := fe.decls.widths widths
  have aout := ca.sem s sa a prior h wa ra
  obtain ⟨va, ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb b va ia wb rb
  apply emit_bool_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra h wa order))
  intro x hx
  have hx : x = a ∨ x = b := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl
  · exact fb.used _ aout.used
  · exact bout.used

theorem mux_order {ctx ρ β we mems initial rec ce ae be hint named vc va vb}
    (cc : Child rec ctx ρ β we mems initial ce "mux_cond" 1 vc)
    (ca : Child rec ctx ρ β we mems initial ae "mux_then" 1 va)
    (cb : Child rec ctx ρ β we mems initial be "mux_else" 1 vb)
    (oc : ActionOrder (rec ce "mux_cond" false false) ctx ρ β we mems initial)
    (oa : ActionOrder (rec ae "mux_then" false false) ctx ρ β we mems initial)
    (ob : ActionOrder (rec be "mux_else" false false) ctx ρ β we mems initial) :
    ActionOrder (translateMuxWith rec (pure .bit) ce ae be hint named) ctx ρ β we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have lookup := Lookup.ofInputs h.inputs
  have fc := cc.frame s sc cw lookup rc
  have fa := ca.frame sc sa aw (lookup.transfer fc) ra
  have fb := cb.frame sa sb bw ((lookup.transfer fc).transfer fa) rb
  have fe := (emit_bool_frame rfl re).1
  have wc := ((fa.decls.trans fb.decls).trans fe.decls).widths widths
  have wa := (fb.decls.trans fe.decls).widths widths
  have wb := fe.decls.widths widths
  have cout := cc.sem s sc cw prior h wc rc
  obtain ⟨vc, ic, _, _⟩ := cout.execution
  have aout := ca.sem sc sa aw vc ic wa ra
  obtain ⟨va, ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb bw va ia wb rb
  apply emit_bool_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra ic wa (oc _ _ _ _ rc h wc order)))
  intro x hx
  have hx : x = cw ∨ x = aw ∨ x = bw := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl | rfl
  · exact fb.used _ (fa.used _ cout.used)
  · exact fb.used _ aout.used
  · exact bout.used

/-- Closed mixed order induction follows the same actual fuel recursion as
the value theorem; no recursive order/protection premise reaches callers. -/
theorem bool_fuel_orders (fuel : Nat) {ctx ρ β we mems initial dom n kb kv}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩) :
    ∀ e, e.WF kb kv n → ∀ hint named,
      ActionOrder (translateFuelFix translateStep fuel
        (quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) hint false named)
        ctx ρ β we mems initial := by
  have vd : ∀ j, j < kv → Denotes β (.fvar (vinp j)) n (bits j) := fun j hj => .fvar (hv j hj)
  induction fuel with
  | zero =>
    intro e he hint named s t w prior hr h widths order
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro e he hint named
    change ActionOrder (translateStepWith translateFallback (translateFuelFix translateStep fuel) _ hint false named) _ _ _ _ _ _
    cases e with
    | inp j =>
      intro s t w prior hr h widths order
      obtain ⟨v, bound, _, _, _⟩ := h.inputs.bool _ _ (hb j he)
      rw [(translateStep_fvar_returns bound hr).2]; exact order
    | lit b => exact literal_order b
    | compare le a b =>
      obtain ⟨ha, hb'⟩ := he
      have da := denotesF_inputs (dom := dom) vd a ha
      have db := denotesF_inputs (dom := dom) vd b hb'
      simp only [quoteB]
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      apply cached_order
      rw [translateBoolUncachedWith_compare]
      exact compare_order ((bits_fuel_contract fuel hn da).child "a")
        ((bits_fuel_contract fuel hn db).child "b")
        (fun s t w prior hr h widths order => fuel_orders fuel _ _ _ _ _ _ _ _ _ hn da hr h widths order)
        (fun s t w prior hr h widths order => fuel_orders fuel _ _ _ _ _ _ _ _ _ hn db hr h widths order)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      simp only [quoteB]
      change ActionOrder (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (boolMuxE dom _ _ _) hint false named) _ _ _ _ _ _
      rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_order
      change ActionOrder (translateMuxWith _ (pure .bit) _ _ _ hint named) _ _ _ _ _ _
      exact mux_order ((bool_fuel_contract fuel hn hb hv c hc).child "mux_cond")
        ((bool_fuel_contract fuel hn hb hv a ha).child "mux_then")
        ((bool_fuel_contract fuel hn hb hv b hb').child "mux_else")
        (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)

theorem translateExprToWire_bool_orders {ctx ρ β we mems initial dom n kb kv}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩)
    (e : BExpr) (he : e.WF kb kv n) (hint : String) (named : Bool) :
    ActionOrder (translateExprToWire
      (quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) hint false named)
      ctx ρ β we mems initial :=
  bool_fuel_orders translateFuelLimit hn hb hv e he hint named

end Tools.ShippingMixedOrderSoundness
