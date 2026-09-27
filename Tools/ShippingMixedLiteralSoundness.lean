import Tools.ShippingMixedInvariant

/-! BitVec literals in mixed Bool/BitVec states, through the actual core and
validated cache. Final-width agreement remains explicit. -/
namespace Tools.ShippingMixedLiteralSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingTypedExprSoundness Tools.ShippingBuilderSoundness Tools.ShippingScalarSoundness

/-- Declaration growth transports final widths to earlier child states. -/
def DeclGrows (s t : CircuitState) : Prop := ∀ p ∈ s.module.wires, p ∈ t.module.wires

theorem DeclGrows.trans {s t u} (h : DeclGrows s t) (k : DeclGrows t u) : DeclGrows s u :=
  fun p hp => k p (h p hp)

theorem DeclGrows.widths {s t we} (h : DeclGrows s t) (hw : ScalarWidthsAgree we t) :
    ScalarWidthsAgree we s := fun p hp => hw p (h p hp)

/-- Allocation followed by assignment preserves both source types. -/
theorem allocate_assign_mixed {ctx ρ β we mems initial s t prior hint named w n rhs value}
    (h : MixedInv ctx ρ β we mems initial s prior)
    (hw : w = (CircuitM.makeWire hint (.bitVector n) named s).1)
    (hs : t = (CircuitM.emitAssign w rhs (CircuitM.makeWire hint (.bitVector n) named s).2).2)
    (typed : TypedExpr we rhs n) (ev : evalExpr we prior rhs = some value)
    (widths : ScalarWidthsAgree we t) :
    DeclGrows s t ∧ Outcome ctx ρ β we mems initial prior s t w n value := by
  have hm := CircuitM.makeWire_spec hint (.bitVector n) named s
  have fresh : s.usedNames.contains w = false := by rw [hw]; exact hm.1
  have used : t.usedNames = s.usedNames.insert w := by
    rw [hs, emitAssign_usedNames, hm.2.1, ← hw]
  have decl : ({name := w, ty := .bitVector n} : Port) ∈ t.module.wires := by
    rw [hs, emitAssign_wires, hm.2.2.2, hw]; simp
  have width : we w = n := widths _ decl
  have grows : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true := by
    intro z hz; simp [used, Std.HashSet.contains_insert, hz]
  let result := write prior w value
  have frame : ∀ z, s.usedNames.contains z = true → result z = prior z := by
    intro z hz
    have ne : z ≠ w := by intro he; subst z; simp [fresh] at hz
    simp [result, write, ne]
  have body : TypedBody we t := by
    unfold TypedBody
    rw [hs, emitAssign_body_cons, hm.2.2.1]
    intro st hst
    rcases List.mem_cons.mp hst with he | he
    · subst st; exact ⟨w, rhs, rfl, width.symm ▸ typed⟩
    · exact h.typed st he
  have run : Runs we mems initial t result := by
    rw [hs]
    exact emitAssign_sound _ we mems initial prior w rhs value
      (runs_of_body_eq hm.2.2.1 h.runs) ev
  refine ⟨?_, by simp [used], width, grows, result, ?_, ?_, frame⟩
  · intro p hp; rw [hs, emitAssign_wires, hm.2.2.2]; exact List.mem_cons_of_mem _ hp
  · apply h.transfer run body ?_ ?_ grows frame
    · rw [hs, emitAssign_sourceBindings, CircuitM.makeWire_sourceBindings]
    · rw [hs, emitAssign_translateRecord, CircuitM.makeWire_translateRecord]
  · simp [result, write]

theorem literal_payload_mixed {ctx ρ β we mems initial s t prior args hint named r c n v}
    (h : MixedInv ctx ρ β we mems initial s prior) (hn : 0 < n)
    (back : args.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateSignalPureLiteral? args hint named) ctx s r t) :
    ∃ w, r = some w ∧ DeclGrows s t ∧
      Outcome ctx ρ β we mems initial prior s t w n (BitVec.ofNat n v).toNat := by
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
  have val : (BitVec.ofNat n v).toNat = v := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt]
  rw [val]
  exact ⟨w, rfl, allocate_assign_mixed h hw hs (.const _ n hn)
    (evalExpr_const_lt we prior v n lt) widths⟩

theorem mixed_bits_hit {ctx ρ β we mems initial s t prior e w n} {x : BitVec n}
    (h : MixedInv ctx ρ β we mems initial s prior) (hd : Denotes β e n x)
    (hr : Returns (cacheLookupValidated e) ctx s (some w) t) :
    DeclGrows s t ∧ Outcome ctx ρ β we mems initial prior s t w n x.toNat := by
  obtain ⟨hs, hit⟩ := cacheLookupValidated_returns hr
  have he := hit w rfl
  obtain ⟨used, val, width⟩ := h.records.bits w e he n x hd
  subst t
  exact ⟨fun _ hp => hp, used, width, fun _ hz => hz, prior, h, val, fun _ _ => rfl⟩

/-- Core literal lowering works in a state already containing Bool assignments. -/
theorem translateCore_literal_mixed {ctx ρ β we mems initial s t prior e us hint named top rec r n}
    {x : BitVec n} (h : MixedInv ctx ρ β we mems initial s prior) (hn : 0 < n)
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCore rec e hint top named) ctx s r t) :
    ∃ w, r = some w ∧ DeclGrows s t ∧ Outcome ctx ρ β we mems initial prior s t w n x.toNat := by
  unfold translateCore at hr
  split at hr
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at hr
    simp only [beq_self_eq_true, if_true] at hr
    cases hd with
    | fvar _ => simp [Lean.Expr.getAppFn] at fn
    | binary fn' hop _ _ _ _ =>
      rw [fn] at fn'; cases fn'; simp [signalBinOpOf] at hop
    | pureLit _ back lit => exact literal_payload_mixed h hn back lit widths hr

/-- Structural information is available before choosing a semantic width
environment, so it can be used to transport a parent's final-width premise. -/
theorem core_literal_shape {ctx s t e us hint named top rec r n} {x : BitVec n}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (hr : Returns (translateCore rec e hint top named) ctx s r t) :
    ∃ w, r = some w ∧ DeclGrows s t := by
  unfold translateCore at hr
  split at hr
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at hr
    simp only [beq_self_eq_true, if_true] at hr
    obtain ⟨w, he, growth, _⟩ := translateSignalPureLiteral_branch
      (we := fun _ => 0) (mems := fun _ _ => 0) (initial := fun _ => 0) fn hd hr
    exact ⟨w, he, growth.1.2.1⟩

theorem core_literal_recorded {ctx ρ β we mems initial s t prior e us hint named top rec w n cacheable}
    {x : BitVec n} {K : Option String → CompilerM String}
    (h : MixedInv ctx ρ β we mems initial s prior) (hn : 0 < n)
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (hk : ∀ v, K (some v) = (recordTranslation e v cacheable >>= fun _ => pure v))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) :
    DeclGrows s t ∧ Outcome ctx ρ β we mems initial prior s t w n x.toNat := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  obtain ⟨v, he, growth⟩ := core_literal_shape fn hd core
  rw [he, hk] at rest
  obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
  obtain ⟨hw, ht⟩ := Returns.pure rest
  subst w t
  have hs := recordTranslation_returns record
  have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
  obtain ⟨v', hv', _, step⟩ := translateCore_literal_mixed h hn fn hd wm core
  have eq : v' = v := Option.some.inj (hv'.symm.trans he)
  subst v'
  obtain ⟨result, inv, val, frame⟩ := step.execution
  refine ⟨?_, ?_, step.width_eq, ?_, result,
    recordTranslation_mixed_bits inv hd step.used val step.width_eq record, val, frame⟩
  · intro p hp; rw [hs]; exact growth p hp
  · rw [hs]; exact step.used
  · rw [hs]; exact step.grows

/-- The real step, including a validated cache hit or fresh literal plus record. -/
theorem translateStep_literal_mixed {ctx ρ β we mems initial s t prior e us hint named top rec w n}
    {x : BitVec n} (h : MixedInv ctx ρ β we mems initial s prior) (hn : 0 < n)
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateStepWith translateFallback rec e hint top named) ctx s w t) :
    DeclGrows s t ∧ Outcome ctx ρ β we mems initial prior s t w n x.toNat := by
  have nf := isFVar_false_of_const fn
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t
      exact mixed_bits_hit h hd rh
    · apply core_literal_recorded (cacheable := !named && !e.isFVar && !top) h hn fn hd ?_ widths hr
      intro v
      simp only [nf, Bool.false_eq_true, if_false]
  · apply core_literal_recorded (cacheable := !named && !e.isFVar && !top) h hn fn hd ?_ widths hr
    intro v
    simp only [nf, Bool.false_eq_true, if_false]

theorem translateExprToWire_literal_mixed {ctx ρ β we mems initial s t prior e us hint named top w n}
    {x : BitVec n} (h : MixedInv ctx ρ β we mems initial s prior) (hn : 0 < n)
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateExprToWire e hint top named) ctx s w t) :
    DeclGrows s t ∧ Outcome ctx ρ β we mems initial prior s t w n x.toNat := by
  change Returns (translateStepWith translateFallback
    (translateFuelFix translateStep (translateFuelLimit - 1)) e hint top named) ctx s w t at hr
  exact translateStep_literal_mixed h hn fn hd widths hr

end Tools.ShippingMixedLiteralSoundness
