import Tools.ShippingUnifiedProtection
import Tools.ShippingContractEntrySoundness

/-! Width-polymorphic output emission from the unified translation contract.
The prepared port layout supplies the unified input lookup; callers pass no
child-correctness or recompilation premise. -/
namespace Tools.ShippingUnifiedEntrySoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion Tools.ShippingUnifiedProtection
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness Tools.ShippingScalarSoundness
open Tools.ShippingBuilderSoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness
open Tools.ShippingTypedPostSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness
open Tools.ShippingMixedOutputSoundness (PortInputs initial_mixed declaredWidths declaredWidths_agree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingMixedEntrySoundness (weOf_eq_moduleWidths moduleWidths_finish)
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingTranslationOrder (OrderInv)

/-- The prepared port layout provides the unified binding lookup. -/
theorem lookup_of_ports {ctx ρ β s initial} (h : PortInputs ctx ρ β s initial)
    (hw : WiresOk s) : Lookup ctx (inputValues ρ β) s := by
  constructor
  intro id v hi
  unfold inputValues at hi
  cases hb : ρ id with
  | some b =>
    simp only [hb] at hi
    cases hi
    obtain ⟨w, bound, decl, _⟩ := h.bool id b hb
    exact ⟨w, bound, hw.2 _ decl⟩
  | none =>
    simp only [hb] at hi
    cases hv : β id with
    | none => simp [hv] at hi
    | some value =>
      obtain ⟨n, x⟩ := value
      simp only [hv, Option.map_some, Option.some.injEq] at hi
      subst v
      obtain ⟨w, bound, decl, _⟩ := h.bits id n x hv
      exact ⟨w, bound, hw.2 _ decl⟩

/-- At the first leaf there is no emitted code or cache record. -/
theorem initial_unified {ctx ρ β we mems initial s}
    (body : s.module.body = []) (record : s.translateRecord = {})
    (separate : Separate ρ β)
    (inputs : Tools.ShippingMixedInvariant.Inputs ctx ρ β we s initial) :
    Inv ctx (inputValues ρ β) we mems initial s initial :=
  have mi := initial_mixed (mems := mems) body record separate inputs
  ⟨mi.runs, Inputs.of_mixed inputs, Records.empty record, mi.typed⟩

/-- The actual leaf emitter preserves declaration uniqueness. -/
theorem emitLeaves_structure {rec ctx inputs we mems initial s t e v cache logProf returned}
    (contract : Contract rec ctx inputs we mems initial e v)
    (lookup : Lookup ctx inputs s) (wires : WiresOk s)
    (hr : Returns (emitLeaves rec cache logProf [("out", e)] none 0) ctx s returned t) :
    DeclGrows s t ∧ WiresOk t := by
  obtain ⟨w, sm, ty, tr, fresh, ht, _⟩ := emitLeaves_single hr
  have frame := contract.frame "out" false true s sm w lookup tr
  have wm := frame.wires wires
  refine ⟨?_, ?_, ?_⟩
  · intro p hp; rw [ht, emitAssign_wires]; exact frame.decls p hp
  · rw [ht, emitAssign_wires]; exact wm.1
  · intro p hp
    rw [ht, emitAssign_wires] at hp
    have hu := wm.2 p hp
    rw [ht, emitAssign_usedNames, addOutput_state]
    simp [Std.HashSet.contains_insert, hu]

theorem emitLeaves_correct {ctx inputs we mems initial prior s t e cache logProf returned}
    {v : Value} (positive : 0 < v.kind.width)
    (contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      ctx inputs we mems initial e v)
    (h : Inv ctx inputs we mems initial s prior) (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", e)] none 0)
      ctx s returned t) :
    ∃ result, Runs we mems initial t result ∧ result "out" = v.toNat ∧
      "out" ∈ t.module.outputs.map (·.name) ∧ TypedStmts we t.module.finalize.body ∧
      (∀ z, s.usedNames.contains z = true → result z = prior z) := by
  obtain ⟨w, sm, ty, translate, fresh, ht, _⟩ := emitLeaves_single hr
  have wm : ScalarWidthsAgree we sm := by
    intro p hp; apply widths p; rw [ht, emitAssign_wires]; exact hp
  have step := contract.sem "out" false true s sm w prior h wm translate
  obtain ⟨middle, inv, val, frame⟩ := step.execution
  let result := write middle "out" v.toNat
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    apply emitAssign_sound _ we mems initial middle "out" (.ref w) _ ?_ ?_
    · exact runs_of_body_eq rfl inv.runs
    · simpa [evalExpr] using congrArg some val
  · simp [result, write]
  · rw [ht, emitAssign_outputs, addOutput_state]; simp [Module.addOutput]
  · intro st hs
    change st ∈ t.module.body.reverse at hs
    rw [ht, emitAssign_body_cons, List.mem_reverse] at hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst st
      refine ⟨"out", .ref w, v.kind.width, rfl, ?_, Or.inr rfl⟩
      exact step.width ▸ TypedExpr.ref (we := we) w (by rw [step.width]; exact positive)
    · obtain ⟨l, rhs, eq, typed⟩ := inv.typed st hs
      exact ⟨l, rhs, we l, eq, typed, Or.inl rfl⟩
  · intro z hz
    have ne : z ≠ "out" := by
      intro eq; subst z
      have := step.grows "out" hz; simp [fresh] at this
    simpa [result, write, ne] using frame z hz

theorem emitLeaves_from_ports {ctx ρ β mems initial s t e cache logProf returned}
    {v : Value} (positive : 0 < v.kind.width)
    (contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      ctx (inputValues ρ β) (declaredWidths t) mems initial e v)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (wires : WiresOk s) (ports : PortInputs ctx ρ β s initial)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", e)] none 0)
      ctx s returned t) :
    WiresOk t ∧ ∃ result, Runs (declaredWidths t) mems initial t result ∧
      result "out" = v.toNat ∧
      "out" ∈ t.module.outputs.map (·.name) ∧
      TypedStmts (declaredWidths t) t.module.finalize.body ∧
      (∀ z, s.usedNames.contains z = true → result z = initial z) := by
  obtain ⟨growth, finalWires⟩ := emitLeaves_structure contract (lookup_of_ports ports wires) wires hr
  have widths := declaredWidths_agree finalWires
  exact ⟨finalWires, emitLeaves_correct positive contract
    (initial_unified body record (ports.separate wires)
      (ports.inputs wires growth widths)) widths hr⟩

theorem emitLeaves_postReady_at {mems : MEnv} {ctx ρ β initial s t e cache logProf returned}
    {m : Sparkle.IR.AST.Module} {v : Value} (positive : 0 < v.kind.width)
    (contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      ctx (inputValues ρ β) (declaredWidths t) mems initial e v)
    (ordered : ActionOrder (translateExprToWire e "out" false true) ctx (inputValues ρ β)
      (declaredWidths t) mems initial)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (wires : WiresOk s) (ports : PortInputs ctx ρ β s initial)
    (scalar : ScalarWires s) (outputs : s.module.outputs = [])
    (mw : m.wires = t.module.wires.reverse) (mb : m.body = t.module.finalize.body)
    (mo : m.outputs = t.module.outputs.reverse)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", e)] none 0)
      ctx s returned t) :
    weOf m = declaredWidths t ∧ TypedPostReady m ∧ (∀ p ∈ m.outputs, PrintableType p.ty) ∧
      OutputTypedAt v.kind.width (weOf m) m.body ∧
      (∀ p ∈ m.outputs, p.ty.bitWidth = v.kind.width) ∧
      Tools.ShippingSettledSoundness.Acyclic m.body := by
  obtain ⟨unique, result, run, value, out, typed, rest⟩ :=
    emitLeaves_from_ports positive contract body record wires ports hr
  obtain ⟨w, sm, ty, tr, fresh, ht, hty⟩ := emitLeaves_single hr
  have frame := contract.frame "out" false true s sm w (lookup_of_ports ports wires) tr
  have smScalar := frame.scalar scalar
  have smWires := frame.wires wires
  have scalarT : ScalarWires t := by
    intro p hp; rw [ht, emitAssign_wires] at hp; exact smScalar p hp
  have wm : weOf m = declaredWidths t := by
    rw [weOf_eq_moduleWidths (by intro p hp; rw [mw, List.mem_reverse] at hp; exact scalarT p hp)]
    exact moduleWidths_finish mw unique
  have widths : ScalarWidthsAgree (declaredWidths t) sm := by
    intro p hp; apply declaredWidths_agree unique p; rw [ht, emitAssign_wires]; exact hp
  have initialInv := initial_unified (mems := mems) body record (ports.separate wires)
    (ports.inputs wires (by intro p hp; rw [ht, emitAssign_wires]; exact frame.decls p hp)
      (declaredWidths_agree unique))
  have step := contract.sem "out" false true s sm w initial initialInv widths tr
  have width : declaredWidths sm w = v.kind.width := by
    have eq : declaredWidths t = declaredWidths sm := by
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths
      rw [ht, emitAssign_wires]; rfl
    rw [eq] at step
    exact step.width
  have tyWidth : ty.bitWidth = v.kind.width := by
    rw [hty]; unfold leafOutputType
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths at width
    cases hf : sm.module.wires.find? (fun p => p.name == w) with
    | none => simp [hf] at width; omega
    | some p => simpa [hf] using width
  have noOut : "out" ∉ m.wires.map (·.name) := by
    intro hmem
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp hmem
    rw [mw, List.mem_reverse, ht, emitAssign_wires] at hp
    have used := smWires.2 p hp
    rw [eq, fresh] at used
    cases used
  have mo' : m.outputs = [{name := "out", ty := ty}] := by
    rw [mo, ht, emitAssign_outputs, addOutput_state]
    simp [Module.addOutput, frame.outputs, outputs]
  refine ⟨wm, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [mw, List.map_reverse]; exact nodup_reverse unique.1
  · unfold weOf
    have none : m.wires.find? (fun p => p.name == "out") = none := by
      apply List.find?_eq_none.mpr
      intro p hp
      simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
      intro eq
      exact noOut (List.mem_map.mpr ⟨p, hp, eq⟩)
    rw [none]
  · unfold Sparkle.IR.Optimize.buildWidthMap
    rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" noOut, mo']
    simp [tyWidth, Nat.ne_of_gt positive]
  · rw [wm, mb]; exact typed
  · have printTy : PrintableType ty := by
      rw [hty]
      unfold leafOutputType
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths at width
      cases hf : sm.module.wires.find? (fun p => p.name == w) with
      | none => simp [hf] at width; omega
      | some p =>
        simp only [hf, Option.map_some, Option.getD_some] at width
        change PrintableType p.ty
        rcases smScalar p (List.mem_of_find?_eq_some hf) with bit | ⟨k, bits⟩
        · rw [bit]; exact .bit
        · rw [bits] at width ⊢
          exact .bits k (by change k = v.kind.width at width; omega)
    intro p hp
    rw [mo', List.mem_singleton] at hp
    subst p
    exact printTy
  · intro rhs hs
    rw [mb] at hs
    change Stmt.assign "out" rhs ∈ t.module.body.reverse at hs
    rw [List.mem_reverse, ht, emitAssign_body_cons] at hs
    rcases List.mem_cons.mp hs with eq | hs
    · cases eq
      rw [wm, ← step.width]
      exact .ref w (by rw [step.width]; exact positive)
    · obtain ⟨result, inv, _⟩ := step.execution
      obtain ⟨l, r, eq, rhsTyped⟩ := inv.typed _ hs
      cases eq
      have pos := rhsTyped.positive
      have zero : declaredWidths t "out" = 0 := by
        unfold Tools.ShippingMixedOutputSoundness.declaredWidths
        rw [ht, emitAssign_wires]
        have none : sm.module.wires.find? (fun p => p.name == "out") = none := by
          apply List.find?_eq_none.mpr
          intro p hp he
          have eq : p.name = "out" := by simpa using he
          have used := smWires.2 p hp
          rw [eq, fresh] at used; cases used
        change ((sm.module.wires.find? (fun p => p.name == "out")).map
          (fun p => p.ty.bitWidth)).getD 0 = 0
        simp [none]
      rw [zero] at pos; omega
  · intro p hp
    rw [mo', List.mem_singleton] at hp
    subst p; exact tyWidth
  · have order := ordered s sm w initial tr initialInv widths
      (Tools.ShippingTranslationOrder.OrderInv.empty body)
    have pending : "out" ∉ Tools.ShippingTranslationOrder.footprint sm.module.body.reverse := by
      intro hs
      have used := order.2 "out" ((Tools.ShippingTranslationOrder.footprint_reverse_mem _ _).mp hs)
      rw [fresh] at used; cases used
    have ne : w ≠ "out" := by
      intro eq
      have used := step.used
      rw [eq, fresh] at used; cases used
    rw [mb]
    change Tools.ShippingSettledSoundness.Acyclic t.module.body.reverse
    rw [ht, emitAssign_body_cons, List.reverse_cons]
    exact Tools.ShippingTranslationOrder.acyclic_snoc order.1 pending
      (by simpa [Sparkle.IR.Reorder.refsOf] using Ne.symm ne)

end Tools.ShippingUnifiedEntrySoundness
