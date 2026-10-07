import Tools.ShippingMixedRecursion
import Tools.ShippingTypedPostSoundness

/-! Connect the closed mixed translator to the real single-leaf output emitter.
This is an entry boundary theorem: input binding facts and final width agreement
remain explicit, rather than assuming a recursive translation oracle. -/
namespace Tools.ShippingMixedOutputSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedRecursion Tools.ShippingCompareLoweringSoundness
open Tools.ShippingMixedLiteralSoundness Tools.ShippingMixedBinarySoundness
open Tools.ShippingBindingsSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingEntrySoundness
open Tools.ShippingBuilderSoundness Tools.ShippingScalarSoundness

/-- At the first leaf there is no emitted code or cache record. These two
parts of the invariant are discharged; only input facts and separation remain. -/
theorem initial_mixed {ctx ρ β we mems initial s}
    (body : s.module.body = []) (record : s.translateRecord = {})
    (separate : Separate ρ β) (inputs : Inputs ctx ρ β we s initial) :
    MixedInv ctx ρ β we mems initial s initial := by
  refine ⟨separate, ?_, inputs, ⟨?_, ?_⟩, ?_⟩
  · simp [Runs, Module.finalize, body, evalAssigns]
  · intro w e he b hd; rw [record] at he; simp at he
  · intro w e he n x hd; rw [record] at he; simp at he
  · intro st hs; rw [body] at hs; cases hs

/-- A real `emitLeaves` run drives `out` with the quoted source's Bool value.
It also produces the typed statement property used by mixed postprocessing. -/
theorem emitLeaves_bool_correct {ctx ρ β we mems initial prior s t dom n kb kv cache logProf returned}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (h : MixedInv ctx ρ β we mems initial s prior) (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0)
      ctx s returned t) :
    ∃ result, Runs we mems initial t result ∧ result "out" = encodeBool (evalB n bools bits e) ∧
      "out" ∈ t.module.outputs.map (·.name) ∧ TypedStmts we t.module.finalize.body ∧
      (∀ z, s.usedNames.contains z = true → result z = prior z) := by
  obtain ⟨w, sm, ty, translate, fresh, ht, _⟩ := emitLeaves_single hr
  have wm : ScalarWidthsAgree we sm := by
    intro p hp; apply widths p; rw [ht, emitAssign_wires]; exact hp
  have contract := translateExprToWire_bool_contract (ctx := ctx) (we := we) (mems := mems)
    (initial := initial) (dom := dom) hn hb hv e he
  have step := contract.sem "out" false true s sm w prior h wm translate
  obtain ⟨middle, inv, value, frame⟩ := step.execution
  let result := write middle "out" (encodeBool (evalB n bools bits e))
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    apply emitAssign_sound _ we mems initial middle "out" (.ref w) _ ?_ ?_
    · exact runs_of_body_eq rfl inv.runs
    · simpa [evalExpr] using congrArg some value
  · simp [result, write]
  · rw [ht, emitAssign_outputs, addOutput_state]; simp [Module.addOutput]
  · intro st hs
    change st ∈ t.module.body.reverse at hs
    rw [ht, emitAssign_body_cons, List.mem_reverse] at hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst st
      refine ⟨"out", .ref w, 1, rfl, ?_, Or.inr rfl⟩
      exact step.width_eq ▸ TypedExpr.ref (we := we) w (by rw [step.width_eq]; decide)
    · obtain ⟨l, rhs, eq, typed⟩ := inv.typed st hs
      exact ⟨l, rhs, we l, eq, typed, Or.inl rfl⟩
  · intro z hz
    have ne : z ≠ "out" := by
      intro eq; subst z
      have := step.grows "out" hz; simp [fresh] at this
    simpa [result, write, ne] using frame z hz

/-- First-leaf specialization: no initial execution/record/typed-body premises
are needed once the actual input stage's empty-body and binding facts are known. -/
theorem emitLeaves_bool_from_inputs {ctx ρ β we mems initial s t dom n kb kv cache logProf returned}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (separate : Separate ρ β) (inputs : Inputs ctx ρ β we s initial)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0)
      ctx s returned t) :
    ∃ result, Runs we mems initial t result ∧ result "out" = encodeBool (evalB n bools bits e) ∧
      "out" ∈ t.module.outputs.map (·.name) ∧ TypedStmts we t.module.finalize.body ∧
      (∀ z, s.usedNames.contains z = true → result z = initial z) :=
  emitLeaves_bool_correct hn hb hv e he (initial_mixed body record separate inputs) widths hr

/-- Widths read directly from the actual state's declarations. -/
def declaredWidths (s : CircuitState) : WEnv := fun w =>
  ((s.module.wires.find? (fun p => p.name == w)).map (fun p => p.ty.bitWidth)).getD 0

theorem declaredWidths_agree {s} (h : WiresOk s) : ScalarWidthsAgree (declaredWidths s) s := by
  intro p hp
  unfold declaredWidths
  rw [find?_of_nodup h.1 hp]
  rfl

/-- Facts provided by input allocation, before an execution-width environment
is chosen. Types are actual declarations, not a type-inference oracle. -/
structure PortInputs (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (s : CircuitState) (initial : Env) : Prop where
  bool : ∀ id b, ρ id = some b → ∃ w, visible ctx s.sourceBindings id = some w ∧
    ({name := w, ty := .bit} : Port) ∈ s.module.wires ∧ initial w = encodeBool b
  bits : ∀ id n (x : BitVec n), β id = some ⟨n, x⟩ → ∃ w,
    visible ctx s.sourceBindings id = some w ∧
    ({name := w, ty := .bitVector n} : Port) ∈ s.module.wires ∧ initial w = x.toNat

theorem PortInputs.lookup {ctx ρ β s initial} (h : PortInputs ctx ρ β s initial)
    (hw : WiresOk s) : Lookup ctx ρ β s := by
  constructor
  · intro id b hi
    obtain ⟨w, bound, decl, _⟩ := h.bool id b hi
    exact ⟨w, bound, hw.2 _ decl⟩
  · intro id n x hi
    obtain ⟨w, bound, decl, _⟩ := h.bits id n x hi
    exact ⟨w, bound, hw.2 _ decl⟩

theorem PortInputs.separate {ctx ρ β s initial} (h : PortInputs ctx ρ β s initial)
    (hw : WiresOk s) : Separate ρ β := by
  intro id b hi
  cases hv : β id with
  | none => rfl
  | some value =>
    obtain ⟨n, x⟩ := value
    obtain ⟨bw, bb, bd, _⟩ := h.bool id b hi
    obtain ⟨vw, vb, vd, _⟩ := h.bits id n x hv
    have eq : bw = vw := Option.some.inj (bb.symm.trans vb)
    subst vw
    have hb := find?_of_nodup hw.1 bd
    have hv := find?_of_nodup hw.1 vd
    rw [hb] at hv
    cases hv

theorem PortInputs.inputs {ctx ρ β s t initial we} (h : PortInputs ctx ρ β s initial)
    (hw : WiresOk s) (growth : DeclGrows s t) (widths : ScalarWidthsAgree we t) :
    Inputs ctx ρ β we s initial := by
  refine ⟨?_, (h.lookup hw).bits, ?_⟩
  · intro id b hi
    obtain ⟨w, bound, decl, val⟩ := h.bool id b hi
    exact ⟨w, bound, hw.2 _ decl, val, widths _ (growth _ decl)⟩
  · intro id n x w hi bound
    obtain ⟨v, bv, decl, val⟩ := h.bits id n x hi
    have eq : v = w := Option.some.inj (bv.symm.trans bound)
    subst v
    exact ⟨val, widths _ (growth _ decl)⟩

/-- The actual leaf emitter preserves declaration uniqueness. Its output port
reserves a name but does not add a second internal wire declaration. -/
theorem emitLeaves_structure {rec ctx ρ β we mems initial s t e n v cache logProf returned}
    (contract : Contract rec ctx ρ β we mems initial e n v)
    (lookup : Lookup ctx ρ β s) (wires : WiresOk s)
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

/-- Closed translation and actual output emission, with widths and valuation
separation derived from declarations. The remaining entry premise is the real
input allocation's port layout, plus its empty body and record. -/
theorem emitLeaves_bool_from_ports {ctx ρ β mems initial s t dom n kb kv cache logProf returned}
    {binp vinp : Nat → FVarId} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (wires : WiresOk s) (ports : PortInputs ctx ρ β s initial)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0)
      ctx s returned t) :
    WiresOk t ∧ ∃ result, Runs (declaredWidths t) mems initial t result ∧
      result "out" = encodeBool (evalB n bools bits e) ∧
      "out" ∈ t.module.outputs.map (·.name) ∧ TypedStmts (declaredWidths t) t.module.finalize.body ∧
      (∀ z, s.usedNames.contains z = true → result z = initial z) := by
  have contract := translateExprToWire_bool_contract (ctx := ctx) (we := declaredWidths t)
    (mems := mems) (initial := initial) (dom := dom) hn hb hv e he
  obtain ⟨growth, finalWires⟩ := emitLeaves_structure contract (ports.lookup wires) wires hr
  have widths := declaredWidths_agree finalWires
  exact ⟨finalWires, emitLeaves_bool_from_inputs hn hb hv e he body record (ports.separate wires)
    (ports.inputs wires growth widths) widths hr⟩

/-- Library Signal observations, rather than only the reflected evaluator.
The chosen observation time is a source time, not an RTL delta round. -/
theorem emitLeaves_bool_signal {ctx ρ β mems initial s t dom n kb kv cache logProf returned}
    {D : Sparkle.Core.Domain.DomainConfig} {tick : Nat}
    {binp vinp : Nat → FVarId}
    {bools : Nat → Sparkle.Core.Signal.Signal D Bool}
    {bits : Nat → Sparkle.Core.Signal.Signal D (BitVec n)}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some ((bools j).val tick))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, (bits j).val tick⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (wires : WiresOk s) (ports : PortInputs ctx ρ β s initial)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0)
      ctx s returned t) :
    ∃ result, Runs (declaredWidths t) mems initial t result ∧
      result "out" = encodeBool ((denoteB n bools bits e).val tick) := by
  obtain ⟨_, result, run, value, _⟩ := emitLeaves_bool_from_ports hn hb hv e he body record wires ports hr
  exact ⟨result, run, by rw [denoteB_val]; exact value⟩

end Tools.ShippingMixedOutputSoundness
