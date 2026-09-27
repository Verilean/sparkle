import Tools.ShippingMixedInputSoundness
import Tools.ShippingMixedOrderSoundness

/-! The shipping mixed entry's complete input walk. Preparation below is a
pure description of the states reached by the actual bindMixedCertifiedInputs;
prepare_returns connects every successful run to that state, not a replacement
compiler or a replay hypothesis. -/
namespace Tools.ShippingMixedEntrySoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedOutputSoundness Tools.ShippingMixedInputSoundness
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMixedBinarySoundness Tools.ShippingMixedRecursion Tools.ShippingTypedPostSoundness
open Tools.ShippingPostSoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness

structure Setup where
  context : CompilerState
  state : CircuitState
  bools : BoolValuation
  bits : Valuation

def extend (a : Setup) (binder : (Name × MixedGateBinder) × FVarId)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) : Setup :=
  let ((name, kind), id) := binder
  match kind with
  | .domain => a
  | .bool =>
    { context := inputContext a.context id (inputWire a.state name.toString .bit)
      state := inputState a.state name.toString .bit
      bools := fun key => if key = id then some (bools id) else a.bools key
      bits := fun key => if key = id then none else a.bits key }
  | .bits n =>
    { context := inputContext a.context id (inputWire a.state name.toString (.bitVector n))
      state := inputState a.state name.toString (.bitVector n)
      bools := fun key => if key = id then none else a.bools key
      bits := fun key => if key = id then some ⟨n, bits id n⟩ else a.bits key }

def prepare (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    List ((Name × MixedGateBinder) × FVarId) → Setup → Setup
  | [], a => a
  | b :: rest, a => prepare bools bits rest (extend a b bools bits)

/-- The source value at one allocated RTL input port. -/
def InputValue (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (a : Setup) (binder : (Name × MixedGateBinder) × FVarId) : Prop :=
  match binder.1.2 with
  | .domain => True
  | .bool => initial (inputWire a.state binder.1.1.toString .bit) = encodeBool (bools binder.2)
  | .bits n => initial (inputWire a.state binder.1.1.toString (.bitVector n)) = (bits binder.2 n).toNat

/-- Ordinary admissibility of source input values at their allocated RTL ports. -/
def Admissible (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) : List ((Name × MixedGateBinder) × FVarId) → Setup → Prop
  | [], _ => True
  | b :: rest, a => InputValue bools bits initial a b ∧
    Admissible bools bits initial rest (extend a b bools bits)

theorem restrict_ports {ctx ρ β ρ' β' s initial} (h : PortInputs ctx ρ β s initial)
    (hb : ∀ id b, ρ' id = some b → ρ id = some b)
    (hv : ∀ id n (x : BitVec n), β' id = some ⟨n, x⟩ → β id = some ⟨n, x⟩) :
    PortInputs ctx ρ' β' s initial :=
  ⟨fun id b hi => h.bool id b (hb id b hi), fun id n x hi => h.bits id n x (hv id n x hi)⟩

theorem extend_layout {a : Setup} {binder bools bits initial}
    (ports : PortInputs a.context a.bools a.bits a.state initial)
    (wires : WiresOk a.state)
    (value : match binder.1.2 with
      | .domain => True
      | .bool => initial (inputWire a.state binder.1.1.toString .bit) = encodeBool (bools binder.2)
      | .bits n => initial (inputWire a.state binder.1.1.toString (.bitVector n)) = (bits binder.2 n).toNat) :
    let next := extend a binder bools bits
    PortInputs next.context next.bools next.bits next.state initial ∧ WiresOk next.state ∧
      next.state.module.body = a.state.module.body ∧ next.state.translateRecord = a.state.translateRecord := by
  obtain ⟨⟨name, kind⟩, id⟩ := binder
  cases kind with
  | domain => exact ⟨ports, wires, rfl, rfl⟩
  | bool =>
    have restricted : PortInputs a.context a.bools
        (fun key => if key = id then none else a.bits key) a.state initial := by
      apply restrict_ports ports (fun _ _ h => h)
      intro key n x hi
      split at hi
      · cases hi
      · exact hi
    exact ⟨bind_bool_layout (id := id) (β := fun key => if key = id then none else a.bits key) restricted (if_pos rfl) value, input_wiresOk wires,
      input_body _ _ _, input_record _ _ _⟩
  | bits n =>
    have restricted : PortInputs a.context (fun key => if key = id then none else a.bools key)
        a.bits a.state initial := by
      apply restrict_ports ports ?_ (fun _ _ _ h => h)
      intro key b hi
      split at hi
      · cases hi
      · exact hi
    exact ⟨bind_bits_layout (id := id) (ρ := fun key => if key = id then none else a.bools key) _ restricted (if_pos rfl) value, input_wiresOk wires,
      input_body _ _ _, input_record _ _ _⟩

theorem prepare_layout {bools bits initial} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) (ports : PortInputs a.context a.bools a.bits a.state initial)
    (wires : WiresOk a.state) (values : Admissible bools bits initial L a) :
    let final := prepare bools bits L a
    PortInputs final.context final.bools final.bits final.state initial ∧ WiresOk final.state ∧
      final.state.module.body = a.state.module.body ∧ final.state.translateRecord = a.state.translateRecord := by
  induction L generalizing a with
  | nil => exact ⟨ports, wires, rfl, rfl⟩
  | cons binder rest ih =>
    obtain ⟨value, values⟩ := values
    obtain ⟨ports', wires', body, record⟩ := extend_layout (binder := binder) (bools := bools) (bits := bits) ports wires value
    obtain ⟨ports'', wires'', body', record'⟩ := ih _ ports' wires' values
    exact ⟨ports'', wires'', body'.trans body, record'.trans record⟩

theorem input_scalar {s name ty} (hs : ScalarWires s)
    (ht : ty = .bit ∨ ∃ n, ty = .bitVector n) : ScalarWires (inputState s name ty) := by
  intro p hp
  rw [input_wires] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ht
  · exact hs p hp

theorem input_outputs (s : CircuitState) (name : String) (ty : Sparkle.IR.Type.HWType) :
    (inputState s name ty).module.outputs = s.module.outputs := by
  change (CircuitM.makeWire name ty true s).2.module.outputs = _
  exact makeWire_outputs _ _ _ _

theorem prepare_shape {bools bits} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) (hs : ScalarWires a.state) :
    ScalarWires (prepare bools bits L a).state ∧
      (prepare bools bits L a).state.module.outputs = a.state.module.outputs := by
  induction L generalizing a with
  | nil => exact ⟨hs, rfl⟩
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih a hs
    | bool =>
      have h := ih (extend a ((name, .bool), id) bools bits) (input_scalar hs (Or.inl rfl))
      exact ⟨h.1, h.2.trans (input_outputs _ _ _)⟩
    | bits n =>
      have h := ih (extend a ((name, .bits n), id) bools bits) (input_scalar hs (Or.inr ⟨n, rfl⟩))
      exact ⟨h.1, h.2.trans (input_outputs _ _ _)⟩

/-- Every physical input, including unused source arguments, is bounded and
has the same declaration in the internal width environment. -/
def InputBounds (s : CircuitState) (initial : Env) : Prop :=
  ∀ p ∈ s.module.inputs, p ∈ s.module.wires ∧ initial p.name < 2 ^ p.ty.bitWidth

theorem input_bounds {s initial name ty value}
    (h : InputBounds s initial) (hv : initial (inputWire s name ty) = value)
    (bound : value < 2 ^ ty.bitWidth) : InputBounds (inputState s name ty) initial := by
  intro p hp
  change p ∈ {name := inputWire s name ty, ty := ty} :: (CircuitM.makeWire name ty true s).2.module.inputs at hp
  rw [makeWire_inputs] at hp
  rw [input_wires]
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨List.mem_cons_self, by simpa [hv] using bound⟩
  · obtain ⟨decl, bound⟩ := h p hp
    exact ⟨List.mem_cons_of_mem _ decl, bound⟩

theorem prepare_inputBounds {bools bits initial} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) (h : InputBounds a.state initial) (values : Admissible bools bits initial L a) :
    InputBounds (prepare bools bits L a).state initial := by
  induction L generalizing a with
  | nil => exact h
  | cons binder rest ih =>
    obtain ⟨value, values⟩ := values
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    apply ih _ ?_ values
    cases kind with
    | domain => exact h
    | bool =>
      apply input_bounds h value
      cases bools id <;> decide
    | bits n =>
      exact input_bounds h value (bits id n).isLt

def PositiveBinders (bs : List (Name × MixedGateBinder)) : Prop :=
  ∀ name n, (name, .bits n) ∈ bs → 0 < n

theorem input_print {a : Setup} {name ty}
    (hi : ∀ p ∈ a.state.module.inputs, PrintableType p.ty) (pt : PrintableType ty) :
    (∀ p ∈ (inputState a.state name ty).module.inputs, PrintableType p.ty) ∧
    (inputState a.state name ty).module.parameters = a.state.module.parameters ∧
    (inputState a.state name ty).module.isPrimitive = a.state.module.isPrimitive := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    change p ∈ {name := inputWire a.state name ty, ty := ty} ::
      (CircuitM.makeWire name ty true a.state).2.module.inputs at hp
    rw [makeWire_inputs] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact pt
    · exact hi p hp
  · change (CircuitM.makeWire name ty true a.state).2.module.parameters = _
    rw [makeWire_module]; rfl
  · change (CircuitM.makeWire name ty true a.state).2.module.isPrimitive = _
    rw [makeWire_module]; rfl

/-- Scalar inputs are printable, and binding introduces no module metadata. -/
theorem prepare_print {bools bits} (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup)
    (hi : ∀ p ∈ a.state.module.inputs, PrintableType p.ty)
    (positive : ∀ name n id, ((name, .bits n), id) ∈ L → 0 < n) :
    (∀ p ∈ (prepare bools bits L a).state.module.inputs, PrintableType p.ty) ∧
    (prepare bools bits L a).state.module.parameters = a.state.module.parameters ∧
    (prepare bools bits L a).state.module.isPrimitive = a.state.module.isPrimitive := by
  induction L generalizing a with
  | nil => exact ⟨hi, rfl, rfl⟩
  | cons binder rest ih =>
    have tail := fun name n id mem => positive name n id (List.mem_cons_of_mem _ mem)
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih a hi tail
    | bool =>
      have inp := input_print (name := name.toString) hi PrintableType.bit
      have next := ih (extend a ((name, .bool), id) bools bits) inp.1 tail
      exact ⟨next.1, next.2.1.trans inp.2.1, next.2.2.trans inp.2.2⟩
    | bits n =>
      have inp := input_print (name := name.toString) hi (PrintableType.bits n (positive name n id List.mem_cons_self))
      have next := ih (extend a ((name, .bits n), id) bools bits) inp.1 tail
      exact ⟨next.1, next.2.1.trans inp.2.1, next.2.2.trans inp.2.2⟩

/-- Every successful execution of the actual input walk reaches `prepare`.
There are no binder-type inference or handler-correctness premises. -/
theorem prepare_returns {α : Type} {bools bits} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) {k : CompilerM α} {result : α} {t : CircuitState}
    (hr : Returns (bindMixedCertifiedInputs k L) a.context a.state result t) :
    Returns k (prepare bools bits L a).context (prepare bools bits L a).state result t := by
  induction L generalizing a with
  | nil => exact hr
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih a hr
    | bool => exact ih (extend a ((name, .bool), id) bools bits) (bindInputPort_returns hr)
    | bits n => exact ih (extend a ((name, .bits n), id) bools bits) (bindInputPort_returns hr)

/-- The entire real binder walk and output emitter, not just one input node.
Quotation/source-value facts remain explicit until the declaration bridge. -/
theorem bindMixed_emitLeaves_sound {bools bits initial mems ctx s t dom n kb kv cache logProf returned}
    (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup)
    (haCtx : a.context = ctx) (haState : a.state = s)
    {binp vinp : Nat → FVarId} {bvals : Nat → Bool} {vvals : Nat → BitVec n}
    (hn : 0 < n)
    (hb : ∀ j, j < kb → (prepare bools bits L a).bools (binp j) = some (bvals j))
    (hv : ∀ j, j < kv → (prepare bools bits L a).bits (vinp j) = some ⟨n, vvals j⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (ports : PortInputs a.context a.bools a.bits a.state initial)
    (wires : WiresOk a.state) (body : a.state.module.body = []) (record : a.state.translateRecord = {})
    (values : Admissible bools bits initial L a)
    (hr : Returns (bindMixedCertifiedInputs
      (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
        [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0) L)
      ctx s returned t) :
    ∃ result, Runs (declaredWidths t) mems initial t result ∧
      result "out" = encodeBool (evalB n bvals vvals e) := by
  rw [← haCtx, ← haState] at hr
  have leaf := prepare_returns L a (bools := bools) (bits := bits) hr
  obtain ⟨p, w, b, r⟩ := prepare_layout L a ports wires values
  obtain ⟨_, result, run, val, _⟩ := emitLeaves_bool_from_ports hn hb hv e he
    (b.trans body) (r.trans record) w p leaf
  exact ⟨result, run, val⟩

/-- Widths read from the actual returned module, including scalar Bool wires. -/
def moduleWidths (m : Sparkle.IR.AST.Module) : WEnv := fun w =>
  ((m.wires.find? (fun p => p.name == w)).map (fun p => p.ty.bitWidth)).getD 0

theorem moduleWidths_finish {m : Sparkle.IR.AST.Module} {s : CircuitState}
    (wires : m.wires = s.module.wires.reverse) (unique : WiresOk s) :
    moduleWidths m = declaredWidths s := by
  funext w
  have eq : m.wires.find? (fun p => p.name == w) = s.module.wires.find? (fun p => p.name == w) := by
    cases hf : s.module.wires.find? (fun p => p.name == w) with
    | none =>
      apply List.find?_eq_none.mpr
      intro p hp
      rw [wires, List.mem_reverse] at hp
      exact List.find?_eq_none.mp hf p hp
    | some p =>
      have hp := List.mem_of_find?_eq_some hf
      have pname : p.name = w := by simpa using List.find?_some hf
      have nd : (m.wires.map (·.name)).Nodup := by
        rw [wires, List.map_reverse]; exact nodup_reverse unique.1
      have hp' : p ∈ m.wires := by rw [wires, List.mem_reverse]; exact hp
      simpa [pname] using find?_of_nodup nd hp'
  unfold moduleWidths declaredWidths
  rw [eq]

theorem weOf_eq_moduleWidths {m : Sparkle.IR.AST.Module}
    (hs : ∀ p ∈ m.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n) :
    weOf m = moduleWidths m := by
  funext w
  unfold weOf moduleWidths
  cases hf : m.wires.find? (fun p => p.name == w) with
  | none => rfl
  | some p =>
    rcases hs p (List.mem_of_find?_eq_some hf) with ht | ⟨n, ht⟩
    · cases p; simp_all [Sparkle.IR.Type.HWType.bitWidth]
    · cases p; simp_all [Sparkle.IR.Type.HWType.bitWidth]

/-- Derive the cleanup preconditions from the real leaf emission, rather than
requiring a readiness certificate for the compiled module. -/
theorem emitLeaves_postReady {mems : MEnv} {ctx ρ β initial s t dom n kb kv cache logProf returned}
    {m : Sparkle.IR.AST.Module} {binp vinp : Nat → FVarId}
    {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hn : 0 < n) (hb : ∀ j, j < kb → ρ (binp j) = some (bools j))
    (hv : ∀ j, j < kv → β (vinp j) = some ⟨n, bits j⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (body : s.module.body = []) (record : s.translateRecord = {})
    (wires : WiresOk s) (ports : PortInputs ctx ρ β s initial)
    (scalar : ScalarWires s) (outputs : s.module.outputs = [])
    (mw : m.wires = t.module.wires.reverse) (mb : m.body = t.module.finalize.body)
    (mo : m.outputs = t.module.outputs.reverse)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0)
      ctx s returned t) :
    weOf m = declaredWidths t ∧ TypedPostReady m ∧ (∀ p ∈ m.outputs, PrintableType p.ty) ∧
      OutputTyped (weOf m) m.body ∧ (∀ p ∈ m.outputs, p.ty.bitWidth = 1) ∧
      Tools.ShippingSettledSoundness.Acyclic m.body := by
  have contract := translateExprToWire_bool_contract (ctx := ctx) (we := declaredWidths t)
    (mems := mems) (initial := initial) (dom := dom) hn hb hv e he
  obtain ⟨unique, result, run, value, out, typed, rest⟩ := emitLeaves_bool_from_ports (mems := mems) hn hb hv e he body record wires ports hr
  obtain ⟨w, sm, ty, tr, fresh, ht, hty⟩ := emitLeaves_single hr
  have frame := contract.frame "out" false true s sm w (ports.lookup wires) tr
  have smScalar := frame.scalar scalar
  have smWires := frame.wires wires
  have scalarT : ScalarWires t := by
    intro p hp; rw [ht, emitAssign_wires] at hp; exact smScalar p hp
  have wm : weOf m = declaredWidths t := by
    rw [weOf_eq_moduleWidths (by intro p hp; rw [mw, List.mem_reverse] at hp; exact scalarT p hp)]
    exact moduleWidths_finish mw unique
  have widths : ScalarWidthsAgree (declaredWidths t) sm := by
    intro p hp; apply declaredWidths_agree unique p; rw [ht, emitAssign_wires]; exact hp
  have initialInv := initial_mixed (mems := mems) body record (ports.separate wires)
    (ports.inputs wires (by intro p hp; rw [ht, emitAssign_wires]; exact frame.decls p hp)
      (declaredWidths_agree unique))
  have step := contract.sem "out" false true s sm w initial initialInv widths tr
  have width : declaredWidths sm w = 1 := by
    have eq : declaredWidths t = declaredWidths sm := by unfold declaredWidths; rw [ht, emitAssign_wires]; rfl
    rw [eq] at step
    exact step.width_eq
  have tyWidth : ty.bitWidth = 1 := by
    rw [hty]; unfold leafOutputType
    unfold declaredWidths at width
    cases hf : sm.module.wires.find? (fun p => p.name == w) with
    | none => simp [hf] at width
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
    rw [wmFold_notin m.wires _ "out" noOut, mo']
    simp [tyWidth]
  · rw [wm, mb]; exact typed
  · have printTy : PrintableType ty := by
      rw [hty]
      unfold leafOutputType
      unfold declaredWidths at width
      cases hf : sm.module.wires.find? (fun p => p.name == w) with
      | none => simp [hf] at width
      | some p =>
        simp only [hf, Option.map_some, Option.getD_some] at width
        change PrintableType p.ty
        rcases smScalar p (List.mem_of_find?_eq_some hf) with bit | ⟨k, bits⟩
        · rw [bit]; exact .bit
        · rw [bits] at width ⊢
          exact .bits k (by change k = 1 at width; omega)
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
      rw [wm, ← step.width_eq]
      exact .ref w (by rw [step.width_eq]; decide)
    · obtain ⟨result, inv, _⟩ := step.execution
      obtain ⟨l, r, eq, rhsTyped⟩ := inv.typed _ hs
      cases eq
      have pos := rhsTyped.positive
      have zero : declaredWidths t "out" = 0 := by
        unfold declaredWidths
        rw [ht, emitAssign_wires]
        have none : sm.module.wires.find? (fun p => p.name == "out") = none := by
          apply List.find?_eq_none.mpr
          intro p hp he
          have eq : p.name = "out" := by simpa using he
          have used := smWires.2 p hp
          rw [eq, fresh] at used; cases used
        change ((sm.module.wires.find? (fun p => p.name == "out")).map (fun p => p.ty.bitWidth)).getD 0 = 0
        simp [none]
      rw [zero] at pos; omega
  · intro p hp
    rw [mo', List.mem_singleton] at hp
    subst p; exact tyWidth
  · have order := Tools.ShippingMixedOrderSoundness.translateExprToWire_bool_orders
      hn hb hv e he "out" true s sm w initial tr initialInv widths
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

/-- No inferred-type premise: this decomposes the actual mixed synthesis run. -/
theorem synthesizeMixedCertified_returns {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body) (m, d)) :
    ∃ ids cache returned st, ids.Nodup ∧ ids.length = bs.length ∧
      Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init declName.toString) returned st ∧
      m = (addClockResetIfSequential st.module).finalize ∧ d = st.design ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true := by
  unfold synthesizeMixedCertified at hr
  obtain ⟨ids, _, hr⟩ := MReturns.bind hr
  split at hr
  rotate_left
  · exact (MReturns.throw hr).elim
  rename_i hids
  dsimp only at hr
  obtain ⟨cache, _, hr⟩ := MReturns.bind hr
  obtain ⟨⟨returned, st⟩, run, finish⟩ := MReturns.bind hr
  obtain ⟨hm, hd, name⟩ := finishSynth_returns finish
  exact ⟨ids, cache, returned, st, hids.1, hids.2, MReturns.run run, hm, hd, name⟩

def start (ctx : CompilerState) (name : String) : Setup :=
  ⟨ctx, CircuitM.init name, fun _ => none, fun _ => none⟩

/-- Relational source preservation for the actual mixed entry. As in the old
entry theorem, source meaning is supplied on the instantiated declaration;
it is not a hypothesis about correctness of a compiler subroutine. -/
def MixedSourcePreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (observes : Env → MEnv → Nat → Prop) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    ∀ (dom : Lean.Expr) (n kb kv : Nat) (binp vinp : Nat → FVarId)
      (bvals : Nat → Bool) (vvals : Nat → BitVec n) (e : BExpr),
    0 < n → e.WF kb kv n →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨n, vvals j⟩) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e →
    observes initial mems (encodeBool (evalB n bvals vvals e))

/-- Input allocation maintains a sublist of declared wires, including unused
arguments; names come from the actual fresh-name allocator. -/
theorem input_declarations {s name ty}
    (sub : s.module.inputs.Sublist s.module.wires)
    (names : ∀ p ∈ s.module.wires, Sparkle.IR.NameHints.Allocated p.name) :
    (inputState s name ty).module.inputs.Sublist (inputState s name ty).module.wires ∧
      (∀ p ∈ (inputState s name ty).module.wires, Sparkle.IR.NameHints.Allocated p.name) := by
  constructor
  · rw [input_wires]
    change (_ :: (CircuitM.makeWire name ty true s).2.module.inputs).Sublist (_ :: s.module.wires)
    rw [makeWire_inputs]
    exact sub.cons_cons _
  · intro p hp
    rw [input_wires] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact CircuitM.makeWire_allocated name ty true s
    · exact names p hp

theorem prepare_declarations {bools bits} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) (sub : a.state.module.inputs.Sublist a.state.module.wires)
    (names : ∀ p ∈ a.state.module.wires, Sparkle.IR.NameHints.Allocated p.name) :
    (prepare bools bits L a).state.module.inputs.Sublist (prepare bools bits L a).state.module.wires ∧
      (∀ p ∈ (prepare bools bits L a).state.module.wires, Sparkle.IR.NameHints.Allocated p.name) := by
  induction L generalizing a with
  | nil => exact ⟨sub, names⟩
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih a sub names
    | bool =>
      have h := input_declarations (name := name.toString) (ty := .bit) sub names
      exact ih (extend a ((name, .bool), id) bools bits) h.1 h.2
    | bits n =>
      have h := input_declarations (name := name.toString) (ty := .bitVector n) sub names
      exact ih (extend a ((name, .bits n), id) bools bits) h.1 h.2

/-- Metadata before zero-width cleanup. Internal zero-width declarations may
still be present; input/output declarations are already printable. -/
structure PrintBaseAt (outWidth : Nat) (m : Sparkle.IR.AST.Module) : Prop where
  primitive : m.isPrimitive = false
  parameters : m.parameters = []
  inputs : ∀ p ∈ m.inputs, PrintableType p.ty
  outputs : ∀ p ∈ m.outputs, PrintableType p.ty
  wires : ∀ p ∈ m.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n
  wireNames : ∀ p ∈ m.wires, Sparkle.IR.NameHints.Allocated p.name
  inputNames : (m.inputs.map Port.name).Nodup
  inputWires : ∀ p ∈ m.inputs, p ∈ m.wires
  output : ∃ ty, m.outputs = [{name := "out", ty := ty}]
  outputTyped : OutputTypedAt outWidth (weOf m) m.body
  outputWidth : ∀ p ∈ m.outputs, p.ty.bitWidth = outWidth
  order : Tools.ShippingSettledSoundness.Acyclic m.body
  moduleName : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true

/-- Compatibility specialization for the existing Bool source endpoint. -/
abbrev PrintBase := PrintBaseAt 1

/-- The raw entry establishes both value preservation and the preconditions
needed by the real cleanup and optimizer passes, at its actual output width. -/
def RawValueAt (outWidth : Nat) (bs : List (Name × MixedGateBinder)) (m : Sparkle.IR.AST.Module)
    (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
    ∃ result, evalAssigns (moduleWidths m) mems m.body initial = some result ∧
      result "out" = expected ∧
      TypedPostReady m ∧ SimpleStmts m.body ∧ weOf m = moduleWidths m ∧ "out" ∈ m.outputs.map (·.name) ∧
      (∀ p ∈ m.inputs, initial p.name < 2 ^ weOf m p.name) ∧
      (PositiveBinders bs → PrintBaseAt outWidth m)

abbrev RawValue := RawValueAt 1

def MixedPreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (m : Sparkle.IR.AST.Module) : Prop :=
  MixedSourcePreserves declName bs body (RawValue bs m)

theorem MixedSourcePreserves.map {declName bs body P Q}
    (h : MixedSourcePreserves declName bs body P)
    (f : ∀ initial mems expected, P initial mems expected → Q initial mems expected) :
    MixedSourcePreserves declName bs body Q := by
  obtain ⟨ids, nd, len, cache, h⟩ := h
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals e hn he hb hv quote
  exact f initial mems _ (h bools bits initial mems values dom n kb kv binp vinp bvals vvals e hn he hb hv quote)

theorem synthesizeMixedCertified_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body) (m, d)) :
    MixedPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals e hn he hb hv quote
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [quote] at leaf
  obtain ⟨unique, result, eval, value, out, typed, _⟩ := emitLeaves_bool_from_ports hn hb hv e he
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  have outputEq : m.outputs = st.module.outputs.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
  have shape := prepare_shape (bools := bools) (bits := bits) (bs.zip ids) a (by intro p hp; cases hp)
  obtain ⟨wm, ready, printOutputs, outputTyped, outputWidth, order⟩ := emitLeaves_postReady (mems := mems) hn hb hv e he
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 shape.1 shape.2 wireEq bodyEq outputEq leaf
  have ib := prepare_inputBounds (bs.zip ids) a (by intro p hp; cases hp) values
  have contract := translateExprToWire_bool_contract (ctx := p.context) (we := declaredWidths st)
    (mems := mems) (initial := initial) (dom := dom) hn hb hv e he
  obtain ⟨w, sm, ty, tr, fresh, ht, hty⟩ := emitLeaves_single leaf
  have frame := contract.frame "out" false true p.state sm w (prepared.1.lookup prepared.2.1) tr
  refine ⟨result, ?_, value, ready, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moduleWidths_finish wireEq unique, bodyEq]; exact eval
  · have simple := frame.simple (by rw [prepared.2.2.1]; intro stmt hs; cases hs)
    intro stmt hs
    rw [bodyEq] at hs
    change stmt ∈ st.module.body.reverse at hs
    rw [List.mem_reverse, ht, emitAssign_body_cons] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨"out", .ref w, rfl, rfl⟩
    · exact simple stmt hs
  · rw [wm, moduleWidths_finish wireEq unique]
  · rw [outputEq, List.map_reverse, List.mem_reverse]; exact out
  · intro port hp
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      have hs' : stmt ∈ st.module.finalize.body := List.mem_reverse.mpr hs
      obtain ⟨l, rhs, n, eq, _⟩ := typed stmt hs'
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    have hp' : port ∈ p.state.module.inputs := by
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      exact frame.inputs ▸ hp
    obtain ⟨decl, bound⟩ := ib port hp'
    rw [wm, declaredWidths_agree unique port (by rw [ht, emitAssign_wires]; exact frame.decls port decl)]
    exact bound
  · intro positive
    have pi := prepare_print (bools := bools) (bits := bits) (bs.zip ids) a
      (by intro port hp; cases hp) (fun name n id hp => positive name n (List.of_mem_zip hp).1)
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      obtain ⟨l, rhs, n, eq, _⟩ := typed stmt (List.mem_reverse.mpr hs)
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    have decls := prepare_declarations (bools := bools) (bits := bits) (bs.zip ids) a
      (List.Sublist.refl []) (by intro port hp; cases hp)
    refine ⟨?_, ?_, ?_, printOutputs, ?_, ?_, ?_, ?_, ?_, outputTyped, outputWidth, order, nameLegal⟩
    · rw [hm, noSeq]
      change st.module.isPrimitive = false
      rw [ht]; change sm.module.isPrimitive = false
      rw [frame.primitive]; exact pi.2.2
    · rw [hm, noSeq]
      change st.module.parameters.reverse = []
      rw [ht]; change sm.module.parameters.reverse = []
      rw [frame.parameters, pi.2.1]; rfl
    · intro port hp
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      exact pi.1 port (frame.inputs ▸ hp)
    · intro port hp
      rw [wireEq, List.mem_reverse, ht, emitAssign_wires] at hp
      exact frame.scalar shape.1 port hp
    · intro port hp
      rw [wireEq, List.mem_reverse, ht, emitAssign_wires] at hp
      exact (frame.wireNames port hp).elim (decls.2 port) id
    · rw [mi, List.map_reverse]
      apply nodup_reverse
      rw [ht, emitAssign_inputs]
      change (sm.module.inputs.map Port.name).Nodup
      rw [frame.inputs]
      exact prepared.2.1.1.sublist (decls.1.map _)
    · intro port hp
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      change port ∈ sm.module.inputs at hp
      rw [frame.inputs] at hp
      rw [wireEq, List.mem_reverse, ht, emitAssign_wires]
      exact frame.decls port (decls.1.subset hp)
    · refine ⟨ty, ?_⟩
      rw [outputEq, ht, emitAssign_outputs]
      change ( {name := "out", ty := ty} :: sm.module.outputs).reverse = _
      rw [frame.outputs, shape.2]; rfl

/-- The actual declaration dispatcher selects this proved input/translation
path. Both gate decisions are pure, checkable conditions on that declaration. -/
theorem synthesizeFromConst_mixed_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName [] false true ci) (m, d)) :
    MixedPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_sound run

/-- The mixed result is tied to the declaration read by this very synthesis
run. As for the old entry, identifying that declaration with a source constant
is the separate `EnvDefines` trust boundary. -/
theorem synthesizeCombinationalCore_mixed_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) → MixedPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape => synthesizeFromConst_mixed_sound old shape run.mreturns⟩

end Tools.ShippingMixedEntrySoundness
