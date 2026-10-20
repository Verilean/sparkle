import Tools.ShippingMixedOutputSoundness

/-! Actual input-port allocation establishes mixed input layout facts.
The legacy telescope/type-recognition walk is not assumed proved here. -/
namespace Tools.ShippingMixedInputSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedOutputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingBindingsSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMuxLoweringSoundness

def inputWire (s : CircuitState) (name : String) (ty : HWType) : String :=
  (CircuitM.makeWire name ty true s).1

def inputState (s : CircuitState) (name : String) (ty : HWType) : CircuitState :=
  (CircuitM.addInput (inputWire s name ty) ty (CircuitM.makeWire name ty true s).2).2

def inputContext (ctx : CompilerState) (id : FVarId) (wire : String) : CompilerState :=
  {ctx with varMap := (id, wire) :: ctx.varMap}

theorem input_wires (s : CircuitState) (name : String) (ty : HWType) :
    (inputState s name ty).module.wires = {name := inputWire s name ty, ty := ty} :: s.module.wires := by
  exact (CircuitM.makeWire_spec name ty true s).2.2.2

theorem input_bindings (s : CircuitState) (name : String) (ty : HWType) :
    (inputState s name ty).sourceBindings = s.sourceBindings :=
  CircuitM.makeWire_sourceBindings name ty true s

theorem input_body (s : CircuitState) (name : String) (ty : HWType) :
    (inputState s name ty).module.body = s.module.body :=
  (CircuitM.makeWire_spec name ty true s).2.2.1

theorem input_record (s : CircuitState) (name : String) (ty : HWType) :
    (inputState s name ty).translateRecord = s.translateRecord :=
  CircuitM.makeWire_translateRecord name ty true s

theorem input_wiresOk {s name ty} (h : WiresOk s) : WiresOk (inputState s name ty) := by
  have hm := CircuitM.makeWire_spec name ty true s
  have hw := WiresOk.fresh hm.1 hm.2.1 hm.2.2.2 h
  refine ⟨hw.1, ?_⟩
  intro p hp
  have hu := hw.2 p hp
  change ((CircuitM.addInput _ _ _).2).usedNames.contains p.name = true
  rw [addInput_state]
  simp [Std.HashSet.contains_insert, hu]

theorem visible_new {ctx s name ty id} :
    visible (inputContext ctx id (inputWire s name ty)) (inputState s name ty).sourceBindings id =
      some (inputWire s name ty) := by
  simp [visible, inputContext, lookup_cons_self]

theorem visible_old {ctx s name ty id other} (hne : other ≠ id) :
    visible (inputContext ctx id (inputWire s name ty)) (inputState s name ty).sourceBindings other =
      visible ctx s.sourceBindings other := by
  unfold visible inputContext
  rw [lookup_cons_ne _ _ hne, input_bindings]

theorem bind_bool_layout {ctx ρ β s initial id name b}
    (h : PortInputs ctx ρ β s initial) (other : β id = none)
    (value : initial (inputWire s name .bit) = encodeBool b) :
    PortInputs (inputContext ctx id (inputWire s name .bit))
      (fun key => if key = id then some b else ρ key) β (inputState s name .bit) initial := by
  constructor
  · intro key val hv
    by_cases eq : key = id
    · subst key
      simp only [ite_true] at hv
      cases hv
      exact ⟨inputWire s name .bit, visible_new, by rw [input_wires]; simp, value⟩
    · simp only [eq, if_false] at hv
      obtain ⟨w, bound, decl, val⟩ := h.bool key val hv
      exact ⟨w, (visible_old eq).trans bound, by rw [input_wires]; exact List.mem_cons_of_mem _ decl, val⟩
  · intro key n x hv
    have ne : key ≠ id := by intro eq; subst key; rw [other] at hv; cases hv
    obtain ⟨w, bound, decl, val⟩ := h.bits key n x hv
    exact ⟨w, (visible_old ne).trans bound, by rw [input_wires]; exact List.mem_cons_of_mem _ decl, val⟩

theorem bind_bits_layout {ctx ρ β s initial id name n} (x : BitVec n)
    (h : PortInputs ctx ρ β s initial) (other : ρ id = none)
    (value : initial (inputWire s name (.bitVector n)) = x.toNat) :
    PortInputs (inputContext ctx id (inputWire s name (.bitVector n))) ρ
      (fun key => if key = id then some ⟨n, x⟩ else β key) (inputState s name (.bitVector n)) initial := by
  constructor
  · intro key b hv
    have ne : key ≠ id := by intro eq; subst key; rw [other] at hv; cases hv
    obtain ⟨w, bound, decl, val⟩ := h.bool key b hv
    exact ⟨w, (visible_old ne).trans bound, by rw [input_wires]; exact List.mem_cons_of_mem _ decl, val⟩
  · intro key k y hv
    by_cases eq : key = id
    · subst key
      simp only [ite_true] at hv
      cases hv
      exact ⟨inputWire s name (.bitVector n), visible_new, by rw [input_wires]; simp, value⟩
    · simp only [eq, if_false] at hv
      obtain ⟨w, bound, decl, val⟩ := h.bits key k y hv
      exact ⟨w, (visible_old eq).trans bound, by rw [input_wires]; exact List.mem_cons_of_mem _ decl, val⟩

/-- The continuation of the actual Bool binder receives this proved layout. -/
theorem bindInputPort_bool_correct {α : Type} {ctx ρ β s t initial id name b}
    {k : CompilerM α} {result : α}
    (h : PortInputs ctx ρ β s initial) (wires : WiresOk s) (other : β id = none)
    (value : initial (inputWire s name .bit) = encodeBool b)
    (hr : Returns (bindInputPort id name .bit k) ctx s result t) :
    let sc := inputState s name .bit
    let cc := inputContext ctx id (inputWire s name .bit)
    Returns k cc sc result t ∧
    PortInputs cc (fun key => if key = id then some b else ρ key) β sc initial ∧
    WiresOk sc ∧ sc.module.body = s.module.body ∧ sc.translateRecord = s.translateRecord :=
  ⟨bindInputPort_returns hr, bind_bool_layout h other value, input_wiresOk wires,
    input_body _ _ _, input_record _ _ _⟩

theorem bindInputPort_bits_correct {α : Type} {ctx ρ β s t initial id name n}
    {k : CompilerM α} {result : α} (x : BitVec n)
    (h : PortInputs ctx ρ β s initial) (wires : WiresOk s) (other : ρ id = none)
    (value : initial (inputWire s name (.bitVector n)) = x.toNat)
    (hr : Returns (bindInputPort id name (.bitVector n) k) ctx s result t) :
    let sc := inputState s name (.bitVector n)
    let cc := inputContext ctx id (inputWire s name (.bitVector n))
    Returns k cc sc result t ∧
    PortInputs cc ρ (fun key => if key = id then some ⟨n, x⟩ else β key) sc initial ∧
    WiresOk sc ∧ sc.module.body = s.module.body ∧ sc.translateRecord = s.translateRecord :=
  ⟨bindInputPort_returns hr, bind_bits_layout x h other value, input_wiresOk wires,
    input_body _ _ _, input_record _ _ _⟩

theorem empty_layout (ctx : CompilerState) (name : String) (initial : Env) :
    PortInputs ctx (fun _ => none) (fun _ => none) (CircuitM.init name) initial ∧
      WiresOk (CircuitM.init name) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro id b hi; cases hi
  · intro id n x hi; cases hi
  · simp [WiresOk, CircuitM.init, Module.empty]

end Tools.ShippingMixedInputSoundness
