import Tools.ShippingMachineClose
import Tools.ShippingMachineTrace
import Tools.ShippingUnifiedExecutionSoundness

/-! # A state machine through the real synthesis

`synthesizeMachineCertified` compiles the TRANSITION of a `circuit do` — a
combinational body over the declaration's binders plus one binder per
register slot, its value the result and every next value packed into one bit
vector — with the certified combinational harness, and closes the slot ports
into registers (`Sparkle.IR.Machine.closeMachine`).

This file composes what is already proved about the two halves:

* the harness computes the packed transition value on every environment
  that carries the binders' values (`synthesizeMixedCertified_term_sound_at`);
* closing steps every slot register to its field of that value and drives
  `out` with the result field (`closeMachine_step`);

into one cycle of the emitted module (`MachinePreserves`), and iterates it
(`machine_trace`): the emitted module, run for any number of cycles with
reset low from a state holding the slots' values, shows at every cycle the
result field of the transition applied to that cycle's inputs and slot
values — for ANY valuation of the slots over time that starts in the
registers' state and follows the transition. That the source `circuit do` is
such a valuation is `Tools/ShippingMachineSource.lean`. -/
namespace Tools.ShippingMachineEntry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Machine Sparkle.IR.Type
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose Tools.ShippingMachineTrace

/-! ## The input ports of the binder walk -/

/-- The input ports the binder walk declares, in declaration order: one per
Bool or BitVec binder, named by the wire allocator at that point. -/
def inputPorts (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    List ((Name × MixedGateBinder) × FVarId) → Setup → List Port
  | [], _ => []
  | ((name, .domain), id) :: rest, a =>
    inputPorts bools bits rest (extend a ((name, .domain), id) bools bits)
  | ((name, .bool), id) :: rest, a =>
    { name := inputWire a.state name.toString .bit, ty := .bit } ::
      inputPorts bools bits rest (extend a ((name, .bool), id) bools bits)
  | ((name, .bits n), id) :: rest, a =>
    { name := inputWire a.state name.toString (.bitVector n), ty := .bitVector n } ::
      inputPorts bools bits rest (extend a ((name, .bits n), id) bools bits)

theorem inputState_inputs (s : CircuitState) (name : String) (ty : HWType) :
    (inputState s name ty).module.inputs =
      { name := inputWire s name ty, ty := ty } :: s.module.inputs := by
  change (_ :: (CircuitM.makeWire name ty true s).2.module.inputs) = _
  rw [Tools.ShippingTranslateSoundness.makeWire_inputs]

theorem prepare_inputs {bools bits} (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) :
    (prepare bools bits L a).state.module.inputs =
      (inputPorts bools bits L a).reverse ++ a.state.module.inputs := by
  induction L generalizing a with
  | nil => simp [prepare, inputPorts]
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih _
    | bool =>
      have h := ih (extend a ((name, .bool), id) bools bits)
      simp only [prepare, inputPorts, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [h]
      congr 1
      exact inputState_inputs a.state name.toString .bit
    | bits n =>
      have h := ih (extend a ((name, .bits n), id) bools bits)
      simp only [prepare, inputPorts, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [h]
      congr 1
      exact inputState_inputs a.state name.toString (.bitVector n)

theorem extend_state (a a' : Setup) (b : (Name × MixedGateBinder) × FVarId)
    (bools bools' : FVarId → Bool) (bits bits' : (id : FVarId) → (n : Nat) → BitVec n)
    (h : a.state = a'.state) :
    (extend a b bools bits).state = (extend a' b bools' bits').state := by
  obtain ⟨⟨name, kind⟩, id⟩ := b
  cases kind <;> simp [extend, h]

/-- The ports depend on the allocator state only, not on the values. -/
theorem inputPorts_congr {bools bools' : FVarId → Bool}
    {bits bits' : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a a' : Setup), a.state = a'.state →
      inputPorts bools bits L a = inputPorts bools' bits' L a'
  | [], _, _, _ => rfl
  | ((name, .domain), id) :: rest, a, a', h => by
    simp only [inputPorts]
    exact inputPorts_congr rest _ _ (extend_state a a' _ bools bools' bits bits' h)
  | ((name, .bool), id) :: rest, a, a', h => by
    simp only [inputPorts, h]
    rw [inputPorts_congr rest _ _ (extend_state a a' _ bools bools' bits bits' h)]
  | ((name, .bits n), id) :: rest, a, a', h => by
    simp only [inputPorts, h]
    rw [inputPorts_congr rest _ _ (extend_state a a' _ bools bools' bits bits' h)]

/-- … and so does the allocator state the walk reaches. -/
theorem prepare_state_congr {bools bools' : FVarId → Bool}
    {bits bits' : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a a' : Setup), a.state = a'.state →
      (prepare bools bits L a).state = (prepare bools' bits' L a').state
  | [], _, _, h => h
  | b :: rest, a, a', h =>
    prepare_state_congr rest _ _ (extend_state a a' b bools bools' bits bits' h)

theorem prepare_append {bools bits} (L1 L2 : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) :
    prepare bools bits (L1 ++ L2) a = prepare bools bits L2 (prepare bools bits L1 a) := by
  induction L1 generalizing a with
  | nil => rfl
  | cons b rest ih => exact ih _

theorem inputPorts_append {bools bits} (L1 L2 : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) :
    inputPorts bools bits (L1 ++ L2) a =
      inputPorts bools bits L1 a ++ inputPorts bools bits L2 (prepare bools bits L1 a) := by
  induction L1 generalizing a with
  | nil => rfl
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih _
    | bool => simp only [List.cons_append, inputPorts, prepare, ih]
    | bits n => simp only [List.cons_append, inputPorts, prepare, ih]

theorem admissible_append {bools bits initial}
    (L1 L2 : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) :
    Admissible bools bits initial (L1 ++ L2) a ↔
      Admissible bools bits initial L1 a ∧
        Admissible bools bits initial L2 (prepare bools bits L1 a) := by
  induction L1 generalizing a with
  | nil => simp [Admissible, prepare]
  | cons b rest ih => simp only [List.cons_append, Admissible, prepare, ih, and_assoc]

/-- The all-zero environment carries the all-zero values. -/
theorem admissible_zero (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) :
    Admissible (fun _ => false) (fun _ n => 0#n) (fun _ => 0) L a := by
  induction L generalizing a with
  | nil => trivial
  | cons b rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := b
    refine ⟨?_, ih _⟩
    cases kind <;> simp [InputValue, encodeBool]

/-- Admissibility reads the values of the listed binders only. -/
theorem admissible_congr {bools bools' : FVarId → Bool}
    {bits bits' : (id : FVarId) → (n : Nat) → BitVec n} {initial : Env} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a a' : Setup), a.state = a'.state →
      (∀ b ∈ L, bools b.2 = bools' b.2 ∧ ∀ n, bits b.2 n = bits' b.2 n) →
      Admissible bools bits initial L a → Admissible bools' bits' initial L a'
  | [], _, _, _, _, _ => trivial
  | ((name, kind), id) :: rest, a, a', hs, hv, ⟨h, hrest⟩ => by
    refine ⟨?_, admissible_congr rest _ _ (extend_state a a' _ bools bools' bits bits' hs)
      (fun b hb => hv b (List.mem_cons_of_mem _ hb)) hrest⟩
    have hval := hv ((name, kind), id) List.mem_cons_self
    cases kind with
    | domain => trivial
    | bool =>
      simp only [InputValue] at h ⊢
      rw [← hs, ← hval.1]; exact h
    | bits n =>
      simp only [InputValue] at h ⊢
      rw [← hs, ← hval.2 n]; exact h

/-- The inputs' admissibility reads the valuation at the inputs' positions
only. -/
theorem sourceInputs_congr {declName : Name} {bs : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} (nd : ids.Nodup)
    {bools bools' : Nat → Bool} {bits bits' : (j : Nat) → (n : Nat) → BitVec n} {initial : Env}
    (hb : ∀ j, j < bs.length → bools j = bools' j)
    (hv : ∀ j, j < bs.length → ∀ n, bits j n = bits' j n)
    (h : SourceInputs declName bs ids cache bools bits initial) :
    SourceInputs declName bs ids cache bools' bits' initial := by
  unfold SourceInputs at h ⊢
  refine admissible_congr _ _ _ rfl ?_ h
  intro b hmem
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hmem
  have hjb : j < bs.length := by
    rw [List.length_zip] at hj; omega
  have hji : j < ids.length := by
    rw [List.length_zip] at hj; omega
  have hid : b.2 = ids[j]! := by
    rw [← hget]
    simp [List.getElem_zip, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hji]
  have hidx : ids.idxOf b.2 = j := by rw [hid]; exact index_fresh ids nd j hji
  exact ⟨by simp only [boolValues, hidx]; exact hb j hjb,
    fun n => by simp only [bitValues, hidx]; exact hv j hjb n⟩

/-- The encoded source value of a binder. -/
def binderEnc (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (b : (Name × MixedGateBinder) × FVarId) : Nat :=
  match b.1.2 with
  | .domain => 0
  | .bool => encodeBool (bools b.2)
  | .bits n => (bits b.2 n).toNat

/-- Hardware binders whose ports hold their values are admissible. -/
theorem admissible_of_ports {bools bits initial} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (∀ b ∈ L, b.1.2 ≠ .domain) →
      Zip₂ (fun (p : Port) b => initial p.name = binderEnc bools bits b)
        (inputPorts bools bits L a) L →
      Admissible bools bits initial L a
  | [], _, _, _ => trivial
  | ((name, .domain), id) :: rest, a, hnd, _ => absurd rfl (hnd _ List.mem_cons_self)
  | ((name, .bool), id) :: rest, a, hnd, hz => by
    simp only [inputPorts] at hz
    cases hz with
    | cons h hs =>
      exact ⟨h, admissible_of_ports rest _ (fun b hb => hnd b (List.mem_cons_of_mem _ hb)) hs⟩
  | ((name, .bits n), id) :: rest, a, hnd, hz => by
    simp only [inputPorts] at hz
    cases hz with
    | cons h hs =>
      exact ⟨h, admissible_of_ports rest _ (fun b hb => hnd b (List.mem_cons_of_mem _ hb)) hs⟩

/-- The hardware type of a binder kind. -/
def kindTy : MixedGateBinder → HWType
  | .domain => .bit
  | .bool => .bit
  | .bits n => .bitVector n

/-- Hardware binders get one port each, of the binder's type. -/
theorem inputPorts_types {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (∀ b ∈ L, b.1.2 ≠ .domain) →
      Zip₂ (fun (p : Port) b => p.ty = kindTy b.1.2) (inputPorts bools bits L a) L
  | [], _, _ => .nil
  | ((name, .domain), id) :: rest, a, hnd => absurd rfl (hnd _ List.mem_cons_self)
  | ((name, .bool), id) :: rest, a, hnd => by
    simp only [inputPorts]
    exact .cons rfl (inputPorts_types rest _ (fun b hb => hnd b (List.mem_cons_of_mem _ hb)))
  | ((name, .bits n), id) :: rest, a, hnd => by
    simp only [inputPorts]
    exact .cons rfl (inputPorts_types rest _ (fun b hb => hnd b (List.mem_cons_of_mem _ hb)))

/-! ## Lists -/

theorem zip_take_length {α β : Type} : ∀ (l : List α) (r : List β),
    l.zip r = l.zip (r.take l.length)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: r => by simp [zip_take_length l r]

/-! ## The register updates, by name -/

/-- The update list: each register steps to its field of the packed value. -/
def fieldNexts (P : Nat) : List String → List SlotField → List (String × Nat)
  | r :: rs, f :: fs => (r, mask f.width (P >>> f.lo)) :: fieldNexts P rs fs
  | _, _ => []

theorem slotNexts_eq (P : Nat) : ∀ (ps : List Port) (fs : List SlotField),
    slotNexts P ps fs = fieldNexts P (ps.map Port.name) fs
  | [], _ => by simp [slotNexts, fieldNexts]
  | _ :: _, [] => by simp [slotNexts, fieldNexts]
  | p :: ps, f :: fs => by simp [slotNexts, fieldNexts, slotNexts_eq P ps fs]

theorem applyNexts_fieldNexts {st : String → Nat} {P : Nat} :
    ∀ {rs : List String} {fs : List SlotField}, rs.Nodup →
      ∀ (i : Nat) (r : String) (f : SlotField), rs[i]? = some r → fs[i]? = some f →
        applyNexts st (fieldNexts P rs fs) r = mask f.width (P >>> f.lo)
  | [], _, _, i, r, f, hr, _ => by simp at hr
  | _ :: _, [], _, i, r, f, _, hf => by simp at hf
  | r0 :: rs, f0 :: fs, nd, 0, r, f, hr, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hf
    subst hr; subst hf
    simp [applyNexts, fieldNexts]
  | r0 :: rs, f0 :: fs, nd, i + 1, r, f, hr, hf => by
    simp only [List.getElem?_cons_succ] at hr hf
    obtain ⟨hnot, nd'⟩ := List.nodup_cons.mp nd
    have hne : r0 ≠ r := fun h => hnot (h ▸ List.mem_of_getElem? hr)
    have ih := applyNexts_fieldNexts (st := st) (P := P) nd' i r f hr hf
    have hb : (r0 == r) = false := by simpa using hne
    simpa [applyNexts, fieldNexts, hb] using ih

/-! ## The transition module -/

/-- The value of the binder at position `pos`, encoded. -/
def posEnc (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (pos : Nat) :
    MixedGateBinder → Nat
  | .domain => 0
  | .bool => encodeBool (bools pos)
  | .bits n => (bits pos n).toNat

/-- What a run of the certified combinational harness on a quoted term fixes
about the module it returns: the value of `out` on every environment that
carries the binders' values, that the body ends in `assign out = w`, and
that the input ports are the binder walk's. -/
theorem transition_facts {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init declName.toString) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (nameLegal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {srt : SType} {e : Term srt} (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) e) :
    (∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env)
        (mems : MEnv),
      SourceInputs declName bs ids cache bools bits initial →
      RawValueAt srt.width bs m initial mems
        (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat) ∧
    (∃ B w, m.body = B ++ [.assign "out" (.ref w)]) ∧
    (∀ bools bits, m.inputs = inputPorts bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)) := by
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  have at_ : ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env)
      (mems : MEnv), SourceInputs declName bs ids cache bools bits initial →
      RawValueAt srt.width bs m initial mems
          (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat ∧
        ∃ w sm ty, st = (CircuitM.emitAssign "out" (.ref w) (CircuitM.addOutput "out" ty sm).2).2 ∧
          sm.module.inputs = (prepare (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.module.inputs := by
    intro bools bits initial mems values
    subst hbody
    apply synthesizeMixedCertified_term_sound_at run hm nameLegal
      (boolValues ids bools) (bitValues ids bits) initial mems values
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
      kb kv vw (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bool_lookup (bools := boolValues ids bools)
        (bits := bitValues ids bits) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
      simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
    · intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bits_lookup (bools := boolValues ids bools)
        (bits := bitValues ids bits) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
      simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup
    · apply instantiated_quote _ _ e he
      · intro j hj
        obtain ⟨name, pos⟩ := hb j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
      · intro j hj
        obtain ⟨name, pos⟩ := hv j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
  refine ⟨fun bools bits initial mems values => (at_ bools bits initial mems values).1, ?_, ?_⟩
  all_goals
    have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
        (fun _ => 0) := admissible_zero _ _
    obtain ⟨raw, w, sm, ty, ht, hin⟩ := at_ _ _ _ (fun _ _ => 0) zero
    have bodyEq : m.body = st.module.body.reverse := by
      rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  · refine ⟨(CircuitM.addOutput "out" ty sm).2.module.body.reverse, w, ?_⟩
    rw [bodyEq, ht, emitAssign_body_cons, List.reverse_cons]
  · intro bools bits
    obtain ⟨result, _, _, ready, _⟩ := raw
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      obtain ⟨l, rhs, k, eq, _⟩ := ready.typed stmt (by rw [bodyEq]; exact List.mem_reverse.mpr hs)
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    rw [mi, ht, emitAssign_inputs]
    change sm.module.inputs.reverse = _
    rw [hin, prepare_inputs]
    simp only [start, CircuitM.init, Module.empty, List.append_nil, List.reverse_reverse]
    exact inputPorts_congr _ _ _ rfl

/-! ## One cycle of the machine -/

/-- The packed transition value at a valuation of the binders. -/
def packedAt {srt : SType} (e : Term srt) (bpos vpos : Nat → Nat) (bools : Nat → Bool)
    (bits : (j : Nat) → (n : Nat) → BitVec n) : Nat :=
  (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat

/-- **One cycle of a compiled state machine.** The module the machine route
returns has one register per slot (`regs`, in slot order) and, on every
environment that carries the inputs' values, holds the slots' values in the
registers and has reset low, one cycle steps each register to its field of
the packed transition value and drives `out` with the result field. -/
def MachinePreserves (declName : Name) (shape : MachineShape)
    (bsIn slotBs : List (Name × MixedGateBinder)) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bpos vpos : Nat → Nat)
      {srt : SType} (e : Term srt),
    e.WF kb kv vw →
    (∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool)) →
    (∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j))) →
    shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j)) e →
    ∃ regs : List String, regs.Nodup ∧ regs.length = slotBs.length ∧
    ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (env0 : Env) (mems : MEnv),
      SourceInputs declName bsIn ids cache bools bits env0 →
      (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        env0 r = posEnc bools bits (bsIn.length + i) b.2) →
      env0 "rst" = 0 →
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, fieldNexts (packedAt e bpos vpos bools bits) regs shape.layout.slots,
            mems) ∧
        envF "out" = mask shape.layout.outWidth
          (packedAt e bpos vpos bools bits >>> shape.layout.outLo)

theorem synthesizeMachineCertified_returns {logProf declName shape m d}
    (hr : MReturns (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
      (m, d)) :
    ∃ t, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire e hint top named) logProf declName
        shape.binders shape.body) (t, d) ∧
      m = closeMachine shape.layout t := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, run, hr⟩ := MReturns.bind hr
  have eq := MReturns.pure hr
  cases eq
  exact ⟨t, run, rfl⟩

theorem weOf_of_port {m : Sparkle.IR.AST.Module} (nd : (m.wires.map (·.name)).Nodup)
    {p : Port} (hp : p ∈ m.wires) :
    weOf m p.name = match p.ty with
      | .bitVector k => k
      | .bit => 1
      | _ => 0 := by
  unfold weOf
  rw [find?_of_nodup nd hp]
  obtain ⟨name, ty⟩ := p
  cases ty <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The machine route preserves one cycle.** -/
theorem synthesizeMachineCertified_sound {logProf declName shape m d}
    {bsIn slotBs : List (Name × MixedGateBinder)}
    (hr : MReturns (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
      (m, d))
    (hbs : shape.binders = bsIn ++ slotBs)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outPos : 0 < shape.layout.outWidth) :
    MachinePreserves declName shape bsIn slotBs m := by
  obtain ⟨t, hrun, hmt⟩ := synthesizeMachineCertified_returns hr
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns hrun
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos srt e he hb hv hbody
  obtain ⟨raw, ⟨B, w, hB⟩, hinputs⟩ := transition_facts nd len run hm nameLegal he hb hv hbody
  -- The binder list splits into inputs and slots; so do the ids.
  let a := start (entryCompilerState false cache) declName.toString
  let k := bsIn.length
  have hk : k ≤ ids.length := by rw [len, hbs]; simp [k]
  have hzip : shape.binders.zip ids = bsIn.zip (ids.take k) ++ slotBs.zip (ids.drop k) := by
    conv => lhs; rw [hbs, ← List.take_append_drop k ids]
    exact List.zip_append (by simp [k, Nat.min_eq_left hk])
  have dropLen : (ids.drop k).length = slotBs.length := by
    have : ids.length = bsIn.length + slotBs.length := by rw [len, hbs]; simp
    simp [k]; omega
  have slotNoDom : ∀ b ∈ slotBs.zip (ids.drop k), b.1.2 ≠ .domain :=
    fun b hb => slotKinds b.1 (List.of_mem_zip hb).1
  -- The slot ports, at the zero valuation.
  let zb : FVarId → Bool := fun _ => false
  let zv : (id : FVarId) → (n : Nat) → BitVec n := fun _ n => 0#n
  let ps := inputPorts zb zv (slotBs.zip (ids.drop k)) (prepare zb zv (bsIn.zip (ids.take k)) a)
  have psTypes := inputPorts_types (bools := zb) (bits := zv) (slotBs.zip (ids.drop k))
    (prepare zb zv (bsIn.zip (ids.take k)) a) slotNoDom
  have psLen : ps.length = slotBs.length := by
    rw [psTypes.length_eq, List.length_zip, dropLen, Nat.min_self]
  have slotsLen : shape.layout.slots.length = slotBs.length := layW.length_eq
  have tInputs : t.inputs = inputPorts zb zv (bsIn.zip (ids.take k)) a ++ ps := by
    rw [hinputs zb zv, hzip, inputPorts_append]
  have hdrop : t.inputs.drop (t.inputs.length - shape.layout.slots.length) = ps := by
    rw [tInputs, List.length_append, slotsLen, psLen, Nat.add_sub_cancel, List.drop_left]
  -- Facts of the transition module that do not depend on the cycle.
  have zero : SourceInputs declName shape.binders ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := raw _ _ _ (fun _ _ => 0) zero
  have pb := base positive
  have psMem : ∀ p ∈ ps, p ∈ t.wires := fun p hp =>
    pb.inputWires p (by rw [tInputs]; exact List.mem_append_right _ hp)
  have psNodup : (ps.map Port.name).Nodup := by
    have := pb.inputNames
    rw [tInputs, List.map_append] at this
    exact (List.nodup_append.mp this).2.1
  have slotsOk : Zip₂ (SlotOk (weOf t)) ps shape.layout.slots := by
    apply Zip₂.of_get (by rw [psLen, slotsLen])
    intro i p f hp hf
    have hi : i < slotBs.length := by
      have := (List.getElem?_eq_some_iff.mp hp).1; omega
    have hid : i < (ids.drop k).length := by omega
    have hbz : (slotBs.zip (ids.drop k))[i]? = some (slotBs[i], (ids.drop k)[i]) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hid⟩
    have hty := psTypes.get i p _ hp hbz
    have hw := layW.get i f _ hf (List.getElem?_eq_getElem hi)
    have hmem : p ∈ ps := List.mem_of_getElem? hp
    have hwe := weOf_of_port ready.wiresNodup (psMem p hmem)
    have hnd := slotKinds _ (List.getElem_mem hi)
    rw [hty] at hwe
    revert hwe hw hnd
    generalize hkind : (slotBs[i]).2 = kind
    have hpos : ∀ n, kind = .bits n → 0 < n := by
      intro n hn
      refine positive (slotBs[i]).1 n ?_
      rw [hbs]
      refine List.mem_append_right _ ?_
      have : slotBs[i] = ((slotBs[i]).1, MixedGateBinder.bits n) := by
        rw [← hn, ← hkind]
      rw [← this]
      exact List.getElem_mem hi
    intro hwe hw hnd
    cases kind with
    | domain => exact absurd rfl hnd
    | bool => exact ⟨by rw [hw, hwe]; rfl, by rw [hwe]; exact Nat.one_pos⟩
    | bits n => exact ⟨by rw [hw, hwe]; rfl, by rw [hwe]; exact hpos n rfl⟩
  refine ⟨ps.map Port.name, psNodup, by rw [List.length_map, psLen], ?_⟩
  intro bools bits env0 mems inputs slotVals hrst
  -- The cycle's environment carries every binder's value.
  have values : SourceInputs declName shape.binders ids cache bools bits env0 := by
    unfold SourceInputs
    rw [hzip, admissible_append]
    refine ⟨?_, ?_⟩
    · have := inputs
      unfold SourceInputs at this
      rwa [zip_take_length] at this
    · apply admissible_of_ports _ _ slotNoDom
      have hps : inputPorts (boolValues ids bools) (bitValues ids bits) (slotBs.zip (ids.drop k))
          (prepare (boolValues ids bools) (bitValues ids bits) (bsIn.zip (ids.take k)) a) = ps := by
        exact inputPorts_congr _ _ _ (prepare_state_congr _ _ _ rfl)
      rw [hps]
      apply Zip₂.of_get (by rw [psLen, List.length_zip, dropLen, Nat.min_self])
      intro i p b hp hb
      obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hb
      have hreg : (ps.map Port.name)[i]? = some p.name := by simp [hp]
      rw [slotVals i p.name b.1 hreg hb1]
      have hi : i < slotBs.length := (List.getElem?_eq_some_iff.mp hb1).1
      have hidx : ids.idxOf b.2 = k + i := by
        have hget : ids[k + i]! = b.2 := by
          have hlt : k + i < ids.length := by
            have : ids.length = bsIn.length + slotBs.length := by rw [len, hbs]; simp
            simp only [k]; omega
          rw [List.getElem?_drop] at hb2
          simp [List.getElem!_eq_getElem?_getD, hb2]
        rw [← hget]
        exact index_fresh ids nd (k + i) (by
          have : ids.length = bsIn.length + slotBs.length := by rw [len, hbs]; simp
          simp only [k]; omega)
      obtain ⟨⟨name, kind⟩, id⟩ := b
      cases kind <;> simp [binderEnc, posEnc, boolValues, bitValues, hidx, k] at hidx ⊢
  obtain ⟨result, hres, hval, ready', _, hwe, _, _, _⟩ := raw bools bits env0 mems values
  rw [← hwe] at hres
  obtain ⟨envF, hstep, hout⟩ := closeMachine_step (lay := shape.layout) hB ready'.typed
    pb.wireNames pb.inputWires pb.inputNames (by rw [hdrop]; exact slotsOk) outPos hres hrst
  rw [hdrop, slotNexts_eq, hval] at hstep
  rw [hval] at hout
  subst hmt
  exact ⟨envF, hstep, hout⟩

/-! ## The trace -/

/-- **The trace of a compiled state machine.** Let `bools τ`, `bits τ` be a
valuation of the binders over time — inputs and slots alike — whose slot
values start in the registers' state and follow the transition. Then a
`T`-cycle run of the emitted module, seeded each cycle with the inputs of
that cycle over the register state and with reset low, succeeds, and cycle
`j` drives `out` with the result field of the transition at time `j`. -/
theorem machine_trace {declName shape m} {bsIn slotBs : List (Name × MixedGateBinder)}
    (h : MachinePreserves declName shape bsIn slotBs m)
    (slotsLen : shape.layout.slots.length = slotBs.length) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bpos vpos : Nat → Nat)
        {srt : SType} (e : Term srt),
      e.WF kb kv vw →
      (∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool)) →
      (∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j))) →
      shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
        (fun j => inputExpr shape.binders.length (vpos j)) e →
      ∃ regs : List String, regs.Nodup ∧ regs.length = slotBs.length ∧
      ∀ (T : Nat) (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T →
          SourceInputs declName bsIn ids cache (bools (T - 1 - t)) (bits (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
          st0 r = posEnc (bools 0) (bits 0) (bsIn.length + i) b.2) →
        (∀ τ i f b, shape.layout.slots[i]? = some f → slotBs[i]? = some b →
          posEnc (bools (τ + 1)) (bits (τ + 1)) (bsIn.length + i) b.2 =
            mask f.width (packedAt e bpos vpos (bools τ) (bits τ) >>> f.lo)) →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
            mask shape.layout.outWidth
              (packedAt e bpos vpos (bools j) (bits j) >>> shape.layout.outLo) := by
  obtain ⟨ids, nd, len, cache, h⟩ := h
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos srt e he hb hv hbody
  obtain ⟨regs, regsNd, regsLen, step⟩ := h dom kb kv vw bpos vpos e he hb hv hbody
  refine ⟨regs, regsNd, regsLen, ?_⟩
  intro T bools bits seed st0 mems inputs pass rst init follow
  -- `k` cycles remain; the state holds the slots' values at time `T - k`.
  suffices main : ∀ (k : Nat), k ≤ T → ∀ (st : String → Nat),
      (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        st r = posEnc (bools (T - k)) (bits (T - k)) (bsIn.length + i) b.2) →
      ∃ envs, runModule (weOf m) m.body seed k st mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          mask shape.layout.outWidth
            (packedAt e bpos vpos (bools (T - k + j)) (bits (T - k + j)) >>>
              shape.layout.outLo) by
    obtain ⟨envs, hrun, hlen, hobs⟩ := main T (Nat.le_refl T) st0 (by simpa using init)
    refine ⟨envs, hrun, hlen, fun j hj => ?_⟩
    simpa using hobs j hj
  intro k
  induction k with
  | zero => intro _ st _; exact ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro hk st inv
    have hτ : T - 1 - k = T - (k + 1) := by omega
    obtain ⟨envF, hstep, hout⟩ := step (bools (T - (k + 1))) (bits (T - (k + 1)))
      (seed k st) mems (hτ ▸ inputs k st (by omega))
      (fun i r b hr hb' => by
        rw [pass k st r (List.mem_of_getElem? hr)]; exact inv i r b hr hb')
      (rst k st)
    have inv' : ∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        applyNexts st (fieldNexts (packedAt e bpos vpos (bools (T - (k + 1)))
          (bits (T - (k + 1)))) regs shape.layout.slots) r =
          posEnc (bools (T - k)) (bits (T - k)) (bsIn.length + i) b.2 := by
      intro i r b hr hb'
      have hi : i < shape.layout.slots.length := by
        have := (List.getElem?_eq_some_iff.mp hb').1; omega
      rw [applyNexts_fieldNexts regsNd i r _ hr (List.getElem?_eq_getElem hi)]
      have hT : T - k = T - (k + 1) + 1 := by omega
      rw [hT]
      exact (follow (T - (k + 1)) i _ b (List.getElem?_eq_getElem hi) hb').symm
    obtain ⟨rest, hrun, hlen, hobs⟩ := ih (by omega) _ inv'
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hobs i hi]
        have hidx : T - k + i = T - (k + 1) + (i + 1) := by
          have : i < k := by omega
          omega
        rw [hidx]

/-! ## The real entry -/

theorem RunsTo.pure_eq {α : Type} {a b : α} {mctx mref cctx cref w w'}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a :=
  MReturns.pure h.mreturns

/-- A constant both certified gates refuse: the entry reads the environment
again, and when the constant is a machine shape the run IS the machine
synthesis of that shape. -/
theorem synthesizeFromConst_machine {logProf : String → IO Unit} {declName : Name}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Design}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (userProjection? envR) = some shape →
        MReturns (synthesizeMachineCertified
          (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
          (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  have hm := RunsTo.pure_eq hp
  subst hm
  refine ⟨envR, _, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact run

/-- **The machine boundary.** In this run the entry constant of the
declaration — computed by `entryConst` from the declaration and the
environment the run reads — is refused by both certified gates and is the
machine `shape` (by the structure projections of the environment the run
reads). -/
def MachineDefines (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ w1 ci w2 w5 envR w6 w7 envR' w8,
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (userProjection? envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (userProjection? envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (userProjection? envR)) (userProjection? envR') = some shape

/-- **A state machine through the real entry.** One successful run of the
real synthesis entry on a declaration at the machine boundary returns a
module that preserves every cycle of the machine. -/
theorem synthesizeCombinationalCore_machine_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hbs : shape.binders = bsIn ++ slotBs)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outPos : 0 < shape.layout.outWidth) :
    MachinePreserves declName shape bsIn slotBs m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine old miss run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  exact synthesizeMachineCertified_sound (hmach shape hshape) hbs positive slotKinds layW outPos

section
open Lean Elab Command

/-- `#def_machine_body v of f` adds `def v : Lean.Expr := <the packed
transition body of f>`: the body of the machine shape the synthesis entry
computes for `f`, by the same `entryConst` and `machineShape?` from the same
`getConstInfo` and environment. -/
elab "#def_machine_body " n:ident " of " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let ci ← getConstInfo declName
  let env ← getEnv
  let some shape := Sparkle.Compiler.Elab.machineShape? false []
      (Sparkle.Compiler.Elab.entryConst true false [] ci
        (Sparkle.Compiler.Elab.instancePredicate env) (Sparkle.Compiler.Elab.userInliner env)
        (Sparkle.Compiler.Elab.userProjection? env))
      (Sparkle.Compiler.Elab.userProjection? env)
    | throwError "{declName} is not a machine shape"
  let r ← match reflExpr shape.body with
    | .ok r => pure r
    | .error msg => throwError msg
  let nm := (← getCurrNamespace) ++ n.getId
  let ty := mkConst ``Lean.Expr
  let dv : DefinitionVal :=
    { name := nm
      levelParams := []
      type := ty
      value := r
      hints := ReducibilityHints.abbrev
      safety := DefinitionSafety.safe }
  liftCoreM <| addDecl (Declaration.defnDecl dv)

end

/-! ## Fields of a packed value -/

/-- A field inside the low operand of a concatenation. -/
theorem field_lo {m n : Nat} (x : BitVec m) (y : BitVec n) {lo w : Nat} (h : lo + w ≤ n) :
    mask w ((x ++ y).toNat >>> lo) = mask w (y.toNat >>> lo) := by
  unfold mask
  rw [BitVec.toNat_append]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hi : i < w
  · have : ¬ (n ≤ lo + i) := by omega
    simp [hi, this]
  · simp [hi]

/-- A field inside the high operand of a concatenation. -/
theorem field_hi {m n : Nat} (x : BitVec m) (y : BitVec n) {lo w : Nat} (h : n ≤ lo) :
    mask w ((x ++ y).toNat >>> lo) = mask w (x.toNat >>> (lo - n)) := by
  unfold mask
  rw [BitVec.toNat_append]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hi : i < w
  · have h1 : n ≤ lo + i := by omega
    have h2 : y.toNat.testBit (lo + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) h1))
    have h3 : lo + i - n = lo - n + i := by omega
    simp [hi, h1, h2, h3]
  · simp [hi]

/-- A whole operand. -/
theorem field_all {n : Nat} (y : BitVec n) : mask n (y.toNat >>> 0) = y.toNat := by
  simp [mask, Nat.mod_eq_of_lt y.isLt]

end Tools.ShippingMachineEntry
