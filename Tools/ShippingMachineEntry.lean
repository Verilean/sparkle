import Tools.ShippingMachineClose
import Tools.ShippingMachineTrace
import Tools.ShippingMachineInst
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
open Tools.ShippingTypedPostSoundness Tools.ShippingTypedExprSoundness
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

/-! ## Hardware `let`s -/

/-- An environment that agrees on the binders' ports is as admissible. -/
theorem admissible_env_congr {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} {env env' : Env} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (∀ p ∈ inputPorts bools bits L a, env' p.name = env p.name) →
      Admissible bools bits env L a → Admissible bools bits env' L a
  | [], _, _, _ => trivial
  | ((name, .domain), id) :: rest, a, h, ⟨_, hr⟩ =>
    ⟨trivial, admissible_env_congr rest _ h hr⟩
  | ((name, .bool), id) :: rest, a, h, ⟨hv, hr⟩ => by
    refine ⟨?_, admissible_env_congr rest _ (fun p hp => h p (by simp [inputPorts, hp])) hr⟩
    simp only [InputValue] at hv ⊢
    rw [h { name := inputWire a.state name.toString .bit, ty := .bit } (by simp [inputPorts])]
    exact hv
  | ((name, .bits n), id) :: rest, a, h, ⟨hv, hr⟩ => by
    refine ⟨?_, admissible_env_congr rest _ (fun p hp => h p (by simp [inputPorts, hp])) hr⟩
    simp only [InputValue] at hv ⊢
    rw [h { name := inputWire a.state name.toString (.bitVector n), ty := .bitVector n }
      (by simp [inputPorts])]
    exact hv

theorem inputPorts_length {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (∀ b ∈ L, b.1.2 ≠ .domain) → (inputPorts bools bits L a).length = L.length :=
  fun L a h => (inputPorts_types L a h).length_eq

/-- The packed value with the `let` fields in front:
`let₀ ++ (let₁ ++ … (letₖ₋₁ ++ core))`. -/
def packLets : List (Σ w : Nat, Term (.bits w)) → {c : Nat} → Term (.bits c) →
    Σ W : Nat, Term (.bits W)
  | [], c, core => ⟨c, core⟩
  | f :: rest, _, core => ⟨f.1 + (packLets rest core).1, .concat f.2 (packLets rest core).2⟩

theorem packLets_wf {kb kv : Nat} {vw : Nat → Nat} :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
      (packLets fs core).2.WF kb kv vw → core.WF kb kv vw
  | [], _, _, h => h
  | _ :: rest, _, core, h => packLets_wf rest core h.2

/-- The valuation gives every `let` position the value of its field (and the
`let` binder is as wide as the field). -/
def LetsHold (bpos vpos : Nat → Nat) (bools : Nat → Bool)
    (bits : (j : Nat) → (n : Nat) → BitVec n) :
    Nat → List (Name × MixedGateBinder) → List (Σ w : Nat, Term (.bits w)) → Prop
  | _, [], [] => True
  | p, b :: bs, f :: fs =>
    posEnc bools bits p b.2 =
        (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) f.2).toNat ∧
      machWidth b.2 = f.1 ∧ LetsHold bpos vpos bools bits (p + 1) bs fs
  | _, _, _ => False

theorem LetsHold.length_eq {bpos vpos bools bits} :
    ∀ {p : Nat} {bs : List (Name × MixedGateBinder)} {fs : List (Σ w : Nat, Term (.bits w))},
      LetsHold bpos vpos bools bits p bs fs → bs.length = fs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => by simp [LetsHold.length_eq h.2.2]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

theorem LetsHold.get {bpos vpos bools bits} :
    ∀ {p : Nat} {bs : List (Name × MixedGateBinder)} {fs : List (Σ w : Nat, Term (.bits w))},
      LetsHold bpos vpos bools bits p bs fs →
      ∀ (i : Nat) (b : Name × MixedGateBinder) (f : Σ w : Nat, Term (.bits w)),
        bs[i]? = some b → fs[i]? = some f →
        posEnc bools bits (p + i) b.2 =
            (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) f.2).toNat ∧
          machWidth b.2 = f.1
  | _, _ :: _, _ :: _, h, 0, b, f, hb, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hf
    subst hb; subst hf
    exact ⟨h.1, h.2.1⟩
  | p, _ :: _, _ :: _, h, i + 1, b, f, hb, hf => by
    simp only [List.getElem?_cons_succ] at hb hf
    have := LetsHold.get h.2.2 i b f hb hf
    rw [show p + 1 + i = p + (i + 1) by omega] at this
    exact this
  | _, [], _, _, _, _, _, hb, _ => by simp at hb
  | _, _ :: _, [], h, _, _, _, _, _ => h.elim

/-! ### Bits -/

theorem or_shift_lt {a b n m : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ n) :
    a <<< n ||| b < 2 ^ (m + n) := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, Nat.pow_add]
  have : a * 2 ^ n + b < (a + 1) * 2 ^ n := by rw [Nat.add_mul]; omega
  exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ ha)

theorem or_shift_inj {a a' b b' n : Nat} (hb : b < 2 ^ n) (hb' : b' < 2 ^ n)
    (h : a <<< n ||| b = a' <<< n ||| b') : a = a' ∧ b = b' := by
  have hd : ∀ x y, y < 2 ^ n → (x <<< n ||| y) / 2 ^ n = x := by
    intro x y hy
    rw [← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq, Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hy, Nat.zero_add]
  have hm : ∀ x y, y < 2 ^ n → (x <<< n ||| y) % 2 ^ n = y := by
    intro x y hy
    rw [← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  exact ⟨by rw [← hd a b hb, h, hd a' b' hb'], by rw [← hm a b hb, h, hm a' b' hb']⟩

theorem mask_lt (w v : Nat) : mask w v < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)

/-- A field inside the low `W` bits does not see what is above them. -/
theorem field_mask {w lo W : Nat} (x : Nat) (h : lo + w ≤ W) :
    mask w (x >>> lo) = mask w (mask W x >>> lo) := by
  unfold mask
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · have : lo + i < W := by omega
    simp [hi, this]
  · simp [hi]

theorem slotNexts_congr {P Q : Nat} :
    ∀ (ps : List Port) (fs : List SlotField),
      (∀ f ∈ fs, mask f.width (P >>> f.lo) = mask f.width (Q >>> f.lo)) →
      slotNexts P ps fs = slotNexts Q ps fs
  | [], _, _ => by simp [slotNexts]
  | _ :: _, [], _ => by simp [slotNexts]
  | p :: ps, f :: fs, h => by
    simp only [slotNexts, h f List.mem_cons_self,
      slotNexts_congr ps fs (fun g hg => h g (List.mem_cons_of_mem _ hg))]

/-! ### The values on the chain of `let` fields -/

open Tools.ShippingSettledSoundness in
/-- Along the chain `w = {a₁, w₁}`, `w₁ = {a₂, w₂}`, …: when `w` holds the
packed value, every operand wire holds its field and the last wire holds
the rest. -/
theorem chain_values {we : WEnv} {R : Env} {body : List Stmt}
    (eqs : IREquations we body R) (typed : TypedStmts we body) (outZero : we "out" = 0)
    {bv : Nat → Bool} {vv : (j : Nat) → (w : Nat) → BitVec w} :
    ∀ {al : List (Port × String)} {w core : String} (fs : List (Σ w : Nat, Term (.bits w)))
      {c : Nat} (coreT : Term (.bits c)),
      LetChain body al w core →
      al.length = fs.length →
      (∀ (i : Nat) (pa : Port × String) (f : Σ w : Nat, Term (.bits w)),
        al[i]? = some pa → fs[i]? = some f → we pa.2 = f.1) →
      we w = (packLets fs coreT).1 →
      mask (we w) (R w) = (eval bv vv (packLets fs coreT).2 : BitVec _).toNat →
      (∀ (i : Nat) (pa : Port × String) (f : Σ w : Nat, Term (.bits w)),
        al[i]? = some pa → fs[i]? = some f →
        mask (we pa.2) (R pa.2) = (eval bv vv f.2 : BitVec f.1).toNat) ∧
      we core = c ∧ mask c (R core) = (eval bv vv coreT : BitVec c).toNat := by
  intro al w core fs c coreT chain
  induction chain generalizing fs with
  | nil =>
    intro hlen _ hw hv
    cases fs with
    | nil =>
      have hwc : we _ = c := hw
      refine ⟨fun i pa f ha => by simp at ha, hwc, ?_⟩
      rw [hwc] at hv; exact hv
    | cons _ _ => simp at hlen
  | @cons p a b w rest core hmem hrest ih =>
    intro hlen hwid hw hv
    cases fs with
    | nil => simp at hlen
    | cons f fs' =>
      have hwa : we a = f.1 := hwid 0 (p, a) f rfl rfl
      obtain ⟨l, e, n, heq, ht, hl⟩ := typed _ hmem
      cases heq
      have hcat : n = we a + we b ∧ 0 < we a ∧ 0 < we b := by
        cases ht with
        | cat _ _ ha hb => exact ⟨rfl, ha, hb⟩
      have hww : we w = we a + we b := by
        rcases hl with hl | hl
        · rw [hl, hcat.1]
        · rw [hl, outZero] at hw
          have : 0 < (packLets (f :: fs') coreT).1 := by
            show 0 < f.1 + _
            rw [← hwa]; exact Nat.add_pos_left hcat.2.1 _
          omega
      have hwb : we b = (packLets fs' coreT).1 := by
        have : we w = f.1 + (packLets fs' coreT).1 := hw
        omega
      have hR : R w = mask (we a) (R a) <<< we b ||| mask (we b) (R b) := by
        have := eqs _ _ hmem
        simp [evalExpr, evalExpr.go, evalList, widthOf] at this
        exact this.symm
      have hbound : R w < 2 ^ (we a + we b) := by
        rw [hR]; exact or_shift_lt (mask_lt _ _) (mask_lt _ _)
      have hval : mask (we a) (R a) <<< we b ||| mask (we b) (R b) =
          (eval bv vv f.2).toNat <<< we b ||| (eval bv vv (packLets fs' coreT).2).toNat := by
        have h1 : mask (we w) (R w) = R w := by
          unfold mask; rw [hww]; exact Nat.mod_eq_of_lt hbound
        rw [h1, hR] at hv
        rw [hv]
        show (eval bv vv f.2 ++ eval bv vv (packLets fs' coreT).2).toNat = _
        rw [BitVec.toNat_append, hwb]
      obtain ⟨hfa, hfb⟩ := or_shift_inj (mask_lt _ _)
        (by rw [hwb]; exact (eval bv vv (packLets fs' coreT).2).isLt) hval
      obtain ⟨hrestv, hc, hcore⟩ := ih fs' (by simpa using hlen)
        (fun i pa g ha hg => hwid (i + 1) pa g (by simpa using ha) (by simpa using hg))
        hwb hfb
      refine ⟨?_, hc, hcore⟩
      intro i pa g ha hg
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hg
        subst ha; subst hg
        exact hfa
      | succ i =>
        exact hrestv i pa g (by simpa using ha) (by simpa using hg)

/-! ### Environments with the `let` ports set -/

/-- `env` with port `i` of the list set to `val i`. -/
def setPorts (val : Nat → Nat) : List Port → Nat → Env → Env
  | [], _, env => env
  | p :: ps, j, env => fun z => if z = p.name then val j else setPorts val ps (j + 1) env z

theorem setPorts_frame {val : Nat → Nat} :
    ∀ (ps : List Port) (j : Nat) (env : Env) (z : String),
      (∀ p ∈ ps, z ≠ p.name) → setPorts val ps j env z = env z
  | [], _, _, _, _ => rfl
  | p :: ps, j, env, z, h => by
    simp only [setPorts, h p List.mem_cons_self, if_false]
    exact setPorts_frame ps (j + 1) env z (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem setPorts_get {val : Nat → Nat} :
    ∀ (ps : List Port) (j : Nat) (env : Env), (ps.map Port.name).Nodup →
      ∀ (i : Nat) (p : Port), ps[i]? = some p → setPorts val ps j env p.name = val (j + i)
  | [], _, _, _, i, p, h => by simp at h
  | q :: ps, j, env, nd, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [setPorts]
  | q :: ps, j, env, nd, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨hnot, nd'⟩ := List.nodup_cons.mp nd
    have hne : p.name ≠ q.name := fun heq =>
      hnot (heq ▸ List.mem_map_of_mem (List.mem_of_getElem? h))
    simp only [setPorts, hne, if_false]
    rw [setPorts_get ps (j + 1) env nd' i p h]
    congr 1; omega

theorem weOf_congr_wires {m m' : Sparkle.IR.AST.Module} (h : m'.wires = m.wires) :
    weOf m' = weOf m := by
  funext x; unfold weOf; rw [h]

/-! ## One cycle of the machine -/

/-- The packed transition value at a valuation of the binders. -/
def packedAt {srt : SType} (e : Term srt) (bpos vpos : Nat → Nat) (bools : Nat → Bool)
    (bits : (j : Nat) → (n : Nat) → BitVec n) : Nat :=
  (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat

/-- The number of the declaration's ports (its binders but the calls, slots
and `let`s, a domain binder having no port): where `closeInstsM` finds the
calls' ports. -/
def machNIn (shape : MachineShape) : Nat :=
  ((shape.binders.take (shape.binders.length - shape.insts.length - shape.layout.slots.length -
    shape.layout.lets)).filter (fun b => b.2 != .domain)).length

/-- The ports the binders of a machine transition get, in order (a domain
binder has none); their names depend on the allocator only. -/
def machPorts (declName : Name) (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
    (bs : List (Name × MixedGateBinder)) : List Port :=
  inputPorts (fun _ => false) (fun _ n => 0#n) (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)

/-- How a machine module is wired to its children in its design: the
transition's port names are distinct, the `let` wires are the last of them,
the registers are among the slot and `let` ports, every call `k` is an instance statement of the module (`CallStmt`) whose
module is what its name resolves to in the design, every instance statement
is such a call, and the body is in the linked order. -/
def MachineWired (declName : Name) (shape : MachineShape) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (regs lets : List String) : Prop :=
  let names := (machPorts declName ids cache shape.binders).map (·.name)
  let kI := shape.insts.length
  let n := shape.layout.slots.length
  let nIn := machNIn shape
  names.Nodup ∧ (∀ x ∈ names, Sparkle.IR.NameHints.Allocated x) ∧
  (∀ r ∈ regs, r ∈ names.drop (names.length - shape.layout.lets - n)) ∧
  lets = names.drop (names.length - shape.layout.lets) ∧
  (∀ k, k < kI → ∃ args mc st, (shape.insts.map (·.2.1))[k]? = some args ∧ st ∈ m.body ∧
    moduleByName dsn.modules mc.name = some mc ∧ Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st) ∧
  (∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → ∃ k args mc,
    (shape.insts.map (·.2.1))[k]? = some args ∧ moduleByName dsn.modules mn = some mc ∧
    Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc (.inst mn iname conns)) ∧
  linkedOk (moduleByName dsn.modules) m.body = true

/-- **One cycle of a compiled state machine.** The module the machine route
returns has one register per slot (`regs`, in slot order) and, on every
environment that carries the inputs' values, holds the slots' values in the
registers and has reset low, one cycle steps each register to its field of
the packed transition value `core` and drives every output port with its
field —
at any valuation of the binders that gives the `let` binders the values of
their fields (`LetsHold`). The transition's packed term is
`let₀ ++ … ++ letₖ₋₁ ++ core`. -/
def MachinePreserves (declName : Name) (shape : MachineShape)
    (bsIn slotBs letBs : List (Name × MixedGateBinder)) (m : Sparkle.IR.AST.Module)
    (dsn : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bpos vpos : Nat → Nat)
      (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
    (packLets fs core).2.WF kb kv vw →
    (∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool)) →
    (∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j))) →
    shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j)) (packLets fs core).2 →
    (∀ f ∈ shape.layout.slots, f.lo + f.width ≤ c) →
    (∀ o ∈ shape.layout.outs, o.lo + o.width ≤ c) →
    ∃ regs : List String, regs.Nodup ∧ regs.length = slotBs.length ∧
    ∃ lets : List String, lets.length = letBs.length ∧
    MachineWired declName shape ids cache m dsn regs lets ∧
    ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (env0 : Env) (mems : MEnv),
      SourceInputs declName bsIn ids cache bools bits env0 →
      (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        env0 r = posEnc bools bits (bsIn.length + i) b.2) →
      env0 "rst" = 0 →
      LetsHold bpos vpos bools bits (bsIn.length + slotBs.length) letBs fs →
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, fieldNexts (packedAt core bpos vpos bools bits) regs shape.layout.slots,
            mems) ∧
        (∀ o ∈ shape.layout.outs, envF o.name =
          mask o.width (packedAt core bpos vpos bools bits >>> o.lo)) ∧
        -- the `let` wires carry the `let` binders' values
        ∀ (j : Nat) (name : String) (b : Name × MixedGateBinder), lets[j]? = some name →
          letBs[j]? = some b → envF name = posEnc bools bits (bsIn.length + slotBs.length + j) b.2

/-- The run of `closeInstsM` is a `closeInsts` of the closed module, for SOME
children (whatever the child entry returned). -/
theorem closeInstsM_returns {shape t m₀ d₀ m d}
    (hr : MReturns (closeInstsM shape t m₀ d₀) (some (m, d))) :
    ∃ children, closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (m₀, d₀) = some (m, d) := by
  unfold closeInstsM at hr
  obtain ⟨synth?, _, hr⟩ := MReturns.bind hr
  cases synth? with
  | none =>
    have := MReturns.pure hr
    cases this
  | some synth =>
    dsimp only at hr
    obtain ⟨children, _, hr⟩ := MReturns.bind hr
    have := MReturns.pure hr
    exact ⟨children, this.symm⟩

/-- A run of the machine synthesis: the harness, `closeLets`, `closeMachine`,
and — for a shape with `@[hardware_module]` calls — `closeInsts` with some
children. -/
theorem synthesizeMachineCertified_returns {logProf declName shape m d}
    (hr : MReturns (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
      (some (m, d))) :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire e hint top named) logProf declName
        shape.binders shape.body) (t, d₀) ∧
      closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children, closeInsts (machNIn shape) shape.insts.length
          shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
          (closeMachine shape.layout t', d₀) = some (m, d))) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, run, hr⟩ := MReturns.bind hr
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := MReturns.pure hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      obtain ⟨children, hc⟩ := closeInstsM_returns hr
      exact ⟨t, t', d', run, hcl, Or.inr ⟨by rw [hi]; exact List.cons_ne_nil _ _, children, hc⟩⟩
  · have eq := MReturns.pure hr
    cases eq

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

theorem typedRef_width {we : WEnv} {x : String} {n : Nat} (h : TypedExpr we (.ref x) n) :
    n = we x := by
  cases h with
  | ref _ _ => rfl

theorem kindTy_bitWidth (k : MixedGateBinder) (h : k ≠ .domain) :
    (kindTy k).bitWidth = machWidth k := by
  cases k with
  | domain => exact absurd rfl h
  | bool => rfl
  | bits n => rfl

set_option maxHeartbeats 4000000 in
open Tools.ShippingSettledSoundness in
/-- **The machine route preserves one cycle.** -/
theorem synthesizeMachineCertified_sound {logProf declName shape m d}
    {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : MReturns (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
      (some (m, d)))
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreserves declName shape bsIn slotBs letBs m d := by
  obtain ⟨t, t', d₀, hrun, hcl, hmt⟩ := synthesizeMachineCertified_returns hr
  -- the module is the closed transition, or `closeInsts` of it
  have hmt : (shape.insts = [] ∧ m = closeMachine shape.layout t') ∨
      ∃ children : List (Sparkle.IR.AST.Module × Design),
        closeInsts (machNIn shape) shape.insts.length shape.layout.slots.length
          (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
          (closeMachine shape.layout t', d₀) = some (m, d) := by
    rcases hmt with ⟨hi, h, _⟩ | ⟨_, children, h⟩
    · exact Or.inl ⟨hi, h⟩
    · exact Or.inr ⟨children, h⟩
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns hrun
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos fs c core he hb hv hbody hfit houtfit
  obtain ⟨raw, ⟨B, w, hB⟩, hinputs⟩ := transition_facts nd len run hm nameLegal he hb hv hbody
  -- The binder list splits into inputs, slots and lets; so do the ids.
  let a := start (entryCompilerState false cache) declName.toString
  let k := bsIn.length
  let n := slotBs.length
  let K := letBs.length
  have hlen : ids.length = k + n + K := by
    show ids.length = bsIn.length + slotBs.length + letBs.length
    rw [len, hbs]; simp only [List.length_append]
  let idsIn := ids.take k
  let idsS := (ids.drop k).take n
  let idsL := ids.drop (k + n)
  have hids : ids = idsIn ++ idsS ++ idsL := by
    simp only [idsIn, idsS, idsL]
    rw [← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]
  have lenIn : idsIn.length = bsIn.length := by simp [idsIn, k]; omega
  have lenS : idsS.length = slotBs.length := by simp [idsS, n, k]; omega
  have lenL : idsL.length = letBs.length := by simp [idsL, K, k, n]; omega
  have hzip : shape.binders.zip ids =
      bsIn.zip idsIn ++ slotBs.zip idsS ++ letBs.zip idsL := by
    conv => lhs; rw [hbs, hids]
    rw [List.zip_append (by simp [lenIn, lenS]), List.zip_append lenIn.symm]
  have slotNoDom : ∀ b ∈ slotBs.zip idsS, b.1.2 ≠ .domain :=
    fun b hb => slotKinds b.1 (List.of_mem_zip hb).1
  have letNoDom : ∀ b ∈ letBs.zip idsL, b.1.2 ≠ .domain :=
    fun b hb => letKinds b.1 (List.of_mem_zip hb).1
  -- The ports, at the zero valuation.
  let zb : FVarId → Bool := fun _ => false
  let zv : (id : FVarId) → (n : Nat) → BitVec n := fun _ n => 0#n
  let a1 := prepare zb zv (bsIn.zip idsIn) a
  let a2 := prepare zb zv (slotBs.zip idsS) a1
  let P1 := inputPorts zb zv (bsIn.zip idsIn) a
  let ps := inputPorts zb zv (slotBs.zip idsS) a1
  let ls := inputPorts zb zv (letBs.zip idsL) a2
  have psTypes := inputPorts_types (bools := zb) (bits := zv) (slotBs.zip idsS) a1 slotNoDom
  have lsTypes := inputPorts_types (bools := zb) (bits := zv) (letBs.zip idsL) a2 letNoDom
  have psLen : ps.length = slotBs.length := by
    rw [psTypes.length_eq, List.length_zip, lenS, Nat.min_self]
  have lsLen : ls.length = letBs.length := by
    rw [lsTypes.length_eq, List.length_zip, lenL, Nat.min_self]
  have slotsLen : shape.layout.slots.length = slotBs.length := layW.length_eq
  have tInputs : t.inputs = P1 ++ ps ++ ls := by
    rw [hinputs zb zv, hzip, inputPorts_append, inputPorts_append, prepare_append]
  have hdropL : t.inputs.drop (t.inputs.length - shape.layout.lets) = ls := by
    rw [hlets, tInputs, List.length_append, lsLen, Nat.add_sub_cancel, List.drop_left]
  have htakeL : t.inputs.take (t.inputs.length - shape.layout.lets) = P1 ++ ps := by
    rw [hlets, tInputs, List.length_append, lsLen, Nat.add_sub_cancel, List.take_left]
  -- Facts of the transition module that do not depend on the cycle.
  have zero : SourceInputs declName shape.binders ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  obtain ⟨_, _, _, ready, _, hwe0, _, _, base⟩ := raw _ _ _ (fun _ _ => 0) zero
  have pb := base positive
  have inNodup := pb.inputNames
  have namesNodup := pb.inputNames
  rw [tInputs, List.map_append, List.map_append] at inNodup
  have psNodup : (ps.map Port.name).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp inNodup).1).2.1
  have lsNodup : (ls.map Port.name).Nodup := (List.nodup_append.mp inNodup).2.1
  have lsDisj : ∀ p ∈ P1 ++ ps, ∀ q ∈ ls, p.name ≠ q.name := by
    intro p hp q hq
    have := (List.nodup_append.mp inNodup).2.2
    exact this p.name (by rw [← List.map_append]; exact List.mem_map_of_mem hp) q.name
      (List.mem_map_of_mem hq)
  have portWidth : ∀ p ∈ t.inputs, weOf t p.name = match p.ty with
      | .bitVector k => k
      | .bit => 1
      | _ => 0 := fun p hp => weOf_of_port ready.wiresNodup (pb.inputWires p hp)
  have corePos : 0 < c := core.wf_pos (packLets_wf fs core he)
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hB]
  have outW : weOf t w = (packLets fs core).1 := by
    exact (typedRef_width (pb.outputTyped (.ref w) (by rw [hB]; simp))).symm
  -- The let-closed transition module.
  have closed : ∃ B' coreW, t'.body = B' ++ [.assign "out" (.ref coreW)] ∧
      TypedStmts (weOf t') t'.body ∧ t'.wires = t.wires ∧ t'.inputs = P1 ++ ps ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (env0 : Env)
        (mems : MEnv),
        SourceInputs declName bsIn ids cache bools bits env0 →
        (∀ i p b, ps[i]? = some p → slotBs[i]? = some b →
          env0 p.name = posEnc bools bits (bsIn.length + i) b.2) →
        LetsHold bpos vpos bools bits (bsIn.length + slotBs.length) letBs fs →
        ∃ R', evalAssigns (weOf t') mems t'.body env0 = some R' ∧
          mask c (R' "out") = packedAt core bpos vpos bools bits ∧
          ∀ (i : Nat) (p : Port) (b : Name × MixedGateBinder), ls[i]? = some p →
            letBs[i]? = some b → R' p.name = posEnc bools bits (bsIn.length + slotBs.length + i) b.2 := by
    -- the cycle's environment with the let ports set carries every binder's value
    have full : ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (env0 : Env),
        SourceInputs declName bsIn ids cache bools bits env0 →
        (∀ i p b, ps[i]? = some p → slotBs[i]? = some b →
          env0 p.name = posEnc bools bits (bsIn.length + i) b.2) →
        SourceInputs declName shape.binders ids cache bools bits
          (setPorts (fun j => posEnc bools bits (k + n + j) ((letBs[j]?.map (·.2)).getD .domain))
            ls 0 env0) := by
      intro bools bits env0 inputs slotVals
      have frame : ∀ p ∈ P1 ++ ps, setPorts (fun j => posEnc bools bits (k + n + j)
          ((letBs[j]?.map (·.2)).getD .domain)) ls 0 env0 p.name = env0 p.name :=
        fun p hp => setPorts_frame ls 0 env0 p.name (fun q hq => lsDisj p hp q hq)
      have idxAt : ∀ (off i : Nat) (id : FVarId), (ids.drop off)[i]? = some id →
          ids.idxOf id = off + i := by
        intro off i id hget
        rw [List.getElem?_drop] at hget
        have hlt : off + i < ids.length := (List.getElem?_eq_some_iff.mp hget).1
        have hg : ids[off + i]! = id := by simp [List.getElem!_eq_getElem?_getD, hget]
        rw [← hg]
        exact index_fresh ids nd (off + i) hlt
      unfold SourceInputs
      rw [hzip, admissible_append, admissible_append]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h1 : Admissible (boolValues ids bools) (bitValues ids bits) env0 (bsIn.zip idsIn) a := by
          have := inputs
          unfold SourceInputs at this
          rwa [zip_take_length] at this
        refine admissible_env_congr _ _ (fun p hp => ?_) h1
        apply frame
        refine List.mem_append_left _ ?_
        rw [show inputPorts (boolValues ids bools) (bitValues ids bits) (bsIn.zip idsIn) a = P1
          from inputPorts_congr _ _ _ rfl] at hp
        exact hp
      · apply admissible_of_ports _ _ slotNoDom
        rw [show inputPorts (boolValues ids bools) (bitValues ids bits) (slotBs.zip idsS)
            (prepare (boolValues ids bools) (bitValues ids bits) (bsIn.zip idsIn) a) = ps from
          inputPorts_congr _ _ _ (prepare_state_congr _ _ _ rfl)]
        apply Zip₂.of_get (by rw [psLen, List.length_zip, lenS, Nat.min_self])
        intro i p b hp hb
        obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hb
        rw [frame p (List.mem_append_right _ (List.mem_of_getElem? hp)),
          slotVals i p b.1 hp hb1]
        have hidx : ids.idxOf b.2 = k + i := by
          apply idxAt k i
          have : idsS[i]? = some b.2 := hb2
          simp only [idsS, List.getElem?_take] at this
          split at this
          · exact this
          · cases this
        obtain ⟨⟨name, kind⟩, id⟩ := b
        cases kind <;> simp [binderEnc, posEnc, boolValues, bitValues, hidx, k] at hidx ⊢
      · apply admissible_of_ports _ _ letNoDom
        rw [show inputPorts (boolValues ids bools) (bitValues ids bits) (letBs.zip idsL)
            (prepare (boolValues ids bools) (bitValues ids bits)
              (bsIn.zip idsIn ++ slotBs.zip idsS) a) = ls from
          inputPorts_congr _ _ _ (by
            rw [prepare_append]
            exact prepare_state_congr _ _ _ (prepare_state_congr _ _ _ rfl))]
        apply Zip₂.of_get (by rw [lsLen, List.length_zip, lenL, Nat.min_self])
        intro i p b hp hb
        obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hb
        rw [setPorts_get ls 0 env0 lsNodup i p hp]
        have hidx : ids.idxOf b.2 = k + n + i := idxAt (k + n) i b.2 hb2
        obtain ⟨⟨name, kind⟩, id⟩ := b
        simp only [Nat.zero_add, hb1, Option.map_some, Option.getD_some]
        cases kind <;> simp [binderEnc, posEnc, boolValues, bitValues, hidx] at hidx ⊢
    by_cases hK : shape.layout.lets = 0
    · -- no let: the transition module itself
      have hfs : letBs = [] := by
        rw [hlets] at hK; exact List.length_eq_zero_iff.mp hK
      have hcl' : t' = t := by
        rw [hK] at hcl
        simp [closeLets] at hcl
        exact hcl.symm
      subst hcl'
      have lsNil : ls = [] := by
        apply List.length_eq_zero_iff.mp; rw [lsLen, hfs]; rfl
      refine ⟨B, w, hB, ready.typed, rfl, by rw [tInputs, lsNil, List.append_nil], ?_⟩
      intro bools bits env0 mems inputs slotVals hold
      have hfs' : fs = [] := by
        have := hold.length_eq
        rw [hfs] at this
        exact List.length_eq_zero_iff.mp this.symm
      have values := full bools bits env0 inputs slotVals
      rw [lsNil] at values
      obtain ⟨result, hres, hval, _, _, hwe, _, _, _⟩ := raw bools bits env0 mems values
      rw [← hwe] at hres
      refine ⟨result, hres, ?_, fun i p b hp => by rw [lsNil] at hp; simp at hp⟩
      subst hfs'
      rw [hval]
      exact Nat.mod_eq_of_lt
        (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) core).isLt
    · -- lets: tie the ports to the operand wires of their fields
      obtain ⟨w0, aliases, coreW, hpw0, hops, hwid, hcoreOut, hnw⟩ := closeLets_some hK hcl
      rw [hpw] at hpw0; cases hpw0
      rw [hdropL] at hops
      obtain ⟨chain, hmap⟩ := letOperands_chain ls w hops
      have alLen : aliases.length = ls.length := by rw [← hmap, List.length_map]
      have aliasPort : ∀ (i : Nat) (pa : Port × String), aliases[i]? = some pa →
          ls[i]? = some pa.1 := by
        intro i pa hpa
        rw [← hmap, List.getElem?_map, hpa]; rfl
      have aliasMem : ∀ pa ∈ aliases, pa.1 ∈ ls := by
        intro pa hpa
        rw [← hmap]; exact List.mem_map_of_mem hpa
      have portBits : ∀ (i : Nat) (p : Port) (b : Name × MixedGateBinder),
          ls[i]? = some p → letBs[i]? = some b →
          p.ty.bitWidth = machWidth b.2 ∧ weOf t p.name = machWidth b.2 := by
        intro i p b hp hb
        have hi : i < idsL.length := by
          have := (List.getElem?_eq_some_iff.mp hb).1; omega
        have hbz : (letBs.zip idsL)[i]? = some (b, idsL[i]) := by
          rw [List.getElem?_zip_eq_some]
          exact ⟨hb, List.getElem?_eq_getElem hi⟩
        have hty := lsTypes.get i p _ hp hbz
        have hnd := letKinds b (List.mem_of_getElem? hb)
        have hpin : p ∈ t.inputs := by
          rw [tInputs]; exact List.mem_append_right _ (List.mem_of_getElem? hp)
        have hw := portWidth p hpin
        rw [hty] at hw ⊢
        refine ⟨kindTy_bitWidth _ hnd, ?_⟩
        rw [hw]
        revert hnd
        cases b.2 with
        | domain => intro h; exact absurd rfl h
        | bool => intro _; rfl
        | bits n => intro _; rfl
      -- structure of the closed module, from one evaluation at the zero valuation
      have hportA : ∀ pa ∈ aliases, weOf t pa.1.name = pa.1.ty.bitWidth := by
        intro pa hpa
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hpa
        have hpa' : aliases[i]? = some pa := by rw [List.getElem?_eq_getElem hi, hget]
        have hlsi := aliasPort i pa hpa'
        have hib : i < letBs.length := by rw [← lsLen, ← alLen]; exact hi
        obtain ⟨h1, h2⟩ := portBits i pa.1 letBs[i] hlsi (List.getElem?_eq_getElem hib)
        rw [h1, h2]
      have perCycle : ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
          (env0 : Env) (mems : MEnv),
          SourceInputs declName bsIn ids cache bools bits env0 →
          (∀ i p b, ps[i]? = some p → slotBs[i]? = some b →
            env0 p.name = posEnc bools bits (bsIn.length + i) b.2) →
          LetsHold bpos vpos bools bits (bsIn.length + slotBs.length) letBs fs →
          weOf t coreW = c ∧
          ∃ R', evalAssigns (weOf t') mems t'.body env0 = some R' ∧
            mask c (R' "out") = packedAt core bpos vpos bools bits ∧
            ∀ (i : Nat) (p : Port) (b : Name × MixedGateBinder), ls[i]? = some p →
              letBs[i]? = some b →
              R' p.name = posEnc bools bits (bsIn.length + slotBs.length + i) b.2 := by
        intro bools bits env0 mems inputs slotVals hold
        have values := full bools bits env0 inputs slotVals
        obtain ⟨R, hres, hval, ready', _, hwe, _, _, _⟩ := raw bools bits _ mems values
        rw [← hwe] at hres
        have eqs := assign_equations pb.order hres
        have hRw : R w = R "out" := by
          have := eqs "out" (.ref w) (by rw [hB]; simp)
          simpa [evalExpr] using this
        have fsLen : letBs.length = fs.length := hold.length_eq
        have widths : ∀ (i : Nat) (pa : Port × String) (f : Σ w : Nat, Term (.bits w)),
            aliases[i]? = some pa → fs[i]? = some f → weOf t pa.2 = f.1 := by
          intro i pa f hpa hf
          have hib : i < letBs.length := by
            have := (List.getElem?_eq_some_iff.mp hf).1; omega
          obtain ⟨h1, _⟩ := portBits i pa.1 letBs[i] (aliasPort i pa hpa)
            (List.getElem?_eq_getElem hib)
          have h2 := (hold.get i letBs[i] f (List.getElem?_eq_getElem hib) hf).2
          rw [show weOf t pa.2 = wireWidth t.wires pa.2 from rfl,
            (hwid pa (List.mem_of_getElem? hpa)).1, h1, h2]
        obtain ⟨hfields, hcw, hcorev⟩ := chain_values (bv := fun j => bools (bpos j))
          (vv := fun j w => bits (vpos j) w) eqs ready'.typed ready'.outWidthZero fs core chain
          (by rw [alLen, lsLen, fsLen]) widths outW
          (by
            rw [hRw, hval, outW]
            exact Nat.mod_eq_of_lt
              (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w)
                (packLets fs core).2).isLt)
        refine ⟨hcw, ?_⟩
        obtain ⟨_, _, _, _, R', hev, hout, hframe⟩ := closeLets_eval (env0 := env0) hK hcl hpw
          (by rw [hdropL]; exact hops) pb.order ready'.typed ready'.outWidthZero hres
          (fun z hz => setPorts_frame ls 0 env0 z (fun q hq => by
            obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hq
            have hia : i < aliases.length := by rw [alLen]; exact hi
            have := aliasPort i aliases[i] (List.getElem?_eq_getElem hia)
            rw [List.getElem?_eq_getElem hi, hget] at this
            have hq' : q = aliases[i].1 := Option.some.inj this
            rw [hq']
            exact hz aliases[i] (List.getElem_mem hia)))
          (by
            intro pa hpa
            obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hpa
            have hpa' : aliases[i]? = some pa := by rw [List.getElem?_eq_getElem hi, hget]
            have hib : i < letBs.length := by rw [← lsLen, ← alLen]; exact hi
            have hif : i < fs.length := by omega
            rw [setPorts_get ls 0 env0 lsNodup i pa.1 (aliasPort i pa hpa')]
            obtain ⟨hh, _⟩ := hold.get i letBs[i] fs[i] (List.getElem?_eq_getElem hib)
              (List.getElem?_eq_getElem hif)
            have hfv := hfields i pa fs[i] hpa' (List.getElem?_eq_getElem hif)
            have hwpa := widths i pa fs[i] hpa' (List.getElem?_eq_getElem hif)
            obtain ⟨h1, _⟩ := portBits i pa.1 letBs[i] (aliasPort i pa hpa')
              (List.getElem?_eq_getElem hib)
            have h2 := (hold.get i letBs[i] fs[i] (List.getElem?_eq_getElem hib)
              (List.getElem?_eq_getElem hif)).2
            simp only [Nat.zero_add, List.getElem?_eq_getElem hib, Option.map_some,
              Option.getD_some]
            rw [show k + n + i = bsIn.length + slotBs.length + i from rfl, hh, ← hfv, hwpa,
              h1, h2])
        refine ⟨R', hev, by rw [hout]; exact hcorev, ?_⟩
        -- a `let` port: not written by the transition, so it keeps its value
        intro i p b hp hb
        have hia : i < aliases.length := by
          rw [alLen]; exact (List.getElem?_eq_some_iff.mp hp).1
        have hpa := aliasPort i aliases[i] (List.getElem?_eq_getElem hia)
        rw [hp] at hpa
        have hpe : p = aliases[i].1 := Option.some.inj hpa
        obtain ⟨hno, hnwr⟩ := hnw aliases[i] (List.getElem_mem hia)
        rw [← hpe] at hno hnwr
        have hseq : Tools.ShippingRegisterSoundness.SeqBody t.body := fun st hs => by
          have := ready'.typed st hs
          obtain ⟨l, e, n, heq, _⟩ := this
          exact Or.inl ⟨l, e, heq⟩
        rw [hframe p.name hno, Tools.ShippingRegisterSoundness.evalAssigns_preserved hseq hres hnwr,
          setPorts_get ls 0 env0 lsNodup i p hp]
        simp only [Nat.zero_add, hb, Option.map_some, Option.getD_some]
        rfl
      -- the structural facts
      obtain ⟨hin', hwires', ⟨B', hB'⟩, _⟩ : t'.inputs = t.inputs.take (t.inputs.length -
          shape.layout.lets) ∧ t'.wires = t.wires ∧
          (∃ B', t'.body = B' ++ [.assign "out" (.ref coreW)]) ∧ True := by
        have hc := hcl
        unfold closeLets at hc
        simp only [hK, if_false, hpw, show letOperands t.body
          (t.inputs.drop (t.inputs.length - shape.layout.lets)) w = some (aliases, coreW) from
          by rw [hdropL]; exact hops] at hc
        split at hc
        · cases hc
          exact ⟨rfl, rfl, ⟨_, by rw [List.append_assoc]⟩, trivial⟩
        · cases hc
      have typed' := closeLets_typed hK hcl hpw (by rw [hdropL]; exact hops) ready.typed
        hportA (chain_core_pos ready.typed chain (by
          intro h
          rw [h] at alLen
          have : letBs.length = 0 := by rw [← lsLen, ← alLen]; rfl
          exact hK (by rw [hlets, this])))
      refine ⟨B', coreW, hB', typed', hwires', by rw [hin', htakeL], ?_⟩
      intro bools bits env0 mems inputs slotVals hold
      exact (perCycle bools bits env0 mems inputs slotVals hold).2
  obtain ⟨B', coreW, hB', typed', hwires', hin', cycle⟩ := closed
  have hweq : weOf t' = weOf t := weOf_congr_wires hwires'
  have psMem : ∀ p ∈ ps, p ∈ t.wires := fun p hp =>
    pb.inputWires p (by rw [tInputs]; exact List.mem_append_left _ (List.mem_append_right _ hp))
  have hdrop : t'.inputs.drop (t'.inputs.length - shape.layout.slots.length) = ps := by
    rw [hin', List.length_append, slotsLen, psLen, Nat.add_sub_cancel, List.drop_left]
  have slotsOk : Zip₂ (SlotOk (weOf t')) ps shape.layout.slots := by
    apply Zip₂.of_get (by rw [psLen, slotsLen])
    intro i p f hp hf
    have hi : i < slotBs.length := by
      have := (List.getElem?_eq_some_iff.mp hp).1; omega
    have hid : i < idsS.length := by omega
    have hbz : (slotBs.zip idsS)[i]? = some (slotBs[i], idsS[i]) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hid⟩
    have hty := psTypes.get i p _ hp hbz
    have hw := layW.get i f _ hf (List.getElem?_eq_getElem hi)
    have hmem : p ∈ ps := List.mem_of_getElem? hp
    have hwe := weOf_of_port ready.wiresNodup (psMem p hmem)
    have hnd := slotKinds _ (List.getElem_mem hi)
    rw [hty] at hwe
    rw [hweq]
    revert hwe hw hnd
    generalize hkind : (slotBs[i]).2 = kind
    have hpos : ∀ n, kind = .bits n → 0 < n := by
      intro n hn
      refine positive (slotBs[i]).1 n ?_
      rw [hbs]
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      have : slotBs[i] = ((slotBs[i]).1, MixedGateBinder.bits n) := by
        rw [← hn, ← hkind]
      rw [← this]
      exact List.getElem_mem hi
    intro hwe hw hnd
    cases kind with
    | domain => exact absurd rfl hnd
    | bool => exact ⟨by rw [hw, hwe]; rfl, by rw [hwe]; exact Nat.one_pos⟩
    | bits n => exact ⟨by rw [hw, hwe]; rfl, by rw [hwe]; exact hpos n rfl⟩
  -- the wiring of the instances
  have hmp : machPorts declName ids cache shape.binders = t.inputs := (hinputs _ _).symm
  have plain0 : (closeMachine shape.layout t').body.all Tools.ShippingMachineInst.plainStmt =
      true := Tools.ShippingMachineInst.closeMachine_plain _ _ typed'.isAssign
  have notInst0 : ∀ st ∈ (closeMachine shape.layout t').body,
      Sparkle.IR.Machine.isInst st = true → False := by
    intro st hs hi
    have := List.all_eq_true.mp plain0 st hs
    cases st <;> simp_all [Tools.ShippingMachineInst.plainStmt, Sparkle.IR.Machine.isInst]
  have wired : MachineWired declName shape ids cache m d (ps.map Port.name) (ls.map Port.name) := by
    dsimp only [MachineWired]
    rw [hmp]
    refine ⟨namesNodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact pb.wireNames p (pb.inputWires p hp)
    · intro r hr
      have e : (t.inputs.map Port.name).length - shape.layout.lets - shape.layout.slots.length =
          (P1.map Port.name).length := by
        rw [tInputs]; simp only [List.length_map, List.length_append]
        rw [hlets, slotsLen, ← lsLen, ← psLen]; omega
      rw [e, tInputs, List.map_append, List.map_append, List.append_assoc, List.drop_left]
      exact List.mem_append_left _ hr
    · rw [← List.map_drop, List.length_map, hdropL]
    · intro k hk
      rcases hmt with ⟨hi, _⟩ | ⟨children, hci⟩
      · rw [hi] at hk; exact absurd hk (Nat.not_lt_zero k)
      · obtain ⟨args, child, mc, hargs, _, hmc, st, hst, hcall⟩ :=
          Tools.ShippingMachineInst.closeInsts_calls hci k (by simpa using hk)
        refine ⟨args, mc, st, hargs, hst, ?_, hcall⟩
        rw [Tools.ShippingMachineInst.moduleByName_name hmc]; exact hmc
    · intro mn iname conns hst
      rcases hmt with ⟨_, hm'⟩ | ⟨children, hci⟩
      · subst hm'; exact absurd rfl (notInst0 _ hst)
      · rcases Tools.ShippingMachineInst.closeInsts_insts hci _ hst rfl with h0 |
          ⟨k, args, child, mc, hargs, _, hmc, hcall⟩
        · exact absurd rfl (notInst0 _ h0)
        · refine ⟨k, args, mc, hargs, ?_, hcall⟩
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hst'⟩ := hcall
          cases hst'
          rw [Tools.ShippingMachineInst.moduleByName_name hmc]; exact hmc
    · rcases hmt with ⟨_, hm'⟩ | ⟨children, hci⟩
      · subst hm'; exact Tools.ShippingMachineInst.linkedOk_plain _ _ plain0
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlink⟩ :=
          Tools.ShippingMachineInst.closeInsts_some hci
        exact hlink
  refine ⟨ps.map Port.name, psNodup, by rw [List.length_map, psLen], ls.map Port.name,
    by rw [List.length_map, lsLen], wired, ?_⟩
  intro bools bits env0 mems inputs slotVals hrst hold
  obtain ⟨R', hev, hcore, hletv⟩ := cycle bools bits env0 mems inputs
    (fun i p b hp hb => slotVals i p.name b (by simp [hp]) hb) hold
  obtain ⟨envF, hstep, hout, hkeep⟩ := closeMachine_step (lay := shape.layout) hB' typed'
    (fun p hp => pb.wireNames p (hwires' ▸ hp))
    (fun p hp => by
      rw [hwires']
      exact pb.inputWires p (by
        rw [tInputs]; rw [hin'] at hp; exact List.mem_append_left _ hp))
    (by
      rw [hin', List.map_append]
      exact (List.nodup_append.mp inNodup).1)
    (by rw [hdrop]; exact slotsOk) outsOk outsNodup hev hrst
  rw [hdrop, slotNexts_congr ps shape.layout.slots (Q := packedAt core bpos vpos bools bits)
    (fun f hf => by
      rw [field_mask (R' "out") (hfit f hf), hcore]), slotNexts_eq] at hstep
  -- the `let` wires keep the transition's values
  have hlets : ∀ (j : Nat) (name : String) (b : Name × MixedGateBinder),
      (ls.map Port.name)[j]? = some name → letBs[j]? = some b →
      envF name = posEnc bools bits (bsIn.length + slotBs.length + j) b.2 := by
    intro j name b hn hb
    rw [List.getElem?_map] at hn
    cases hp : ls[j]? with
    | none => rw [hp] at hn; cases hn
    | some p =>
      rw [hp] at hn
      cases hn
      have hpin : p ∈ ls := List.mem_of_getElem? hp
      have alloc : Sparkle.IR.NameHints.Allocated p.name :=
        pb.wireNames p (pb.inputWires p (by rw [tInputs]; exact List.mem_append_right _ hpin))
      rw [hkeep p.name (fun h => Tools.ShippingRegisterSoundness.not_allocated_out (h ▸ alloc))
        (fun x h => nextName_not_allocated x (h ▸ alloc))
        (fun hmem => by
          obtain ⟨o, ho, heq⟩ := List.mem_map.mp hmem
          exact (outNameOk_facts (outsOk o ho).2).1 (heq ▸ alloc)),
        hletv j p b hp hb]
  rcases hmt with ⟨_, hmt⟩ | ⟨children, hci⟩
  · subst hmt
    refine ⟨envF, hstep, fun o ho => ?_, hlets⟩
    rw [hout o ho, field_mask (R' "out") (houtfit o ho), hcore]
  · have hw : weOf m = weOf (closeMachine shape.layout t') := by
      obtain ⟨hwires, _⟩ := Tools.ShippingMachineInst.closeInsts_some hci
      funext x
      unfold weOf
      rw [hwires]
    rw [hw, Tools.ShippingMachineInst.stepModule_of_closeInsts hci]
    refine ⟨envF, hstep, fun o ho => ?_, hlets⟩
    rw [hout o ho, field_mask (R' "out") (houtfit o ho), hcore]

/-! ## The trace -/

/-- **The trace of a compiled state machine.** Let `bools τ`, `bits τ` be a
valuation of the binders over time — inputs, slots and `let`s alike — whose
slot values start in the registers' state and follow the transition, and
whose `let` values are the values of their fields. Then a `T`-cycle run of
the emitted module, seeded each cycle with the inputs of that cycle over the
register state and with reset low, succeeds, and cycle `j` drives `out` with
the result field of the transition at time `j`. -/
theorem machine_trace {declName shape m dsn} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (h : MachinePreserves declName shape bsIn slotBs letBs m dsn)
    (slotsLen : shape.layout.slots.length = slotBs.length) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bpos vpos : Nat → Nat)
        (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
      (packLets fs core).2.WF kb kv vw →
      (∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool)) →
      (∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j))) →
      shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
        (fun j => inputExpr shape.binders.length (vpos j)) (packLets fs core).2 →
      (∀ f ∈ shape.layout.slots, f.lo + f.width ≤ c) →
      (∀ o ∈ shape.layout.outs, o.lo + o.width ≤ c) →
      ∃ regs : List String, regs.Nodup ∧ regs.length = slotBs.length ∧
      ∃ lets : List String, lets.length = letBs.length ∧
      MachineWired declName shape ids cache m dsn regs lets ∧
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
            mask f.width (packedAt core bpos vpos (bools τ) (bits τ) >>> f.lo)) →
        (∀ τ, LetsHold bpos vpos (bools τ) (bits τ) (bsIn.length + slotBs.length) letBs fs) →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          (∀ j (hj : j < envs.length), ∀ o ∈ shape.layout.outs, (envs[j]'hj) o.name =
            mask o.width (packedAt core bpos vpos (bools j) (bits j) >>> o.lo)) ∧
          ∀ j (hj : j < envs.length) (k : Nat) (name : String) (b : Name × MixedGateBinder),
            lets[k]? = some name → letBs[k]? = some b →
            (envs[j]'hj) name = posEnc (bools j) (bits j) (bsIn.length + slotBs.length + k) b.2 := by
  obtain ⟨ids, nd, len, cache, h⟩ := h
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos fs c core he hb hv hbody hfit houtfit
  obtain ⟨regs, regsNd, regsLen, lets, letsLen, wired, step⟩ :=
    h dom kb kv vw bpos vpos fs core he hb hv hbody hfit houtfit
  refine ⟨regs, regsNd, regsLen, lets, letsLen, wired, ?_⟩
  intro T bools bits seed st0 mems inputs pass rst init follow hold
  -- `k` cycles remain; the state holds the slots' values at time `T - k`.
  suffices main : ∀ (k : Nat), k ≤ T → ∀ (st : String → Nat),
      (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        st r = posEnc (bools (T - k)) (bits (T - k)) (bsIn.length + i) b.2) →
      ∃ envs, runModule (weOf m) m.body seed k st mems = some envs ∧ envs.length = k ∧
        (∀ j (hj : j < envs.length), ∀ o ∈ shape.layout.outs, (envs[j]'hj) o.name =
          mask o.width
            (packedAt core bpos vpos (bools (T - k + j)) (bits (T - k + j)) >>> o.lo)) ∧
        ∀ j (hj : j < envs.length) (q : Nat) (name : String) (b : Name × MixedGateBinder),
          lets[q]? = some name → letBs[q]? = some b →
          (envs[j]'hj) name =
            posEnc (bools (T - k + j)) (bits (T - k + j)) (bsIn.length + slotBs.length + q) b.2 by
    obtain ⟨envs, hrun, hlen, hobs, hlet⟩ := main T (Nat.le_refl T) st0 (by simpa using init)
    refine ⟨envs, hrun, hlen, fun j hj o ho => ?_, fun j hj q name b hn hb => ?_⟩
    · simpa using hobs j hj o ho
    · simpa using hlet j hj q name b hn hb
  intro k
  induction k with
  | zero => intro _ st _; exact ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro hk st inv
    have hτ : T - 1 - k = T - (k + 1) := by omega
    obtain ⟨envF, hstep, hout, hletF⟩ := step (bools (T - (k + 1))) (bits (T - (k + 1)))
      (seed k st) mems (hτ ▸ inputs k st (by omega))
      (fun i r b hr hb' => by
        rw [pass k st r (List.mem_of_getElem? hr)]; exact inv i r b hr hb')
      (rst k st) (hold _)
    have inv' : ∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        applyNexts st (fieldNexts (packedAt core bpos vpos (bools (T - (k + 1)))
          (bits (T - (k + 1)))) regs shape.layout.slots) r =
          posEnc (bools (T - k)) (bits (T - k)) (bsIn.length + i) b.2 := by
      intro i r b hr hb'
      have hi : i < shape.layout.slots.length := by
        have := (List.getElem?_eq_some_iff.mp hb').1; omega
      rw [applyNexts_fieldNexts regsNd i r _ hr (List.getElem?_eq_getElem hi)]
      have hT : T - k = T - (k + 1) + 1 := by omega
      rw [hT]
      exact (follow (T - (k + 1)) i _ b (List.getElem?_eq_getElem hi) hb').symm
    obtain ⟨rest, hrun, hlen, hobs, hletR⟩ := ih (by omega) _ inv'
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_, ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj o ho
      cases j with
      | zero => simpa using hout o ho
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hobs i hi o ho]
        have hidx : T - k + i = T - (k + 1) + (i + 1) := by
          have : i < k := by omega
          omega
        rw [hidx]
    · intro j hj q name b hn hb
      cases j with
      | zero => simpa using hletF q name b hn hb
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hletR i hi q name b hn hb]
        have hidx : T - k + i = T - (k + 1) + (i + 1) := by
          have : i < k := by omega
          omega
        rw [hidx]

/-! ## The real entry -/

theorem RunsTo.pure_eq {α : Type} {a b : α} {mctx mref cctx cref w w'}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a :=
  MReturns.pure h.mreturns

/-- A constant both certified gates refuse: the entry reads the environment
again, and when the constant is a machine shape it runs the machine
synthesis of that shape; when that returns a module, it is the run's. -/
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
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧
          ∀ res, r = some res → res = (m, d) := by
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
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, _, hmach, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm

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
      (userInliner envR) (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (structEnv envR') = some shape

/-- **The `let` boundary.** In this run the machine synthesis of `shape`
ties every `let` port to its field (`closeLets` accepts the transition
module it compiled), so the run does not fall back to the legacy route. For a
shape without `let`s this holds of every run (`machineCloses_of_noLets`). -/
def MachineCloses (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ (logProf : String → IO Unit) w r w',
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
      mctx mref cctx cref w r w' → r ≠ none

theorem machineCloses_of_noLets {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {shape : MachineShape} (h : shape.layout.lets = 0) (hi : shape.insts = []) :
    MachineCloses mctx mref cctx cref declName shape := by
  intro logProf w r w' hr
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d⟩, w1, _, hr⟩ := RunsTo.bind hr
  dsimp only at hr
  rw [h, hi] at hr
  simp only [closeLets, ↓reduceIte] at hr
  have := RunsTo.pure_eq hr
  rw [this]
  exact Option.some_ne_none _

/-- **A state machine through the real entry.** One successful run of the
real synthesis entry on a declaration at the machine boundary returns a
module that preserves every cycle of the machine. -/
theorem synthesizeCombinationalCore_machine_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreserves declName shape bsIn slotBs letBs m d := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine old miss run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape hshape
  have hne := closes logProf _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact synthesizeMachineCertified_sound hrun.mreturns hbs hlets positive slotKinds letKinds
      layW outsOk outsNodup

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
        (Sparkle.Compiler.Elab.structEnv env))
      (Sparkle.Compiler.Elab.structEnv env)
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
