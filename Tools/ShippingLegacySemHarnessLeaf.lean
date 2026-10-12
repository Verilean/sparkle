import Tools.ShippingLegacySemHarnessAt

/-! # The harness's output statement from the leaf's run at the prepared setup

`harness_sound_spec` (`Tools/ShippingLegacySemHarnessAt.lean`) takes a run of
the CERTIFIED binder walk around the leaf emission
(`Returns (bindMixedCertifiedInputs (emitLeaves …) (bs.zip ids)) …`) and uses
it at exactly one place: `prepare_returns`, which turns it into a run of the
leaf emission from the prepared setup (`prepare bools bits (bs.zip ids)
(start …)`). Every other step of the proof is about that leaf run.

The LEGACY binder walk over several variables cannot be turned into a run of
the certified walk: `Returns` quantifies the world per run, so runs cannot be
re-composed under `bindInputPort` (there is no introduction rule for `>>=`).
But it CAN be inverted down to the same leaf run (`bindInputsLegacy_prepare`,
`Tools/ShippingLegacySemBinderList.lean`). So:

**Proved here**: `harness_sound_leaf` — `harness_sound_spec` with the leaf's
run at the prepared setup as its hypothesis, in place of the walk's run. The
proof text is `harness_sound_spec`'s without its `prepare_returns` line
(generated; nothing else changed). `harness_sound_spec` is untouched. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion Tools.ShippingUnifiedProtection
open Tools.ShippingUnifiedEntrySoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingPostSoundness
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedPrintSoundness (mixedShape_positive)
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBoolMuxSoundness (boolMuxE)
open Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup

/-- **The harness's output statement from the LEAF's run at the prepared
setup** (no run of a binder walk in the statement). -/
theorem harness_sound_leaf {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {leafE : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (nameLegal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (mems : MEnv)
    (values : Admissible bools bits initial (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString))
    (leaf : Returns
      (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
        [("out", leafE)] none 0)
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state returned st)
    (v : Value) (positive : 0 < v.kind.width)
    (contract : ActionSpec (translateExprToWire leafE "out" false true)
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (inputValues
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits)
      (declaredWidths st) mems initial v)
    (ordered : ActionOrder (translateExprToWire leafE "out" false true)
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (inputValues
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits)
      (declaredWidths st) mems initial) :
    RawValueAt v.kind.width bs m initial mems v.toNat := by
  let a := start (entryCompilerState false cache) declName.toString
  let p := prepare bools bits (bs.zip ids) a
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  obtain ⟨unique, result, evalr, value, out, typed, _⟩ := emitLeaves_from_ports_spec positive contract
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  have outputEq : m.outputs = st.module.outputs.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
  have shape := prepare_shape (bools := bools) (bits := bits) (bs.zip ids) a (by intro p hp; cases hp)
  obtain ⟨wm, ready, printOutputs, outputTyped, outputWidth, order⟩ := emitLeaves_postReady_at_spec
    positive contract ordered
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 shape.1 shape.2 wireEq bodyEq outputEq leaf
  have ib := prepare_inputBounds (bs.zip ids) a (by intro p hp; cases hp) values
  obtain ⟨w, sm, ty, tr, fresh, ht, hty⟩ := emitLeaves_single leaf
  have frame := contract.frame p.state sm w
    (lookup_of_ports prepared.1 prepared.2.1) tr
  refine ⟨result, ?_, value, ready, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moduleWidths_finish wireEq unique, bodyEq]; exact evalr
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
      obtain ⟨l, rhs, k, eq, _⟩ := typed stmt hs'
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    have hp' : port ∈ p.state.module.inputs := by
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      exact frame.inputs ▸ hp
    obtain ⟨decl, bound⟩ := ib port hp'
    rw [wm, declaredWidths_agree unique port (by rw [ht, emitAssign_wires]; exact frame.decls port decl)]
    exact bound
  · intro positiveBinders
    have pi := prepare_print (bools := bools) (bits := bits) (bs.zip ids) a
      (by intro port hp; cases hp) (fun name k id hp => positiveBinders name k (List.of_mem_zip hp).1)
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      obtain ⟨l, rhs, k, eq, _⟩ := typed stmt (List.mem_reverse.mpr hs)
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
      change ({name := "out", ty := ty} :: sm.module.outputs).reverse = _
      rw [frame.outputs, shape.2]; rfl

end Tools.ShippingLegacySem
