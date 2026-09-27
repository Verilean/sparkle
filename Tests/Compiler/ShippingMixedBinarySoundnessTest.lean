import Tools.ShippingMixedBinarySoundness

namespace Sparkle.Tests.Compiler.ShippingMixedBinarySoundnessTest
open Lean Elab Command Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant Tools.ShippingScalarSoundness
open Tools.ShippingMixedBinarySoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBindingsSoundness

/-- A mixed caller keeps its live Bool input while any canonical binary
operator computes a BitVec result, including an already preallocated target. -/
theorem binary_keeps_bool_input {ctx ρ β we mems initial s t prior rec e args hint named w n id b}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : MixedInv ctx ρ β we mems initial s prior) (input : ρ id = some b)
    (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx ρ β we mems initial args[args.size - 2]! "op_a" n x.toNat)
    (cb : Child rec ctx ρ β we mems initial args[args.size - 1]! "op_b" n y.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCanonicalSignalBinary rec e op.operator args true true hint named) ctx s w t) :
    ∃ oldWire result, visible ctx s.sourceBindings id = some oldWire ∧
      MixedInv ctx ρ β we mems initial t result ∧
      result oldWire = encodeBool b ∧ result w = (op.apply x y).toNat := by
  obtain ⟨v, bound, used, val, _⟩ := h.inputs.bool id b input
  obtain ⟨_, step⟩ := translateCanonicalSignalBinary_mixed op x y hn h width ca cb widths hr
  obtain ⟨result, inv, value, frame⟩ := step.execution
  exact ⟨v, result, bound, inv, (frame v used).trans val, value⟩

/-- The structural half forbids a newly recorded expression at a name that
was already reserved before the child, even without semantic assumptions. -/
theorem reserved_record_was_present {s t w e} (h : Frame s t)
    (reserved : s.usedNames.contains w = true) (old : s.translateRecord.get? w = none) :
    t.translateRecord.get? w ≠ some e := by
  intro he
  have := h.record_reserved reserved he
  rw [old] at this
  cases this

run_cmd do
  for name in [``Frame.refl, ``Frame.trans, ``Frame.record_reserved,
      ``Lookup.ofInputs, ``Lookup.transfer, ``Frame.makeWire, ``Frame.emitAssign, ``emit_reserved_mixed,
      ``binary_returns, ``translateCanonicalSignalBinary_mixed, ``binary_frame,
      ``core_binary_returns, ``Frame.record_new, ``core_binary_recorded,
      ``translateStep_binary_mixed, ``core_binary_record_frame,
      ``translateStep_binary_frame, ``translateExprToWire_binary_mixed,
      ``binary_keeps_bool_input, ``reserved_record_was_present] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed binary axiom: {name}: {ax}"
  logInfo "SHIPPING MIXED BINARY OK: 8 operators, allocation before children, width transport, joint invariant, actual core/cache step; recursive contracts remain explicit"

end Sparkle.Tests.Compiler.ShippingMixedBinarySoundnessTest
