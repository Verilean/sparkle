import Tools.ShippingMixedLiteralSoundness

namespace Sparkle.Tests.Compiler.ShippingMixedLiteralSoundnessTest
open Lean Elab Command Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedLiteralSoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBindingsSoundness

/-- The mixed BitVec leaf theorem retains a live Bool input, not just BitVec
records. Its declaration-growth conclusion recovers entry widths as well. -/
theorem bitvec_literal_keeps_bool_input {ctx ρ β we mems initial s t prior e us hint named top w n id b}
    {x : BitVec n} (h : MixedInv ctx ρ β we mems initial s prior) (hn : 0 < n)
    (input : ρ id = some b)
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us) (hd : Denotes β e n x)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateExprToWire e hint top named) ctx s w t) :
    ScalarWidthsAgree we s ∧ ∃ oldWire result,
      visible ctx s.sourceBindings id = some oldWire ∧
      MixedInv ctx ρ β we mems initial t result ∧
      result oldWire = encodeBool b ∧ result w = x.toNat := by
  obtain ⟨v, bound, used, value, _⟩ := h.inputs.bool id b input
  obtain ⟨growth, step⟩ := translateExprToWire_literal_mixed h hn fn hd widths hr
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨growth.widths widths, v, result, bound, inv, (frame v used).trans value, val⟩

run_cmd do
  for name in [``DeclGrows.trans, ``DeclGrows.widths, ``allocate_assign_mixed,
      ``literal_payload_mixed, ``mixed_bits_hit, ``translateCore_literal_mixed,
      ``core_literal_shape, ``core_literal_recorded, ``Tools.ShippingMixedLiteralSoundness.translateStep_literal_mixed,
      ``Tools.ShippingMixedLiteralSoundness.translateExprToWire_literal_mixed, ``bitvec_literal_keeps_bool_input] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed BitVec literal axiom: {name}: {ax}"
  logInfo "SHIPPING MIXED BITVEC LITERAL OK: actual translator, validated cache and mixed invariant; positive widths; no child or legacy premise"

end Sparkle.Tests.Compiler.ShippingMixedLiteralSoundnessTest
