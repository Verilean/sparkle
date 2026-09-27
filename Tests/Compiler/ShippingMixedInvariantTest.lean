import Tools.ShippingMixedInvariant

namespace Sparkle.Tests.Compiler.ShippingMixedInvariantTest
open Lean Elab Command Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingBoolLiteralSoundness Tools.ShippingMixedInvariant
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingBindingsSoundness (visible)

/-- A consumer of the stronger leaf theorem: producing a Bool literal preserves
an arbitrary live BitVec input, and leaves a joint invariant for the next call. -/
theorem bool_literal_keeps_bitvec_input {ctx ρ β we mems initial s t prior dom hint named top w id n}
    {x : BitVec n} (b : Bool) (h : MixedInv ctx ρ β we mems initial s prior)
    (input : β id = some ⟨n, x⟩) (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateExprToWire (literalE dom b) hint top named) ctx s w t) :
    ∃ oldWire result, visible ctx s.sourceBindings id = some oldWire ∧
      MixedInv ctx ρ β we mems initial t result ∧
      result oldWire = x.toNat ∧ result w = encodeBool b := by
  obtain ⟨v, bound, used⟩ := h.inputs.lookup id n x input
  obtain ⟨value, _⟩ := h.inputs.values id n x v input bound
  obtain ⟨result, inv, val, frame⟩ := (translateExprToWire_literal_mixed b h widths hr).execution
  exact ⟨v, result, bound, inv, (frame v used).trans value, val⟩

/-- Cross-type record exclusion includes width-one BitVec values: equal RTL
widths do not make the two source interpretations interchangeable. -/
theorem bool_is_not_bitvec_one {ρ β e b} (sep : Separate ρ β)
    (hb : BoolDenotes ρ β e b) : ¬ Denotes β e 1 (BitVec.ofNat 1 (encodeBool b)) :=
  fun hv => denotes_disjoint sep hb hv

run_cmd do
  for name in [``denotes_disjoint, ``Records.transfer, ``Records.insert_bool,
      ``Records.insert_bits, ``Inputs.transfer, ``MixedInv.transfer,
      ``recordTranslation_mixed_bool, ``recordTranslation_mixed_bits,
      ``emitBoolResult_mixed, ``mixed_bool_hit, ``translateFallback_literal_mixed,
      ``translateStep_literal_mixed, ``translateExprToWire_literal_mixed,
      ``translateBoolMux_mixed, ``translateControlCachedWith_mixed,
      ``translateFallback_boolMux_mixed, ``translateStep_fvar_returns,
      ``translateStep_bool_input_mixed, ``translateStep_bits_input_mixed,
      ``translateSignalCompare_mixed, ``translateFallback_compare_mixed,
      ``bool_literal_keeps_bitvec_input, ``bool_is_not_bitvec_one] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed-invariant axiom: {name}: {ax}"
  logInfo "SHIPPING MIXED INVARIANT OK: both input/record families preserved by Bool literals, input reads, comparison/mux nodes and cache writes; recursive closure and entry initialization remain open"

end Sparkle.Tests.Compiler.ShippingMixedInvariantTest
