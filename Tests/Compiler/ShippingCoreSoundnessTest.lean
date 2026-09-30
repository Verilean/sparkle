import Tools.ShippingCoreSoundness

/-! S7-1: the reconciled shipping statement — audit that the one core
theorem (and therefore every family contract it bundles) carries only
the standard axioms, and pin that each family dispatcher is recoverable
from the bundle by projection. -/
namespace Sparkle.Tests.Compiler.ShippingCoreSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab
open Tools.ShippingCoreSoundness

/-- Each family contract is a projection of the bundle (spot-pin: the
memory and register families). -/
theorem bundle_projects {declName bs body m}
    (h : ShippingPreserves declName bs body m) :
    Tools.ShippingRegisterSoundness.RegisterPreserves declName bs body m ∧
    Tools.ShippingMemoryEntrySoundness.MemoryConePreserves declName bs body m :=
  ⟨h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

run_cmd liftTermElabM do
  for name in [``Tools.ShippingCoreSoundness.synthesizeCombinationalCore_shipping_sound,
      ``bundle_projects] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected shipping core axiom: {name}: {ax}"
  logInfo "SHIPPING CORE: one entry statement bundles all eleven family contracts; standard axioms only"

end Sparkle.Tests.Compiler.ShippingCoreSoundnessTest
