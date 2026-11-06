import Tools.ShippingFGCircuitS2tHft
set_option autoImplicit false
-- FG circuit pilot S2t: `HftObCDT` from the generated derivation (conditional on `EnvDefs`/`EnvCtors`/`RecFact`). docs/FG-CIRCUIT-PILOT.md §45.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Tools.ShippingFGCircuitS2tHft
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bShare Tools.ShippingFGCircuitS2iTbl Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT

/-- the root's `HftObCDT`, from the generated derivation. REMAINING CONDITIONS (not discharged here): `EnvDefs env Delta`, `EnvCtors env Gamma`, `RecFact env`. -/
theorem hftObCDT_T (env : Lean.Environment) (hΔ : EnvDefs env hftObCDT_of_tablesT.Delta) (hΓ : EnvCtors env hftObCDT_of_tablesT.Gamma) (hrec : RecFact env) :
    Tools.ShippingFGCircuitS2oOb.HftObCDT env :=
  hftObCDT_of_tablesT env hΔ hΓ hrec

end Tools.ShippingFGCircuitS2tHft
#print axioms Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT
#print axioms Tools.ShippingFGCircuitS2tHft.hftObCDT_T
