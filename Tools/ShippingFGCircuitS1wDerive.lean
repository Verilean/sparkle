import Tools.ShippingFGCircuitS1wRun
set_option autoImplicit false
-- FG circuit pilot S1w2: emits `hftObCDW_of_tables` (the typed `DW` derivation of `hftRootValue`). docs §23.6. No sorry/axiom/native_decide/TRUSTED/law.
namespace Tools.ShippingFGCircuitS1wRun
set_option maxHeartbeats 0
set_option maxRecDepth 100000
derive_hft_ob ""
#print axioms hftObCDW_of_tables
end Tools.ShippingFGCircuitS1wRun
