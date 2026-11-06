import Tools.ShippingFGCircuitS2bShare
import Tools.ShippingFGCircuitS2iDTFun
set_option autoImplicit false
-- FG circuit pilot S2o: the obligation of the S1k statement over the closure family `DT`, in ONE environment. docs/FG-CIRCUIT-PILOT.md §36.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. This is a definition only: `hcd` is NOT derived here, and nothing connects it to the new Off entry / carrier.
namespace Tools.ShippingFGCircuitS2oOb
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT Tools.ShippingFGCircuitS2bShare

/-- the obligation (original `hftRootValue`, empty closure environment, the value `synth_hftPcieOutByte`), same shape as `HftObCDS` with `DT` -/
def HftObCDT (env : Lean.Environment) : Prop :=
  CDT env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte

/-- `HftObCDT` determines the value (functionality of `DT`): two values for the same root in the same environment coincide -/
theorem hftObCDT_unique {env : Lean.Environment} {v : MonoTy Tools.ShippingFGCircuitS1kStmt.shHft} (h : HftObCDT env)
    (h' : CDT env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) v) :
    v = Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte := cdt_eq h' h

end Tools.ShippingFGCircuitS2oOb
