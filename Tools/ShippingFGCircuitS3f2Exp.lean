import Tools.ShippingFGCircuitS3b2Exp
import Tools.ShippingFGCircuitS1kRoot
set_option autoImplicit false
-- FG circuit pilot S3f2, unit 1: an EXECUTABLE copy of the ROOT's `machineData` (as S3b2Exp did for the two children), with the kernel equation to the original constant.  The copy is added UNDER A NEW NAME with exactly the original's value (`addAndCompile`); `rootMD_eq` is `rfl`.  No other content; no sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §56.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3f2Exp
open Lean Elab Command
open Tools.ShippingFGCircuitS3b2Exp

compile_data_copy Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machineData Tools.ShippingFGCircuitS3f2Exp.rootMD

/-- the kernel equation of the executable copy to the original constant -/
theorem rootMD_eq : rootMD = Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machineData := rfl

end Tools.ShippingFGCircuitS3f2Exp

#print axioms Tools.ShippingFGCircuitS3f2Exp.rootMD_eq
