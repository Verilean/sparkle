import Tools.ShippingFGCircuitS1kStmt
set_option autoImplicit false
-- FG circuit pilot S3b2 (route B), unit 2: EXECUTABLE copies of the two children's `machineData`.  The `machineData` constants are added with `addDecl` (no compiled code), so a Bool check cannot call them.  Here each is re-added UNDER A NEW NAME with exactly its own value (`addAndCompile`), and the equation to the original is `rfl`.  No other content; no sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §53.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3b2Exp
open Lean Elab Command

/-- `compile_data_copy SRC DST`: add `DST` with the value of `SRC` (same type), compiled -/
elab "compile_data_copy " src:ident dst:ident : command => do
  let env ← getEnv
  let some ci := env.find? src.getId | throwError "no such constant {src.getId}"
  let some v := ci.value? | throwError "{src.getId} has no value"
  liftCoreM <| addAndCompile (.defnDecl
    { name := dst.getId, levelParams := [], type := ci.type, value := v, hints := .abbrev, safety := .safe })

compile_data_copy Sparkle.IP.Net.HTTP.httpGetByte.machineData Tools.ShippingFGCircuitS3b2Exp.httpMD
compile_data_copy Sparkle.IP.Bus.PCIe.tlpCplByte.machineData Tools.ShippingFGCircuitS3b2Exp.tlpMD

theorem httpMD_eq : httpMD = Sparkle.IP.Net.HTTP.httpGetByte.machineData := rfl
theorem tlpMD_eq : tlpMD = Sparkle.IP.Bus.PCIe.tlpCplByte.machineData := rfl

end Tools.ShippingFGCircuitS3b2Exp

#print axioms Tools.ShippingFGCircuitS3b2Exp.httpMD_eq
#print axioms Tools.ShippingFGCircuitS3b2Exp.tlpMD_eq
