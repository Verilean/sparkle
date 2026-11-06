import Tools.ShippingFGCircuitS1zClose
import Tools.ShippingCallsGatePinned
import Tools.ShippingCallsMemPinned
import Tools.ShippingMachineClosesAtGen
set_option autoImplicit false
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingMachineAuto Tools.ShippingFGCircuitS1kStmt Tools.ShippingMachineClosesData

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  for p in [``Sparkle.IP.Net.HTTP.httpGetByte, ``Sparkle.IP.Bus.PCIe.tlpCplByte, ``Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte] do
    for s in ["machine_closes", "machine_closes_at", "machine_ok", "machine_body", "machineData"] do
      if let some ci := env.find? (p ++ Name.mkSimple s) then
        logInfo m!"{p ++ Name.mkSimple s} : {ci.type}"
  if let some ci := env.find? (``Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte ++ `machine_closes_at) then
    logInfo m!"VALUE {ci.value!}"
