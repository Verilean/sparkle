import Tools.ShippingFGCircuitS3vBridge
set_option autoImplicit false
-- FG circuit pilot S3v, steps 2-3: the closed child `pilotK0` (`httpGetByte`) end to end.  From `checkComb_sound` (the module's IR semantics equals the source terms' value), `checkK0 pilotK0 = true`, and the bridge `ofData_sound` (the source terms denote what `Term.eval` on `typedVal` gives), together with `httpGetByte.machine_result` (`machineSource` = those evaluated outputs): `ChildFn pilotK0 (childRange kd) (childValue …)`, the exact conjunct `RootShowsAt` needs for call 0.  Full type, all inputs, no run premise.  The side conditions of the bridge are PROVED for `httpGetByte` by the kernel (per-field closed facts).  docs/FG-CIRCUIT-PILOT.md §71.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3vChild
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingFGCircuitS3vBridge
open Tools.ShippingUnifiedSource Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingFGCircuitS3rArtifact (pilotK0)
open Tools.ShippingMachineCompose (ChildFn argPorts)
open Tools.ShippingMachineChild (childValue childRange decB decV portIdx InRange inRange_get)
open Sparkle.IP.Net.HTTP (httpGetByte)
open Sparkle.Core.Domain (defaultDomain)
open Sparkle.Core (HList)

/-- the data of `httpGetByte` -/
noncomputable abbrev kd0 : MachineData := httpGetByte.machineData

/-! ### the bridge's side conditions, proved for `httpGetByte` (closed facts, kernel) -/
theorem k0_ss : kd0.ss.length = 0 := by decide +kernel
theorem k0_frag_ls : kd0.ls.all (fun l => Frag kd0 l.2) = true := by decide +kernel
theorem k0_frag_outs : kd0.outs.all (fun o => Frag kd0 o.2) = true := by decide +kernel
theorem k0_outs_len : kd0.outs.length = 1 := by decide +kernel
theorem k0_inpos : inputPositions kd0 = [1] := by decide +kernel
theorem k0_portIdx : portIdx kd0.bsIn 1 = 0 := by decide +kernel
theorem k0_range_bs : (kd0.bsIn.filter (fun b => b.2 != .domain)).map (·.2) = [.bits 6] := by decide +kernel
theorem k0_inputs_len : pilotK0.inputs.length = 1 := by decide +kernel
theorem k0_inputs_ok : pilotK0.inputs.all
    (fun p => p.name != "clk" && p.name != "rst" && portW p == 6) = true := by decide +kernel
theorem k0_outputs_len : pilotK0.outputs.length = 1 := by decide +kernel

end Tools.ShippingFGCircuitS3vChild
