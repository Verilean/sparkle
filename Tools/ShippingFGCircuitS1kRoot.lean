import Tests.Compiler.ShippingMachineCombTest
import Tools.ShippingFGCircuitS1iChild
import IP.Bus.PCIeHFT
set_option autoImplicit false
-- FG circuit pilot S1k, unit 1: the non-leaf root `synth_hftPcieOutByte` (a public copy of the private test definition) and its generated endpoints. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.
namespace Tools.ShippingFGCircuitS1kRoot
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Bus.PCIeHFT

/-- the body of `Tests/IP/Bus/PCIeHFTTest.lean`'s `private def synth_hftPcieOutByte` (public here so that its endpoints can be named) -/
def synth_hftPcieOutByte
    (rxByte : Signal defaultDomain (BitVec 8))
    (rxValid sopTlp : Signal defaultDomain Bool)
    (dataDword : Signal defaultDomain (BitVec 32))
    (cplId : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 8) :=
  (hftPcieLoop rxByte rxValid sopTlp dataDword cplId).outByte

end Tools.ShippingFGCircuitS1kRoot
open Tools.ShippingFGCircuitS1kRoot in
#machine_endpoint Sparkle.IP.Bus.PCIe.tlpCplByte
open Tools.ShippingFGCircuitS1kRoot in
#machine_endpoint Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  for p in [``Sparkle.IP.Net.HTTP.httpGetByte, ``Sparkle.IP.Bus.PCIe.tlpCplByte, ``Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte] do
    let mut have_ : List String := []
    for s in ["machineData", "machine_ok", "machine_body", "machine_closes", "machine_sound", "machine_ships_wired", "machine_ships_comb", "machine_closes_at", "machine_design_svHR"] do
      if env.contains (p ++ Name.mkSimple s) then have_ := s :: have_
    logInfo m!"S1K PROBE {p}: {have_.reverse}"
