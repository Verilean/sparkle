import Tools.ShippingFGCircuitS1wRun
set_option autoImplicit false
-- NOT in the lakefile: running it exhausts 28 GB (docs §23.6). Run by hand: `lake env lean Tools/ShippingFGCircuitS1wDerive.lean` under `ulimit -v`.
namespace Tools.ShippingFGCircuitS1wRun
set_option maxHeartbeats 0
set_option maxRecDepth 100000
probe_hft_ob
end Tools.ShippingFGCircuitS1wRun
