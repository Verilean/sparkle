import Tools.ShippingFGCircuitS2iRun
import Tools.ShippingFGCircuitS2oOb
set_option autoImplicit false
-- FG circuit pilot S2t: the GENERATED typed derivation of the original `hftRootValue` over the closure family `DT` (`hcd`), with the APPROVED, evidence-carrying `sigOrBV` (second type argument tied to `W` by `natEvalE`). docs/FG-CIRCUIT-PILOT.md §45.
-- UNTRUSTED generator, kernel-checked theorem (the `kernel ms` of the report is the SYNCHRONOUS `addDeclCore` time). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
open Lean Meta Elab Command Term
open Tools.ShippingFGCircuitS2iRun
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Tools.ShippingFGCircuitS2tHft
derive_hft_t "T"
end Tools.ShippingFGCircuitS2tHft
