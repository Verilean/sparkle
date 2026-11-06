import Tools.ShippingFGCircuitS2iRun
import Tools.ShippingFGCircuitS2oOb
set_option autoImplicit false
-- FG circuit pilot S2q: the GENERATED typed derivation of the original `hftRootValue` over the closure family `DT` (`hcd`). docs/FG-CIRCUIT-PILOT.md §43.
-- NOT in the lakefile on this branch: with the approved rules the generator STOPS at two `HOr.hOr` (`Signal (BitVec n) ||| Signal (BitVec n)`), docs §43.3. The side branch `s2q-exp-or` adds an UNAPPROVED `sigOrBV` rule and registers this file.
-- UNTRUSTED generator, kernel-checked theorem. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
open Lean Meta Elab Command Term
open Tools.ShippingFGCircuitS2iRun
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Tools.ShippingFGCircuitS2qHft
derive_hft_t "Q"
end Tools.ShippingFGCircuitS2qHft
