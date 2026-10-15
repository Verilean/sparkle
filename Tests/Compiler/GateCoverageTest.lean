import Tests.Compiler.GateConeDesignAllTest
import Tests.Compiler.GateConeWrapPickSourceTest
import Tests.Compiler.GateConeWrapPickDesignTest
import Tools.ShippingGateCoverage

/-! # `#gate_coverage` on the eight simulated gate-route parents (round par/gate-cov)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateCoverageTest`;
NOT imported by `Tests.AllTests`). A MEASUREMENT: it logs one row per parent
and asserts nothing.

The imports bring every gate-parent theorem module into the environment:
`GateConeDesignAllTest` (all-run, `…_gate_designSVall`) imports
`GateConeDesignTypedTest` (`…_gate_designSVN3`) and, through it, the older
design / cone / observation test modules; `GateConeWrapPickSourceTest` has
`wrapPick_gate_cone_runK'` (observation level).

This is a SEPARATE tally of gate-route parents. It is NOT part of
`#design_coverage` (`Tests/Compiler/DesignCoverageTest.lean`, the
machine-route census, unchanged), and it does not claim coverage of all
inputs. `GateDefines` is counted as the separate gate-only reflection class
(`docs/parallel/G-gatedefines-class.md`). -/

set_option maxHeartbeats 0 in
#gate_coverage
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentUse
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.wrapAdd
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentMix
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentTwoCalls
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentRepeat
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentCmp
  Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentNested
  Sparkle.Tests.Compiler.SlotlessParentProbeTest.wrapPick
