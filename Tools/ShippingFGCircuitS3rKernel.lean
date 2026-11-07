import Tools.ShippingFGCircuitS3rArtifact
import Tools.ShippingMachineShipsHier
import Tools.ShippingHierSVSoundness
set_option autoImplicit false
-- FG circuit pilot S3r, step 3: the EXISTING pure checks, evaluated by the kernel (`decide +kernel`; no native_decide) on the closed artifact terms of `Tools.ShippingFGCircuitS3rArtifact` (generated, untrusted).
-- These are facts about THE CLOSED TERMS `pilotB0`/`pilotD0`.  That those terms are what `pilotEntry3 hftRoot` returned is NOT a kernel fact (`Tools.ShippingFGCircuitS3rObs` observes it).  They are checker outputs on a term, not a semantic-preservation theorem (that needs `CheckRoot`, the next step).
-- No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §68.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3rKernel
open Sparkle.IR.AST Sparkle.IR.RefineCheck Sparkle.IR.OptCheck Tools.ShippingFGCircuitS3rArtifact
open Tools.ShippingDesignSV (wofOf weS)

/-- the shape of the artifact: 256 top statements, children of 88 and 159 -/
theorem shape : pilotB0.body.length = 256 ∧ pilotD0.modules.map (·.body.length) = [88, 159] := by decide +kernel

/-- the compiler's hierarchical-route checker premise (`machine_ships_hierC`) -/
theorem ships_hier : Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap pilotD0.modules) pilotB0 = true := by decide +kernel

theorem hier_binds : hierBinds pilotB0 = true := by decide +kernel

theorem hier_refine_self : hierRefineCheck pilotB0 pilotB0 = true := by decide +kernel

theorem refine_child0 : refineCheck pilotK0 pilotK0 = true := by decide +kernel

theorem refine_child1 : refineCheck pilotK1 pilotK1 = true := by decide +kernel

/-- `mergeChecked` returns the returned module unchanged (the module has instances) -/
theorem merge_fixed : mergeChecked pilotB0 = pilotB0 := by decide +kernel

/-- the sequential-fragment check on the children (as returned = as shipped) -/
theorem seq_child0 : Tools.SVParser.EmitSem.seqCheck (wofOf pilotK0) (weS pilotK0) pilotK0.body = true := by decide +kernel

theorem seq_child1 : Tools.SVParser.EmitSem.seqCheck (wofOf pilotK1) (weS pilotK1) pilotK1.body = true := by decide +kernel

/-- the shipped form of the top (the optimizer's output, validated by `hierRefineCheck` inside `checkedOptimize`) has 89 statements and passes `seqCheck` -/
theorem shipped_len : (checkedOptimize pilotB0).body.length = 89 := by decide +kernel

theorem seq_shipped : Tools.SVParser.EmitSem.seqCheck (wofOf (checkedOptimize pilotB0)) (weS (checkedOptimize pilotB0)) (checkedOptimize pilotB0).body = true := by decide +kernel

end Tools.ShippingFGCircuitS3rKernel
