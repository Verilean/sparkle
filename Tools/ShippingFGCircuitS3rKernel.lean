import Tools.ShippingFGCircuitS3rArtifact
import Tools.ShippingMachineShipsHier
import Tools.ShippingHierSVSoundness
set_option autoImplicit false
-- FG circuit pilot S3r, step 3: the EXISTING pure checks, evaluated by the kernel (`decide +kernel`; no native_decide) on the closed artifact terms of `Tools.ShippingFGCircuitS3rArtifact` (generated, untrusted).
-- These are facts about THE CLOSED TERMS `pilotB0`/`pilotD0`/`pilotS0`.  That those terms are what `pilotEntry3 hftRoot` returned (and that `pilotS0` is `checkedOptimize pilotB0`) is NOT a kernel fact (`Tools.ShippingFGCircuitS3rObs` observes it).  They are checker outputs on a term, not a semantic-preservation theorem (that needs `CheckRoot`, the next step).
-- NOT kernel-evaluable (measured, docs §68): `checkedOptimize`/`shipsHierCheck` (the optimizer `optimizeModule` is a `partial def`) and `seqCheck` (`sanitizeName` uses `String.all`, which the kernel does not reduce, even on "abc"); the checks that mention `checkedOptimize b` are run with the shipped form supplied as the closed term `pilotS0`.
-- No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §68.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3rKernel
open Sparkle.IR.AST Sparkle.IR.RefineCheck Tools.ShippingFGCircuitS3rArtifact
open Tools.ShippingHierPremisesBase Tools.ShippingMachineLinked Tools.ShippingHierOpen Tools.ShippingHierState (instNames)

/-- the shape of the artifact: 256 top statements, shipped form 89, children of 88 and 159 -/
theorem shape : pilotB0.body.length = 256 ∧ pilotS0.body.length = 89 ∧ pilotD0.modules.map (·.body.length) = [88, 159] := by decide +kernel

/-! ### checks on the returned module (no optimizer involved) -/

theorem hier_binds : hierBinds pilotB0 = true := by decide +kernel

theorem hier_refine_self : hierRefineCheck pilotB0 pilotB0 = true := by decide +kernel

theorem refine_child0 : refineCheck pilotK0 pilotK0 = true := by decide +kernel

theorem refine_child1 : refineCheck pilotK1 pilotK1 = true := by decide +kernel

/-- the children as returned are the children of the design -/
theorem design_kids : pilotD0.modules = [pilotK0, pilotK1] := rfl

/-- `mergeChecked` returns the returned module unchanged -/
theorem merge_fixed : mergeChecked pilotB0 = pilotB0 := by decide +kernel

/-! ### the shipped form as a closed term (`pilotS0`; the optimizer is opaque to the kernel) -/

/-- the optimizer's output, validated by the hierarchical check (the very check `checkedOptimize` runs) -/
theorem hier_refine_shipped : hierRefineCheck pilotB0 pilotS0 = true := by decide +kernel

/-- `shipsHierCheck` with `checkedOptimize pilotB0` replaced by the closed term `pilotS0`: the same conjuncts (`hierCheck`, `instOutWidthsOk`) written out from the existing components -/
theorem ships_hier_shipped :
    (hierBinds pilotB0 &&
      linkedWF (childMap pilotD0.modules) pilotS0.body &&
      decide (instNames pilotB0.body).Nodup && decide (instNames pilotS0.body).Nodup &&
      noSelfRead (childMap pilotD0.modules) pilotS0.body && outsExtracted (childMap pilotD0.modules) pilotB0 &&
      (pilotB0.inputs.map (·.name)).contains "rst" &&
      instOutWidthsOk (childMap pilotD0.modules) (Sparkle.IR.RegDedup.declWidth pilotB0) pilotB0.body) = true := by decide +kernel

/-! ### negative controls: an altered statement makes the check false -/

/-- the shipped form with its first statement dropped -/
def dropFirst (m : Module) : Module := { m with body := m.body.drop 1 }

/-- the shipped form with every register's initial value changed to 1 -/
def flipInit (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .register o c r i _ => .register o c r i 1
      | s => s }

/-- the shipped form with every constant `0` of width 1 replaced by `1` -/
def flipConst (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .assign l (.const 0 1) => .assign l (.const 1 1)
      | s => s }

theorem neg_drop : hierRefineCheck pilotB0 (dropFirst pilotS0) = false := by decide +kernel
theorem neg_init : hierRefineCheck pilotB0 (flipInit pilotS0) = false := by decide +kernel
theorem neg_child0 : refineCheck pilotK0 { pilotK0 with body := pilotK0.body.drop 1 } = false := by decide +kernel
theorem neg_child1 : refineCheck pilotK1 { pilotK1 with body := pilotK1.body.drop 1 } = false := by decide +kernel
/-- the altered module is a different term (so the control is not vacuous) -/
theorem neg_distinct : decide (dropFirst pilotS0 = pilotS0) = false ∧ decide (flipInit pilotS0 = pilotS0) = false := by decide +kernel

end Tools.ShippingFGCircuitS3rKernel
