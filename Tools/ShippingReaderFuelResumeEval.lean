import Tools.ShippingReaderFuelShapeEval
import Tools.ShippingReaderFuelDriverResume

/-! # A finite wrapper derivation ⟺ an answer of the resumable driver

Integrator, 2026-10-17. Connects `Tools/ShippingReaderFuelShapeEval.lean` (`shapeRuns_iff`: a finite wrapper
derivation `ShapeRuns … r` ⟺ some fuel decides `r`) with `Tools/ShippingReaderFuelDriverResume.lean`
(`resumeShape_answers_iff`: the resumable driver eventually answers `r` ⟺ some fuel decides `r`). Both
directions, for success (`r = some s`) and ordinary refusal (`r = none`). A statement about the MODEL only:
nothing here claims that the compiled `partial` reader produces a finite derivation (O1), that the real
constants satisfy their equations (O2), or that one attempt terminates at run time (O3/O4). No `sorry`, no
axiom, no `native_decide`. -/
namespace Tools.ShippingReaderFuel
open Lean Sparkle.Compiler.Elab

/-- **A finite wrapper derivation exists iff the resumable driver (from any start) eventually answers the
same, with a fuel witness.** -/
theorem shapeRuns_iff_resume {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} (start : Nat) (r : Option MachineShape) :
    ShapeRuns sm ps ci senv ai r ↔
      ∃ n, ResumeAnswers (fun n => machineShapeF n sm ps ci senv ai) (resumeInit start) (r, n) :=
  shapeRuns_iff.trans (resumeShape_answers_iff start r).symm

/-- Success version. -/
theorem shapeRuns_ok_iff_resume {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} (start : Nat) (sp : MachineShape) :
    ShapeRuns sm ps ci senv ai (some sp) ↔
      ∃ n, ResumeAnswers (fun n => machineShapeF n sm ps ci senv ai) (resumeInit start) (some sp, n) :=
  shapeRuns_iff_resume start (some sp)

/-- Ordinary-refusal version. -/
theorem shapeRuns_fail_iff_resume {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} (start : Nat) :
    ShapeRuns sm ps ci senv ai none ↔
      ∃ n, ResumeAnswers (fun n => machineShapeF n sm ps ci senv ai) (resumeInit start) (none, n) :=
  shapeRuns_iff_resume start none

end Tools.ShippingReaderFuel
