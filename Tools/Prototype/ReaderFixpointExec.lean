import Tools.Prototype.ReaderFixpointLfp
import Tools.ShippingReaderFuelShape

/-! # Unit LC9 prototype: an EXECUTABLE version of the seven readers, and its identity with `lfpBlock`

FORM.  Lean v4.32.1 accepts `partial_fixpoint` on the DEPENDENT function `(c : Call) → Option (RB c)` whose
body is `(step senv c).run (execBlock senv)`, with the monotonicity proof supplied by hand
(`monotonicity by …` = `Fn_mono`, LC8).  So the executable block is a ONE-function `partial_fixpoint`
over the call type (outer `none` = ⊥, `some none` = refusal, `some (some v)` = success), NOT a seven-member
`mutual … partial_fixpoint … end` in the A1 text form.  The seven bodies are the EXISTING `convStep …
loopRootStep` (hand transcription of the old text, `Tools/ShippingReaderFuelDefs.lean`); this file does not
re-copy the readers.  Transcription fidelity (O2 of the proposal) is therefore NOT discharged here: it is what
the executable check (`Tests/Compiler/ReaderLfpExecTest.lean`) probes, as evidence only.

* `execBlock_eq_lfpBlock` : `execBlock senv = lfpBlock senv` (definitional unfolding; both are
  `Lean.Order.fix (Fn (step senv))`), hence `execBlock_iff` (acceptance iff) and `execBlock_unfold`.
* `machineShapeX`        : the wrapper `machineShape?` read against the executable table
  (`machNorm` real, block = `execBlock`).

BUILT/UNBUILT: see REPORT-LC9.md.  No sorry / axiom / native_decide. -/
namespace Tools.Prototype.ReaderExec
open Lean.Order Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.Prototype.ReaderLfp

/-- The executable block. -/
def execBlock (senv : StructEnv) (c : Call) : Option (RB c) :=
  (step senv c).run (execBlock senv)
partial_fixpoint monotonicity by
  intro h₁ h₂ hle c
  exact Fn_mono (step senv) h₁ h₂ hle c

/-- **Correspondence**: the executable block IS `lfpBlock`. -/
theorem execBlock_eq_lfpBlock (senv : StructEnv) : execBlock senv = lfpBlock senv := by
  unfold lfpBlock Tools.Prototype.ReaderLfp.lfp
  with_unfolding_all rfl

theorem execBlock_unfold (senv : StructEnv) (c : Call) :
    execBlock senv c = (step senv c).run (execBlock senv) := execBlock.eq_1 senv c

/-- Acceptance, transferred: executable success/refusal ↔ some fuel of the twin gives it. -/
theorem execBlock_iff (senv : StructEnv) {c : Call} {r : RB c} :
    execBlock senv c = some r ↔ ∃ n, readF senv n c = some r := by
  rw [execBlock_eq_lfpBlock]; exact lfpBlock_iff senv

theorem execBlock_iff_eval (senv : StructEnv) {c : Call} {r : RB c} :
    execBlock senv c = some r ↔ Eval senv c r := by
  rw [execBlock_eq_lfpBlock]; exact lfpBlock_iff_eval senv

/-- The wrapper's table with the executable block (`machNorm` is the real, `partial`, function). -/
def xtab (senv : StructEnv) : (c : WCall) → Option (WCall.Res c)
  | .norm e => some (machNorm senv e)
  | .blk c => execBlock senv c

/-- The wrapper `machineShape?` (as `shapeW`), run against the executable table. -/
def machineShapeX (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : Lean.ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option (Option MachineShape) :=
  (shapeW symbolicMode parameters ci senv allowInsts).run (xtab senv)

#print axioms execBlock_eq_lfpBlock
#print axioms execBlock_iff

end Tools.Prototype.ReaderExec
