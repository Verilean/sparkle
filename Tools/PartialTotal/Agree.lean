import Tools.Prototype.LiftScalarModelLetOk
import Tools.ShippingLetsExternSpec
set_option autoImplicit false
-- NOT BUILT: K1 skeleton (the four theorems carry `sorry`). Skeleton content built OK at 6e3739fd (Tests.Gen3.PartialTotalCheck exit 0).

/-! # Partial-total agreement theorems (scripts/gen3/PARTIAL_TOTAL_FREEZE.md §3)

`machBoolMap`, `machLiftScalarN` (Sparkle/Compiler/Elab.lean) and `rootFloat` (Sparkle/Compiler/MachRawSurface.lean) are now
total definitions (K1 compiler edit: `partial` removed; `rootFloat` is `rootFloatF` with a fuel `rootFloatNu e + 1`).
The models are the ones already in the tree and are imported, not copied:
`Tools.Prototype.BoolMapModelLetOk.boolMapModel`, `Tools.Prototype.LiftScalarModelLetOk.liftN` / `liftStep`,
`Tools.ShippingLetsReaderInv.rootFloatS` / `liftSpec` / `nu`.
The premise definitions `BoolMapCorr`, `LiftScalarCorr`, `RootFloatAgrees` are the existing ones (unchanged); these theorems
prove them. `rootFloatAgrees` depends on the existing `LiftAgrees` (an open C++ extern premise that stays). -/
namespace Tools.PartialTotal.Agree
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.BoolMapModelLetOk
  Tools.Prototype.LiftScalarModelLetOk

/-- T1L-59, as an equation (stronger than `BoolMapCorr`, which is the `→` direction). -/
theorem boolMap_eq (senv : StructEnv) (dom a : Lean.Expr) (wa : Nat) :
    ∀ (body : Lean.Expr), machBoolMap senv dom a wa body
      = boolMapModel (machLiftScalarN senv dom [(wa, a)]) dom body := by
  sorry

theorem boolMapCorr (senv : StructEnv) : BoolMapCorr senv := by
  sorry

/-- T1L-58. -/
theorem liftScalarCorr (senv : StructEnv) : LiftScalarCorr senv := by
  sorry

/-- T1L-52, under the existing open premise `LiftAgrees`. -/
theorem rootFloatAgrees (hl : LiftAgrees) : RootFloatAgrees := by
  sorry

end Tools.PartialTotal.Agree
