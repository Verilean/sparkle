import Tools.Prototype.LiftScalarModelLetOk
set_option autoImplicit false
-- NOT BUILT: PTOT skeleton measure file (definitions only).

/-! # Fuel measure for `machLiftScalarN` (used by `Tools/PartialTotal/Agree.lean`)

Definitions only, no theorems. `csz` is a measure on which every recursive call of `liftStep` (and the `ashr` re-entry)
decreases: constants/leaves count 1; an application counts its argument, its function part (not for the `BitVec.toNat m`
head, whose `m` is never called) and 1; an `ashr` application counts 3 more, so that the rebuilt `sshiftRight` term is
smaller. Kept out of the proof file so that the proof file adds theorems only (proof-accept `aux`). -/
namespace Tools.PartialTotal.Agree
open Lean

def isToNatHead : Lean.Expr → Bool
  | .app (.const c _) _ => c == ``BitVec.toNat
  | _ => false

def isAshrHead : Lean.Expr → Bool
  | .app (.app (.const c _) _) _ => c == ``Sparkle.Core.Signal.ashr
  | _ => false

def csz : Lean.Expr → Nat
  | .app f a => csz a + 1 + (if isToNatHead f then 0 else csz f) + (if isAshrHead f then 3 else 0)
  | _ => 1

end Tools.PartialTotal.Agree
