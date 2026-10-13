import Tools.ShippingReaderBoolMap

/-! # `machBoolMapT`: the equality arm returns a result on its accepted shape

WRITTEN, NOT BUILT (par/h-1). ONE theorem, separate from
`Tools/ShippingReaderBoolMap.lean` because its proof is a blind `simp`
through a `do` block (a `let` with a pattern, `unless`, an `if`): if it
fails, nothing else depends on it.

    machBoolMapT_beq_some
        (h1 : machBits? ty = some w)
        (h2 : inst.isAppOf ``instBEqOfDecidableEq = true)
        (hx : lift x = some (w, x')) (hy : lift y = some (w, y')) :
      machBoolMapT lift dom (beqE us ty inst x y) = some (beqOut ty dom w x' y')

The four premises are the four tests of the arm, as the compiler writes
them; `lift` is the parameter (at the compiler's instance:
`machLiftScalarN senv dom [(wa, a)]`, a `partial` function — its results are
premises here, not theorems). -/
namespace Tools.ShippingReaderBoolMap
open Lean
open Sparkle.Compiler.Elab (machBits? inlNatLit)

/-- `@BEq.beq ty inst x y`. -/
def beqE (us : List Level) (ty inst x y : Expr) : Expr :=
  .app (.app (.app (.app (.const ``BEq.beq us) ty) inst) x) y

/-- `Signal.beq` of the lifted operands, as the compiler writes it. -/
def beqOut (ty dom : Expr) (w : Nat) (x' y' : Expr) : Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.beq []) ty dom
    (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty
      (mkApp (.const ``instDecidableEqBitVec []) (inlNatLit w))) x' y'

theorem machBoolMapT_beq_some (lift : Expr → Option (Nat × Expr)) (dom : Expr)
    (us : List Level) (ty inst x y : Expr) (w : Nat) (x' y' : Expr)
    (h1 : machBits? ty = some w)
    (h2 : inst.isAppOf ``instBEqOfDecidableEq = true)
    (hx : lift x = some (w, x')) (hy : lift y = some (w, y')) :
    machBoolMapT lift dom (beqE us ty inst x y) = some (beqOut ty dom w x' y') := by
  first
    | (simp [machBoolMapT, beqE, beqOut, h1, h2, hx, hy]; done)
    | (unfold beqE; rw [machBoolMapT]; simp [beqOut, h1, h2, hx, hy]; done)
    | (unfold beqE; simp only [machBoolMapT]; simp [beqOut, h1, h2, hx, hy]; done)
    | (unfold beqE beqOut; simp [machBoolMapT, h1, h2, hx, hy, bind, pure]; done)

end Tools.ShippingReaderBoolMap
