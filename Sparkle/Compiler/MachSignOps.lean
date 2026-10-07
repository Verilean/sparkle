import Lean
import Sparkle.Core.Signal

/-! # Sign extension and arithmetic right shift on the machine route

`BitVec.signExtend` / `BitVec.sshiftRight` (and `Signal.ashr`) are read in
their derived form over the certified operators — the sign bit a 1-bit slice
compared with `1#1`, `fill` a mux of two literals:

* `signExtend (k + w) x` ↦ `fill k (msb x) ++ x`,
* `x.sshiftRight y` ↦ `((x ^^^ M) >>> y) ^^^ M`, `M = fill w (msb x)`.

These are the right-hand sides of `Tools.ShippingSignOps.map_signExtend` /
`ashr_eq` / `map_sshiftRight`; the endpoint generator rewrites the
declaration with those equations, so the reader's form and the rewritten
source agree by the kernel's evaluation. The builders take the reader's
`Nat`-literal and Signal-operator builders as arguments (they live in
`Elab.lean`). -/
namespace Sparkle.Compiler.MachSignOps
open Lean

/-- `BitVec n` at a literal width. -/
def bvT (natE : Nat → Lean.Expr) (n : Nat) : Lean.Expr := mkApp (.const ``BitVec []) (natE n)

/-- The sign bit of a `BitVec w` Signal: `x.map (extractLsb' (w-1) 1 ·) === pure 1#1`. -/
def msbE (natE : Nat → Lean.Expr) (dom : Lean.Expr) (w : Nat) (x : Lean.Expr) : Lean.Expr :=
  let slice := mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom (bvT natE w) (bvT natE 1)
    (.lam `v (bvT natE w)
      (mkApp4 (.const ``BitVec.extractLsb' []) (natE w) (natE (w - 1)) (natE 1) (.bvar 0)) .default) x
  let one := mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (bvT natE 1)
    (mkApp2 (.const ``BitVec.ofNat []) (natE 1) (natE 1))
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.beq []) (bvT natE 1) dom
    (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) (bvT natE 1)
      (mkApp (.const ``instDecidableEqBitVec []) (natE 1))) slice one

/-- `Signal.mux c (pure (2^k-1)#k) (pure 0#k)`. -/
def fillE (natE : Nat → Lean.Expr) (dom : Lean.Expr) (k : Nat) (c : Lean.Expr) : Lean.Expr :=
  let lit (v : Nat) := mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (bvT natE k)
    (mkApp2 (.const ``BitVec.ofNat []) (natE k) (natE v))
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.mux [.zero]) dom (bvT natE k) c (lit (2 ^ k - 1)) (lit 0)

/-- Sign extension of a `BitVec w` Signal to `k + w` bits; `concatE m n a b`
builds the reader's concatenation. -/
def sextE (natE : Nat → Lean.Expr) (concatE : Nat → Nat → Lean.Expr → Lean.Expr → Lean.Expr)
    (dom : Lean.Expr) (k w : Nat) (x : Lean.Expr) : Lean.Expr :=
  concatE k w (fillE natE dom k (msbE natE dom w x)) x

/-- Arithmetic right shift of a `BitVec w` Signal by a `BitVec w` Signal;
`binE m a b` builds the reader's operator `m` (`HXor.hXor`, `HShiftRight.hShiftRight`). -/
def ashrE (natE : Nat → Lean.Expr) (binE : Name → Lean.Expr → Lean.Expr → Lean.Expr)
    (dom : Lean.Expr) (w : Nat) (x y : Lean.Expr) : Lean.Expr :=
  let m := fillE natE dom w (msbE natE dom w x)
  binE ``HXor.hXor (binE ``HShiftRight.hShiftRight (binE ``HXor.hXor x m) y) m

end Sparkle.Compiler.MachSignOps
