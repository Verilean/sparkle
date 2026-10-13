import Lean
import Sparkle.Compiler.Elab

/-! # The machine reader's `machBoolMap`, total (reader generalisation, fourth unit)

WRITTEN, NOT BUILT (par/h-1). NOT wired into the reader: the compiler is not
edited and does not import this file (this file imports the compiler, for
`machBits?` and `inlNatLit`). Record: `docs/parallel/H-reader-units.md`.

## The function

`Sparkle.Compiler.Elab.machBoolMap senv dom a wa` (a `partial def`, Elab.lean
4819–4837) reads a `Bool`-valued lambda body over a `BitVec` Signal: an
equality of lifted operands, under any number of `!`. Its only recursion is
on `x` in the pattern `.app (.const c _) x` — a pattern subterm: structural
as written. It is `partial` because the equality arm calls
`machLiftScalarN`, a `partial` function (and nothing forces a `partial`
caller to be checked for termination).

## What is here

`machBoolMapT lift dom` — the compiler's text, verbatim, with ONE change:
the two calls `machLiftScalarN senv dom [(wa, a)] ·` are a PARAMETER
`lift : Expr → Option (Nat × Expr)`. Structural recursion, no fuel. At
`lift := machLiftScalarN senv dom [(wa, a)]` it is the compiler's function
(by reading: the same text; measured by the shadow).

Proved (about the new definition, for every `lift`):

* `machBoolMapT_not` — the equation of the recursive arm;
* `machBoolMapT_not_isSome` — under a `!` the function returns a result
  exactly when it does on the operand: the recursive arm neither adds nor
  loses an accepted input;
* `machBoolMapT_not_some` / `machBoolMapT_not_none` / `machBoolMapT_other`;
* `machBoolMapT_nots_isSome` — the same through any number of `!`.

The equality arm (`machBoolMapT_beq_some`) is in
`Tools/ShippingReaderBoolMapLeaf.lean` (a blind `simp` proof through a `do`
block; separate so that a failure there does not block this file).

NOT proved: uniqueness of the solution of the recursion equation (the
recursion is structural, so it is provable by induction on the term; not
attempted here); anything about `machLiftScalarN` (a parameter: the next
function on the map).

## The boundary

1. `machBoolMap` is `partial`: an opaque constant; no kernel equation with
   it exists, none is assumed.
2. `machLiftScalarN` is `partial` too. As long as it is, a `machBoolMap`
   made total still has an opaque callee: the switch-over of this function
   alone removes one `partial` and nothing else.

Well-typedness premises: none. -/
namespace Tools.ShippingReaderBoolMap
open Lean
open Sparkle.Compiler.Elab (machBits? inlNatLit)

/-- `machBoolMap` (Elab.lean 4819–4837), total: the same text, the lifting
of the operands a parameter. -/
def machBoolMapT (lift : Lean.Expr → Option (Nat × Lean.Expr)) (dom : Lean.Expr) :
    Lean.Expr → Option Lean.Expr
  | .app (.const c _) x =>
    if c == ``Bool.not || c == ``not then do
      let x' ← machBoolMapT lift dom x
      some (mkApp3 (.const ``Complement.complement [.zero])
        (mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (.const ``Bool []))
        (mkApp (.const ``Sparkle.Core.Signal.instComplementSignalBool []) dom) x')
    else none
  | .app (.app (.app (.app (.const ``BEq.beq _) ty) inst) x) y => do
    let w ← machBits? ty
    unless inst.isAppOf ``instBEqOfDecidableEq do none
    let (wx, x') ← lift x
    let (wy, y') ← lift y
    if wx != w || wy != w then none else
    some (mkApp5 (.const ``Sparkle.Core.Signal.Signal.beq []) ty dom
      (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty
        (mkApp (.const ``instDecidableEqBitVec []) (inlNatLit w))) x' y')
  | _ => none

/-- The Signal's `Bool` complement of `x'`, as the compiler writes it. -/
def complE (dom x' : Expr) : Expr :=
  mkApp3 (.const ``Complement.complement [.zero])
    (mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (.const ``Bool []))
    (mkApp (.const ``Sparkle.Core.Signal.instComplementSignalBool []) dom) x'

/-- The test of the recursive arm: the head constant is `!`. -/
def isNot (c : Name) : Bool := c == ``Bool.not || c == ``not

/-- THE EQUATION OF THE RECURSIVE ARM. -/
theorem machBoolMapT_not (lift : Expr → Option (Nat × Expr)) (dom : Expr) (c : Name)
    (us : List Level) (x : Expr) :
    machBoolMapT lift dom (.app (.const c us) x) =
      if isNot c then (machBoolMapT lift dom x).bind fun x' => some (complE dom x')
      else none := by
  first
    | rfl
    | (rw [machBoolMapT]; rfl)
    | (simp only [machBoolMapT]; rfl)
    | (unfold machBoolMapT; rfl)
    | (simp [machBoolMapT, isNot, complE]; done)

theorem machBoolMapT_not_some (lift : Expr → Option (Nat × Expr)) (dom : Expr) (c : Name)
    (us : List Level) (x x' : Expr) (hc : isNot c = true)
    (hx : machBoolMapT lift dom x = some x') :
    machBoolMapT lift dom (.app (.const c us) x) = some (complE dom x') :=
  (machBoolMapT_not lift dom c us x).trans
    ((if_pos hc).trans
      (congrArg (fun o : Option Expr => o.bind fun x' => some (complE dom x')) hx))

theorem machBoolMapT_not_none (lift : Expr → Option (Nat × Expr)) (dom : Expr) (c : Name)
    (us : List Level) (x : Expr) (hc : isNot c = true)
    (hx : machBoolMapT lift dom x = none) :
    machBoolMapT lift dom (.app (.const c us) x) = none :=
  (machBoolMapT_not lift dom c us x).trans
    ((if_pos hc).trans
      (congrArg (fun o : Option Expr => o.bind fun x' => some (complE dom x')) hx))

/-- A constant that is not `!`, applied to one argument: refused. -/
theorem machBoolMapT_other (lift : Expr → Option (Nat × Expr)) (dom : Expr) (c : Name)
    (us : List Level) (x : Expr) (hc : isNot c = false) :
    machBoolMapT lift dom (.app (.const c us) x) = none :=
  (machBoolMapT_not lift dom c us x).trans
    (if_neg (fun h => Bool.noConfusion (hc.symm.trans h)))

theorem isSome_bind_some {α β : Type} (o : Option α) (g : α → β) :
    (o.bind fun a => some (g a)).isSome = o.isSome := by
  cases o with
  | none => rfl
  | some a => rfl

/-- **The recursive arm neither adds nor loses an accepted input.** -/
theorem machBoolMapT_not_isSome (lift : Expr → Option (Nat × Expr)) (dom : Expr) (c : Name)
    (us : List Level) (x : Expr) (hc : isNot c = true) :
    (machBoolMapT lift dom (.app (.const c us) x)).isSome =
      (machBoolMapT lift dom x).isSome :=
  (congrArg Option.isSome
    ((machBoolMapT_not lift dom c us x).trans (if_pos hc))).trans
    (isSome_bind_some (machBoolMapT lift dom x) (complE dom))

/-- `!` applied `cs.length` times (each with its own constant and levels). -/
def notsE : List (Name × List Level) → Expr → Expr
  | [], x => x
  | (c, us) :: cs, x => .app (.const c us) (notsE cs x)

/-- The same through any number of `!`. -/
theorem machBoolMapT_nots_isSome (lift : Expr → Option (Nat × Expr)) (dom : Expr) (x : Expr) :
    ∀ (cs : List (Name × List Level)), (∀ p, p ∈ cs → isNot p.1 = true) →
      (machBoolMapT lift dom (notsE cs x)).isSome = (machBoolMapT lift dom x).isSome
  | [], _ => rfl
  | (c, us) :: cs, h =>
    (machBoolMapT_not_isSome lift dom c us (notsE cs x)
      (h (c, us) (List.Mem.head cs))).trans
      (machBoolMapT_nots_isSome lift dom x cs
        (fun p hp => h p (List.Mem.tail (c, us) hp)))

end Tools.ShippingReaderBoolMap
