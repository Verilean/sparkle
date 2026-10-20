import Lean

/-! # The pair type of the remaining components (`MachRawSurface.projChain`'s `tail`), total

`MachRawSurface.projChain regs tys j last` builds `regs.snd^j.fst` over the
component types `tys` of a right-nested pair; at level `i` it needs the type
of the second component, the pair of the components after position `i`.

That type was a local `partial` function of `projChain`,

    let rec tail : Nat → Option Lean.Expr
      | i => if i + 1 == tys.length - 1 then tys[tys.length - 1]?
        else do
          let a ← tys[i + 1]?
          let b ← tail (i + 1)
          some (mkApp2 (.const ``Prod [.zero, .zero]) a b)

which made `projChain` itself `partial` (opaque to the kernel). `tailAt tys`
below is the same function by structural recursion on the list: no fuel, no
bound, no new refusal. It is the unique solution of the recursion equation
above (`Tools.ShippingReaderProjChain.tailAt_eq`, `tail_unique`; the proofs
are under `Tools/`, this file has the definitions only).

Pure: no `Expr` is inspected, only `mkApp2` and list operations. -/
namespace Sparkle.Compiler.MachProjChain
open Lean

/-- `Prod a b`, as the compiler writes it. -/
def prodE (a b : Expr) : Expr := mkApp2 (.const ``Prod [.zero, .zero]) a b

/-- The right-nested pair type of a non-empty list of component types: the
last one alone, `Prod a (…)` before it. -/
def tailTy : List Expr → Option Expr
  | [] => none
  | a :: rest =>
    match rest with
    | [] => some a
    | _ :: _ => (tailTy rest).map (prodE a)

/-- `projChain`'s `tail i`: the pair type of the components after position
`i`. -/
def tailAt (tys : List Expr) (i : Nat) : Option Expr := tailTy (tys.drop (i + 1))

end Sparkle.Compiler.MachProjChain
