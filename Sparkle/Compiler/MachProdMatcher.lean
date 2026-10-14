import Lean

/-! # The walk of `MachRawSurface.prodMatcherArity?`, total

`MachRawSurface.prodMatcherArity? env n` reads the arity of a matcher that
destructures one right-nested pair off the matcher's value; the walk down its
`Prod.casesOn` chain was a local `partial` function there,

    go : Lean.Expr → Nat → List Nat → Nat → Option Nat
      | e, subj, vars, depth =>
        match e.getAppFn, e.getAppArgs with
        | .const ``Prod.casesOn _, #[_, _, _, .bvar t, .lam _ _ (.lam _ _ rest _) _] =>
          if t != subj then none else
          go rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
        | .bvar hIdx, args =>
          if hIdx != depth then none else
          let expected := vars ++ [subj]
          if args.toList == expected.map Lean.Expr.bvar then some args.size else none
        | _, _ => none

`partial` because the recursive argument `rest` came out of the ARRAY
`e.getAppArgs`. `goS` below is the same walk by structural recursion on the
term: the arguments are read off the application spine (`argsS`), the first
arm's array pattern is the same five-argument application written as a
constructor pattern, the test is a parameter (the compiler passes its `==`).
No fuel, no bound, no new refusal. That it is the unique solution of the old
text's recursion equation (array form) is proved under `Tools/`
(`Tools.ShippingReaderMatcherArityArray.old_unique`,
`Tools.ShippingReaderMatcherArityReal`); this file has the definitions only.

Pure: no `Expr` is built, reduced or typed; only constructors are inspected. -/
namespace Sparkle.Compiler.MachProdMatcher
open Lean

/-- The arguments of an application in front of `acc`. -/
def argsAccS : Expr → List Expr → List Expr
  | .app f a, acc => argsAccS f (a :: acc)
  | _, acc => acc

/-- `e.getAppArgs`, as a list, structurally. -/
def argsS (e : Expr) : List Expr := argsAccS e []

/-- `==` on lists over the test `eqv`, structurally (`List.beq` at `eqv := (· == ·)`). -/
def listEqvS (eqv : Expr → Expr → Bool) : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => eqv a b && listEqvS eqv as bs
  | _, _ => false

/-- The walk down the `Prod.casesOn` chain and the leaf's test. `subj` is the
bvar index of the current subject; `vars` the component bvar indices met so
far (outermost first, relative to the current depth `depth` below the three
lambdas). -/
def goS (eqv : Expr → Expr → Bool) (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    Option Nat :=
  match e.getAppFn with
  | .bvar hIdx =>
    -- `h` sits at index `depth + 0` relative to the walk start (+2 per level)
    if hIdx != depth then none else
    if listEqvS eqv (argsS e) ((vars ++ [subj]).map Expr.bvar) then some (argsS e).length else none
  | _ =>
    match e with
    | .app (.app (.app (.app (.app (.const c _) _) _) _) (.bvar t))
        (.lam _ _ (.lam _ _ rest _) _) =>
      if c = ``Prod.casesOn then
        -- under two binders: fst = bvar 1, snd = bvar 0; earlier vars shift by 2
        if t != subj then none else goS eqv rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      else none
    | _ => none
termination_by structural e

end Sparkle.Compiler.MachProdMatcher
