import Tools.ShippingFGCircuitS2bShare
set_option autoImplicit false
-- FG circuit pilot S2b: sharing-PRESERVING versions of the table evaluators (the generator side of route N1: `Expr.instantiate1` keeps the DAG, `instE` rebuilds a tree).
-- UNTRUSTED: these are used by the generator only to COMPUTE the next expression; the kernel re-checks every step against the table evaluators `whStepRL`/`unfoldL`/`headRedexRL` (`Eq.refl`).
namespace Tools.ShippingFGCircuitS2bNative
open Lean Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1wTbl

def natBeta : Expr → List Expr → Expr
  | f, [] => f
  | .lam _ _ b _, a :: xs => natBeta (b.instantiate1 a) xs
  | f, a :: xs => mkApps f (a :: xs)

def unfoldN (lk : Look) (e : Expr) : Option (Option Expr) :=
  match appFn e with
  | .const c ls =>
    match lk c with
    | none => none
    | some (.defn r) => some (if r.lps.length = ls.length then some (natBeta (instLE r.lps ls r.value) (appArgs e)) else none)
    | some _ => some none
  | _ => some none

def whStepN (lk : Look) : Expr → Option (Option Expr)
  | .letE _ _ v b _ => some (some (b.instantiate1 v))
  | .proj s j y =>
    match whStepN lk y with
    | none => none
    | some (some y') => some (some (.proj s j y'))
    | some none =>
      match iotaL lk s j y with
      | none => none
      | some (some r) => some (some r)
      | some none =>
        match recStepL lk y with
        | none => none
        | some o => some (o.map fun y' => .proj s j y')
  | .app f a =>
    match f with
    | .lam _ _ b _ => some (some (b.instantiate1 a))
    | .letE _ _ v b _ => some (some (.app (b.instantiate1 v) a))
    | _ => (whStepN lk f).map fun o => o.map fun f' => .app f' a
  | x => unfoldN lk x

def headRedexN (lk : Look) (e : Expr) : Option (Option Expr) :=
  match appFn e, appArgs e with
  | .lam .., _ :: _ => some (some (natBeta (appFn e) (appArgs e)))
  | .letE _ _ v b _, _ :: _ => some (some (mkApps (b.instantiate1 v) (appArgs e)))
  | .proj s j y, _ :: _ => (whStepN lk (.proj s j y)).map fun o => o.map fun h' => mkApps h' (appArgs e)
  | _, _ => some none


end Tools.ShippingFGCircuitS2bNative
