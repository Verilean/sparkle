import Lean
import Sparkle
import Tools.ShippingGen5RowTypedV
set_option autoImplicit false
namespace Tests.Gen5.V2Check
open Lean Tools.ShippingGen5ConstValueESL

def nBinders : Expr → Nat
  | .forallE _ _ B _ => nBinders B + 1
  | _ => 0
def resultOf : Expr → Expr
  | .forallE _ _ B _ => resultOf B
  | e => e
def binderTys : Expr → List Expr
  | .forallE _ A B _ => A :: binderTys B
  | _ => []

run_meta do
  let env ← getEnv
  let DC := `Sparkle.Core.Domain.DomainConfig
  let mut total : Nat := 0
  let mut shape : Nat := 0
  let mut other : Array Name := #[]
  let mut depB : Nat := 0
  let mut names : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if let .ctorInfo _ := ci then
      let T := instantiateLevelParamsS ci.levelParams (ci.levelParams.map fun _ => Level.zero) ci.type
      match T with
      | .forallE _ (.const d []) _ _ =>
        if d == DC then
          total := total + 1
          let n := nBinders T
          let R := resultOf T
          let ok := match R with
            | .app (.const _ _) (.bvar j) => j + 1 == n
            | _ => false
          if ok then shape := shape + 1; names := names.push c else other := other.push c
          let tys := binderTys T
          let mut i : Nat := 0
          let mut anyDep := false
          for A in tys do
            if i > 0 && Tools.ShippingGen5ConstValueESoundK.lbr A > 0 then anyDep := true
            i := i + 1
          if anyDep then depB := depB + 1
      | _ => pure ()
  logInfo m!"ctors with first binder DomainConfig: {total}; dep-first shape {shape}; other {other}; with dependent later binder types {depB}"
  logInfo m!"{names.qsort (·.toString < ·.toString)}"
