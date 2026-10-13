import Lean
import Tools.ShippingReaderProjChainShadow

/-! # What the reader-unit shadow comparisons share

WRITTEN, NOT BUILT (par/h-1). Measurement helpers only; no theorem. It
imports unit 1's shadow (`Tools/ShippingReaderProjChainShadow.lean`) and
reuses its `emit`, `bs`, `marker`, `sameOpt` and `roots`; what that file has
inline in its `sweep` (the collection of the definitions under the roots) is
a function here, for the later units. -/
namespace Tools.ShippingReaderSweep
open Lean Meta
open Tools.ShippingReaderProjChainShadow (roots)

/-- The constant is declared in a module under one of the roots (`Sparkle`,
`Tests`, `IP`, `Examples`, `Tools`) or in the current file. -/
def underRoots (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => roots.contains m.getRoot
    | none => false
  | none => true

/-- The definitions under the roots (the set unit 1's sweep scans). -/
def collectDefs (env : Environment) : Array Name :=
  env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .defnInfo _ => if underRoots env n then acc.push n else acc
    | _ => acc

/-- Every constant of the environment. -/
def collectAll (env : Environment) : Array Name :=
  env.constants.fold (init := (#[] : Array Name)) fun acc n _ => acc.push n

/-- The same length and `Expr.equal` at every position. -/
def sameList : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => a.equal b && sameList as bs
  | _, _ => false

def showNat (o : Option Nat) : String :=
  match o with
  | some k => s!"some {k}"
  | none => "none"

/-- One line of an exception's text. -/
def flat (text : String) : String := text.replace "\n" " | "

end Tools.ShippingReaderSweep
