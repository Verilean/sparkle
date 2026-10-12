import Sparkle.IR.RefineCheck
import Sparkle.IR.HierCheck

/-! # The optimizer's guards and fallback on hand-built modules (branch `fix/opt-fallback`)

Compiled checks (a failure throws):

* G2 (`linkedWFX`): a body in which an assignment READS an instance-driven
  wire BEFORE its instance is refused; the same statements in the linked
  order are accepted; `keepGuarded` returns the input module for the
  refused candidate and the candidate for the accepted one.
* G4: a candidate that repeats an instance name is replaced by the input
  module.
* the fallback: an instance / assignment module whose assignment is outside
  the normal forms (a constant that does not fit its width) passes
  `hierGate`, fails `hierBinds`, and `checkedOptimize` returns it UNCHANGED
  (before this branch: the unchecked optimizer output). -/
namespace Tests.Compiler.OptFallbackTest
open Sparkle.IR.AST Sparkle.IR.HierCheck

def wBit (n : String) : Port := { name := n, ty := .bit }

def instSt : Stmt := .inst "child" "u0" [("o", .ref "w")]
def readSt : Stmt := .assign "y" (.ref "w")

/-- The input module: the instance, then the assignment reading its output. -/
def mGood : Module :=
  { name := "m", inputs := [], outputs := [wBit "y"], wires := [wBit "w", wBit "y"],
    body := [instSt, readSt] }

/-- A candidate with the assignment BEFORE the instance. -/
def oReordered : Module := { mGood with body := [readSt, instSt] }

/-- A candidate repeating the instance name. -/
def oTwice : Module := { mGood with body := [instSt, instSt, readSt] }

/-- An instance / assignment module outside the normal forms. -/
def mOutside : Module :=
  { name := "m2", inputs := [], outputs := [wBit "y"], wires := [wBit "w", wBit "y"],
    body := [instSt, .assign "y" (.const 5 1)] }

open Lean Elab Command in
run_cmd liftTermElabM do
  let X := (openIns mGood).map (·.name)
  unless X == ["w"] do throwError "openIns mGood = {X}, expected [w]"
  unless linkedWFX X mGood.body do throwError "G2 refuses the linked order"
  if linkedWFX X oReordered.body then throwError "G2 accepts a read before the instance"
  unless keepGuarded mGood mGood == mGood do throwError "keepGuarded changes an accepted candidate"
  unless keepGuarded mGood oReordered == mGood do
    throwError "keepGuarded keeps a candidate out of the linked order"
  if decide (instNamesOf oTwice.body).Nodup then throwError "G4 accepts a repeated instance name"
  unless keepGuarded mGood oTwice == mGood do
    throwError "keepGuarded keeps a candidate repeating an instance name"
  unless Sparkle.IR.RefineCheck.hierGate mOutside do throwError "mOutside fails hierGate"
  if Sparkle.IR.RefineCheck.hierBinds mOutside then throwError "mOutside binds (expected not)"
  unless Sparkle.IR.OptCheck.checkedOptimize mOutside == mOutside do
    throwError "checkedOptimize changed a module on which the check does not bind"
  let line : String :=
    "OPT FALLBACK: G2 refuses a read before its instance and accepts the linked order; " ++
    "G4 refuses a repeated instance name; keepGuarded falls back to the input module on both; " ++
    "checkedOptimize returns an instance module outside the normal forms unchanged " ++
    "(hierGate true, hierBinds false)"
  logInfo m!"{line}"

end Tests.Compiler.OptFallbackTest
