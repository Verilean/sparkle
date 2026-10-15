import Tests.Compiler.GateConeUseTest
import Tests.Compiler.GateConeWrapAddTest
import Tests.Compiler.GateConeTwoCallsTest
import Tests.Compiler.GateConeRepeatTest
import Tests.Compiler.GateConeCmpTest
import Tests.Compiler.GateConeNestedTest
import Tests.Compiler.GateParentRunGTest

/-! # PROBE (logs only): is `GateDefines` satisfiable in the real environment?

TARGET-ONLY; not in `Tests.AllTests`. It asserts NOTHING (a log line per parent).

`Tools.ShippingGateDefines.GateDefines f bs body` says: for every run of
`getConstInfo f` and every run of `getEnv`, the entry read
`entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)`
is a definition `dv` refused by the first gate and accepted by the mixed gate
as `(bs, body)`. It is a reflection BINDER of the gate-parent theorems, never
proved. This probe evaluates that read ONCE, in this file's elaboration
environment (the environment a command in this file would capture), for the
seven gate-route parents, and compares the mixed gate's answer with the
reflected `(bs, body)` the theorems are instantiated at:

    GATEDEF START <decl>
    GATEDEF <decl>: defn=<T/F> first=<none/some> mixed=<none/some> binders==<T/F> body==<T/F>

`T T` on both comparisons is evidence (MEASURED, not proved) that the premise
is not vacuous for the environment of this file; it says nothing about other
environments (the premise quantifies over every `getEnv` run). -/
namespace Sparkle.Tests.Compiler.GateDefinesProbe
open Lean Meta Sparkle.Compiler.Elab

def probe (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr) :
    MetaM Unit := do
  IO.eprintln s!"GATEDEF START {declName}"
  let env ← getEnv
  let ci ← getConstInfo declName
  let ci' := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
  let isDefn := match ci' with | .defnInfo _ => true | _ => false
  let first := (certifiedShape? false [] ci').isSome
  let mixed := mixedCertifiedShape? false [] ci' (instancePredicate env)
  let (bEq, eEq) := match mixed with
    | some (bs', body') => (decide (bs' = bs), body' == body)
    | none => (false, false)
  let line := s!"GATEDEF {declName}: defn={isDefn} first={if first then "some" else "none"} mixed={if mixed.isSome then "some" else "none"} binders=={bEq} body=={eEq}"
  IO.eprintln line
  logInfo line

open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest in
run_cmd Lean.Elab.Command.liftTermElabM (probe ``parentUse parentUseBinders
  Sparkle.Tests.Compiler.GateParentRunGTest.parentUseBody)
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest in
run_cmd Lean.Elab.Command.liftTermElabM (probe ``wrapAdd wrapAddBinders
  Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAddBody)
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest in
run_cmd Lean.Elab.Command.liftTermElabM (probe ``parentMix parentMixBinders
  Sparkle.Tests.Compiler.GateConeRunTest.parentMixBody)
run_cmd Lean.Elab.Command.liftTermElabM (probe ``Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentTwoCalls
    Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBinders
    Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCallsBody)
run_cmd Lean.Elab.Command.liftTermElabM (probe ``Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentRepeat
    Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBinders
    Sparkle.Tests.Compiler.GateConeRepeatTest.parentRepeatBody)
run_cmd Lean.Elab.Command.liftTermElabM (probe ``Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentCmp
    Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBinders
    Sparkle.Tests.Compiler.GateConeCmpTest.parentCmpBody)
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest in
run_cmd Lean.Elab.Command.liftTermElabM (probe ``parentNested parentNestedBinders
  Sparkle.Tests.Compiler.GateConeNestedTest.parentNestedBody)

end Sparkle.Tests.Compiler.GateDefinesProbe
