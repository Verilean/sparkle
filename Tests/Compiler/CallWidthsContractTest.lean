import Tests.Compiler.ShippingMachineSeqTest
import Tools.ShippingCallWidthsStrict
import Tools.ShippingCallShadow

/-! # What `true` means for the call-width conditions (finding A) — negative tests

Kernel-checked by `decide`: a wrong expectation is a build error.

The conditions `callWidthsOk` (`Tools/ShippingCallWidths.lean`),
`callWidthsStrict` (`Tools/ShippingCallWidthsStrict.lean`) and the shadow
report (`Tools/ShippingCallShadow.lean`) are evaluated on `parent`'s
reflected data (`Tests/Compiler/ShippingMachineSeqTest.lean`: two entries
of one call of `cnt`, fields `n : BitVec 8` and `hit : Bool`, `nDecl = 1`)
against HAND-MADE child layouts, and on `parent`'s data with
`instFields := []` (the shape of a one-output closing).

| case | child layout | `callWidthsOk` | `callWidthsStrict` |
|---|---|---|---|
| `good` | `n : 8`, `hit : bit` | true | true |
| `named_mismatch` | `n : 7`, `hit : bit` | false | false |
| `oneOut_mismatch` (`instFields = []`) | one output of 3 bits | **true** (vacuous) | false |
| `missing_field` | one output `zzz` only | **true** | **true** |
| `empty_outputs` | none | **true** | **true** |
| `oneOut_empty` (`instFields = []`) | none | **true** | **true** |

So `true` — for BOTH conditions — means only: every layout output that the
entry's name test selects has the binder's width. It does NOT say that the
field exists, that a one-output child has an output, or anything about
arguments. Those are facts of the real closing
(`docs/parallel/B-callkinds.md` §6) and must be combined with it.

The shadow report: an entry without a signature is `unknown` and "agrees"
only as "nothing compared"; with a signature the kinds of failure are
separate.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.CallWidthsContractTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingMachineAuto
open Tools.ShippingCallWidths (callWidthsOk)
open Tools.ShippingCallWidthsStrict (callWidthsStrict)
open Tools.ShippingCallShadow

def outN (w : Nat) : OutField := { name := "n", lo := 1, width := w, ty := .bitVector w }
def outHit : OutField := { name := "hit", lo := 0, width := 1, ty := .bit }
def outOther : OutField := { name := "zzz", lo := 0, width := 3, ty := .bitVector 3 }

/-- `parent`'s data as a one-output closing would see it. -/
noncomputable def dOne : MachineData :=
  { parent.machineData with shape := { parent.machineData.shape with instFields := [] } }

/-! ## The two data conditions -/

theorem good :
    callWidthsOk parent.machineData 1 (fun _ => [outN 8, outHit]) = true ∧
    callWidthsStrict parent.machineData 1 (fun _ => [outN 8, outHit]) = true := by decide

theorem named_mismatch :
    callWidthsOk parent.machineData 1 (fun _ => [outN 7, outHit]) = false ∧
    callWidthsStrict parent.machineData 1 (fun _ => [outN 7, outHit]) = false := by decide

/-- The vacuity: on a one-output closing the old condition accepts a child
whose only output has another width; the strict one does not. -/
theorem oneOut_mismatch :
    callWidthsOk dOne 1 (fun _ => [outOther]) = true ∧
    callWidthsStrict dOne 1 (fun _ => [outOther]) = false := by decide

/-- A MISSING field passes both: existence is not what they test. -/
theorem missing_field :
    callWidthsOk parent.machineData 1 (fun _ => [outOther]) = true ∧
    callWidthsStrict parent.machineData 1 (fun _ => [outOther]) = true := by decide

/-- An EMPTY output list passes both. -/
theorem empty_outputs :
    callWidthsOk parent.machineData 1 (fun _ => []) = true ∧
    callWidthsStrict parent.machineData 1 (fun _ => []) = true := by decide

theorem oneOut_empty :
    callWidthsOk dOne 1 (fun _ => []) = true ∧
    callWidthsStrict dOne 1 (fun _ => []) = true := by decide

/-! ## The shadow report -/

/-- No signature: unknown, nothing compared. -/
theorem shadow_unknown :
    (entryReport [.bits 8] 0 1 "out" [] {}).unknown = true ∧
    (entryReport [.bits 8] 0 1 "out" [] {}).agrees = true := by decide

/-- A known signature with another result kind. -/
theorem shadow_resKind :
    (entryReport [.bits 8] 0 1 "out" []
      { selected := some { outs := [("out", .bits 7)], ins := [] } }).sel.resKind = true ∧
    (entryReport [.bits 8] 0 1 "out" []
      { selected := some { outs := [("out", .bits 7)], ins := [] } }).agrees = false := by decide

/-- A known signature without the field. -/
theorem shadow_missing :
    (entryReport [.bits 8] 0 1 "out" []
      { selected := some { outs := [("x", .bits 8)], ins := [] } }).sel.fieldMissing = true ∧
    (entryReport [.bits 8] 0 1 "out" []
      { selected := some { outs := [("x", .bits 8)], ins := [] } }).sel.resKind = false := by decide

/-- A known signature with another number of arguments: a count
difference, not a kind difference. -/
theorem shadow_argCount :
    (entryReport [.bits 8] 0 1 "out" []
      { selected := some { outs := [("out", .bits 8)], ins := [.bool] } }).sel.argCount = true ∧
    (entryReport [.bits 8] 0 1 "out" []
      { selected := some { outs := [("out", .bits 8)], ins := [.bool] } }).sel.argKind = false := by
  decide

/-- An argument of another kind, the counts equal. -/
theorem shadow_argKind :
    (entryReport [.bits 8, .bits 4] 0 1 "out" [0]
      { selected := some { outs := [("out", .bits 8)], ins := [.bits 5] } }).sel.argKind = true ∧
    (entryReport [.bits 8, .bits 4] 0 1 "out" [0]
      { selected := some { outs := [("out", .bits 8)], ins := [.bits 5] } }).sel.argCount = false := by
  decide

/-- Only the signature that is not selected disagrees: an over-decline of
a rule that asks agreement with both. -/
theorem shadow_overDecline :
    (entryReport [.bits 8] 0 1 "out" []
      { declared := some { outs := [("out", .bits 7)], ins := [] }
        inlined := some { outs := [("out", .bits 8)], ins := [] }
        selected := some { outs := [("out", .bits 8)], ins := [] }
        selInlined := true }).overDecline = true := by decide

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``good, ``named_mismatch, ``oneOut_mismatch, ``missing_field, ``empty_outputs,
      ``oneOut_empty, ``shadow_unknown, ``shadow_resKind, ``shadow_missing, ``shadow_argCount,
      ``shadow_argKind, ``shadow_overDecline] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CALLWIDTHS CONTRACT: 12 expectations hold (good, named_mismatch, oneOut_mismatch: old true / strict false, missing_field: both true, empty_outputs: both true, oneOut_empty: both true, shadow_unknown, shadow_resKind, shadow_missing, shadow_argCount, shadow_argKind, shadow_overDecline) — standard axioms only"

end Tests.Compiler.CallWidthsContractTest
