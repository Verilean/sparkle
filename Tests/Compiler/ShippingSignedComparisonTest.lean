import Tools.ShippingMixedExecutionSoundness
import Tests.Compiler.ShippingMixedExecutionTest

namespace Sparkle.Tests.Compiler.ShippingSignedComparisonTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMuxLoweringSoundness

def signedLt {dom : DomainConfig} (a b : Signal dom (BitVec 8)) := Signal.slt a b
def signedLe {dom : DomainConfig} (a b : Signal dom (BitVec 8)) := Signal.sle a b
def signedOne {dom : DomainConfig} (a b : Signal dom (BitVec 1)) := Signal.slt a b
def signedWide {dom : DomainConfig} (a b : Signal dom (BitVec 65)) := Signal.sle a b
def nested {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux (Signal.slt (a + b) b)
    (Signal.mux c (Signal.sle (a - b) b) (Signal.ult a b)) (Signal.sle (a * b) a)

#def_decl_value nestedValue of nested

def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
def term : BExpr := .mux (.compare .slt (.bin .add (.inp 0) (.inp 1)) (.inp 1))
  (.mux (.inp 0) (.compare .sle (.bin .sub (.inp 0) (.inp 1)) (.inp 1))
    (.compare .ult (.inp 0) (.inp 1)))
  (.compare .sle (.bin .mul (.inp 0) (.inp 1)) (.inp 0))

theorem term_wf : term.WF 1 2 8 := by simp [term, BExpr.WF, FExpr.WF]
theorem nested_peel : mixedGatePeel nestedValue = some (binders,
    quoteB (.bvar 3) 8 (fun _ => inputExpr binders.length 1)
      (fun j => inputExpr binders.length (j + 2)) term) := rfl

theorem nested_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``nested) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``nested nestedValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``nested binders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems (encodeBool
        ((nested (bools 1) (bits 2 8) (bits 3 8)).val tick)) := by
  apply execution_source_of_env hr env (by rfl) nested_peel (by decide) term_wf
  · intro j _; exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.SVParser.AST Tools.SVParser.EmitSem Tools.SVParser.EmitAst
open Tools.ShippingDeclWidths Tools.ShippingModulePrintSoundness Tools.ShippingSVBridge
open ShippingMixedExecutionTest in
run_cmd liftTermElabM do
  let mut cases := 0
  for (name, n) in [( ``signedLt, 8), (``signedLe, 8), (``signedOne, 1), (``signedWide, 65), (``nested, 8)] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "signed source missed proved gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (translateFuelFix (fun rec e h t named =>
        Rec.translateExprToWireCached rec e h t named) translateFuelLimit) name [] false false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "signed semantic/order checks failed"
      let some sv := emitAstModule m | throwError "signed AST emission failed"
      let some pairs := combItems sv.items | throwError "signed body extraction failed"
      let widths := astWidths sv
      let names := (declarationTable sv).map Prod.fst
      for c in [false, true] do
        for a in [0, 1, 2^(n-1)-1, 2^(n-1), 2^n-1] do
          for b in [0, 1, 2^(n-1)-1, 2^(n-1), 2^n-1] do
            let av := BitVec.ofNat n a
            let bv := BitVec.ofNat n b
            let expected := encodeBool <| if name == ``nested then
                if BitVec.slt (av + bv) bv then
                  if c then BitVec.sle (av - bv) bv else BitVec.ult av bv
                else BitVec.sle (av * bv) av
              else if name == ``signedLt || name == ``signedOne then BitVec.slt av bv
              else BitVec.sle av bv
            let values := if name == ``nested then [encodeBool c, a, b] else [a, b]
            let legacyInit := fun w =>
              (((legacy.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
            unless (evalAssigns (Tools.ShippingEntrySoundness.weOf legacy) (fun _ _ => 0)
                legacy.body legacyInit).map (· "out") == some expected do
              throwError "signed legacy/source mismatch: {name}"
            for seed in [0, 1, 2^n-1] do
              let initial := fun w =>
                match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
                | some (_, v) => v
                | none => mask ((widths w).getD 0) seed
              let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
                throwError "signed SV evaluation failed"
              let mut current := initial
              for _ in [:pairs.length] do
                let some next := parallelRound widths pairs current | throwError "signed delta failed"
                current := next
              let some extra := parallelRound widths pairs current | throwError "signed stable round failed"
              unless observeUnsignedOutput sv current "out" == some expected &&
                  names.all (fun x => current x == stable x && extra x == stable x) do
                throwError "signed source/SV/delta mismatch: {name}, {a}, {b}"
              cases := cases + 1
  unless cases == 2250 do throwError "signed case count mismatch"
  logInfo m!"SIGNED SHIPPING EXECUTION: {cases} source/legacy/SV/delta cases, widths 1/8/65 and sign boundaries"

run_cmd do
  if (← get).messages.hasErrors then throwError "signed comparison regression failed"
  for name in [``Tools.ShippingCompareLoweringSoundness.signed_toInt,
      ``Tools.ShippingCompareLoweringSoundness.compare_rhs_correct,
      ``Tools.ShippingMixedRecursion.bool_fuel_contract,
      ``Tools.ShippingMixedOrderSoundness.bool_fuel_orders,
      ``execution_source_of_env, ``nested_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected signed execution axiom: {name}: {ax}"
  logInfo "SIGNED ENDPOINT: recursive slt/sle through shipping syntax and finite settling; standard axioms only"

end Sparkle.Tests.Compiler.ShippingSignedComparisonTest
