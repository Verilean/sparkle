import Tools.ShippingMixedExecutionSoundness
import Tests.Compiler.ShippingMixedExecutionTest

namespace Sparkle.Tests.Compiler.ShippingBoolEqualityTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMuxLoweringSoundness

def equal {dom : DomainConfig} (a b : Signal dom Bool) := Signal.beq a b
def equalSelf {dom : DomainConfig} (a _b : Signal dom Bool) := Signal.beq a a
def equalTrue {dom : DomainConfig} (a : Signal dom Bool) := Signal.beq a (Signal.pure true)
def nested {dom : DomainConfig} (a b c : Signal dom Bool) (x y : Signal dom (BitVec 8)) :=
  Signal.beq (Signal.mux a (Signal.beq b c) (Signal.beq x y))
    (Signal.beq (Signal.ult (x + y) y) (Signal.beq a b))

@[reducible] def customBEq : BEq Bool := ⟨fun a b => a && !b⟩
def custom {dom : DomainConfig} (a b : Signal dom Bool) :=
  @Signal.beq Bool dom customBEq a b

#def_decl_value nestedValue of nested

def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bool), (`b, .bool), (`c, .bool), (`x, .bits 8), (`y, .bits 8)]
def term : BExpr := .boolEq
  (.mux (.inp 0) (.boolEq (.inp 1) (.inp 2)) (.compare .eq (.inp 0) (.inp 1)))
  (.boolEq (.compare .ult (.bin .add (.inp 0) (.inp 1)) (.inp 1)) (.boolEq (.inp 0) (.inp 1)))
theorem term_wf : term.WF 3 2 8 := by simp [term, BExpr.WF, FExpr.WF]
theorem nested_peel : mixedGatePeel nestedValue = some (binders,
    quoteB (.bvar 5) 8 (fun j => inputExpr binders.length (j + 1))
      (fun j => inputExpr binders.length (j + 4)) term) := rfl

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
        ((nested (bools 1) (bools 2) (bools 3) (bits 4 8) (bits 5 8)).val tick)) := by
  apply execution_source_of_env hr env (by rfl) nested_peel (by decide) term_wf
  · intro j hj
    have h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases h with rfl | rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩
    · exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`x, rfl⟩
    · exact ⟨`y, rfl⟩

open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.SVParser.AST Tools.SVParser.EmitSem Tools.SVParser.EmitAst
open Tools.ShippingDeclWidths Tools.ShippingModulePrintSoundness Tools.ShippingSVBridge
open ShippingMixedExecutionTest in
run_cmd liftTermElabM do
  let mut count := 0
  for name in [``equal, ``equalSelf, ``equalTrue, ``nested] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "Bool equality missed proved gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (translateFuelFix (fun rec e h t named =>
        Rec.translateExprToWireCached rec e h t named) translateFuelLimit) name [] false false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "Bool equality semantic/order checks failed"
      let some sv := emitAstModule m | throwError "Bool equality AST emission failed"
      let some pairs := combItems sv.items | throwError "Bool equality body extraction failed"
      let widths := astWidths sv
      let names := (declarationTable sv).map Prod.fst
      let inputs := if name == ``nested then
          (List.range 8).flatMap fun flags => [0, 1, 127, 128, 255].flatMap fun x =>
            [0, 1, 127, 128, 255].map fun y => [flags % 2, flags / 2 % 2, flags / 4, x, y]
        else if name == ``equalTrue then [[0], [1]]
        else [[0, 0], [0, 1], [1, 0], [1, 1]]
      for values in inputs do
        let a := values[0]! == 1
        let b := values[1]?.getD 0 == 1
        let expected := encodeBool <| if name == ``nested then
            let c := values[2]! == 1
            let x := BitVec.ofNat 8 values[3]!
            let y := BitVec.ofNat 8 values[4]!
            (if a then b == c else x == y) == (BitVec.ult (x + y) y == (a == b))
          else if name == ``equalSelf then true
          else if name == ``equalTrue then a else a == b
        let legacyInit := fun w =>
          (((legacy.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
        unless (evalAssigns (Tools.ShippingEntrySoundness.weOf legacy) (fun _ _ => 0)
            legacy.body legacyInit).map (· "out") == some expected do
          throwError "Bool equality legacy/source mismatch: {name}, {values}"
        for seed in [0, 1, 255] do
          let initial := fun w =>
            match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
            | some (_, v) => v
            | none => mask ((widths w).getD 0) seed
          let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
            throwError "Bool equality SV evaluation failed"
          let mut current := initial
          for _ in [:pairs.length] do
            let some next := parallelRound widths pairs current | throwError "Bool equality delta failed"
            current := next
          let some extra := parallelRound widths pairs current | throwError "Bool equality stable round failed"
          unless observeUnsignedOutput sv current "out" == some expected &&
              names.all (fun x => current x == stable x && extra x == stable x) do
            throwError "Bool equality source/SV/delta mismatch: {name}, {values}"
          count := count + 1
  unless count == 1890 do throwError "Bool equality case count mismatch: {count}"
  logInfo m!"BOOL EQUALITY EXECUTION: {count} source/legacy/SV/delta cases; nested mixed comparisons and aliases"

run_cmd liftTermElabM do
  unless (mixedCertifiedShape? false [] (← getConstInfo ``custom)).isNone do
    throwError "custom Bool BEq entered proved gate"
  let (m, _) ← synthesizeCombinational ``custom
  for a in [false, true] do
    for b in [false, true] do
      let initial := fun w => if w == m.inputs[0]!.name then encodeBool a else
        if w == m.inputs[1]!.name then encodeBool b else 0
      unless (evalAssigns (Tools.ShippingEntrySoundness.weOf m) (fun _ _ => 0)
          m.body initial).map (· "out") == some (encodeBool (a && !b)) do
        throwError "custom Bool BEq meaning changed"
  logInfo "BOOL EQUALITY INSTANCE GUARD: custom asymmetric BEq preserved on every input"

run_cmd do
  if (← get).messages.hasErrors then throwError "Bool equality regression failed"
  for name in [``Tools.ShippingMixedRecursion.bool_fuel_contract,
      ``Tools.ShippingMixedOrderSoundness.bool_fuel_orders,
      ``execution_source_of_env, ``nested_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected Bool equality axiom: {name}: {ax}"
  logInfo "BOOL EQUALITY ENDPOINT: shipping source, syntax and finite settling; standard axioms only"

end Sparkle.Tests.Compiler.ShippingBoolEqualityTest
