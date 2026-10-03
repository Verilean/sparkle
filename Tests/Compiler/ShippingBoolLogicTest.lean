import Tools.ShippingMixedExecutionSoundness
import Tests.Compiler.ShippingMixedExecutionTest

namespace Sparkle.Tests.Compiler.ShippingBoolLogicTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMuxLoweringSoundness

def band {dom : DomainConfig} (a b : Signal dom Bool) := a &&& b
def bor {dom : DomainConfig} (a b : Signal dom Bool) := a ||| b
def bxor {dom : DomainConfig} (a b : Signal dom Bool) := a ^^^ b
def bnot {dom : DomainConfig} (a : Signal dom Bool) := ~~~a
def shared {dom : DomainConfig} (a b : Signal dom Bool) := (a &&& b) ^^^ (a &&& b)
def nested {dom : DomainConfig} (a b c : Signal dom Bool) (x y : Signal dom (BitVec 8)) :=
  Signal.beq ((a &&& b) ||| (~~~c ^^^ Signal.ult (x + y) y))
    (Signal.mux (Signal.beq x y) (a ^^^ a) (~~~(a ||| b)))

#def_decl_value nestedValue of nested

def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bool), (`b, .bool), (`c, .bool), (`x, .bits 8), (`y, .bits 8)]
def term : BExpr := .boolEq
  (.boolBin .bor (.boolBin .band (.inp 0) (.inp 1))
    (.boolBin .bxor (.boolNot (.inp 2)) (.compare .ult (.bin .add (.inp 0) (.inp 1)) (.inp 1))))
  (.mux (.compare .eq (.inp 0) (.inp 1)) (.boolBin .bxor (.inp 0) (.inp 0))
    (.boolNot (.boolBin .bor (.inp 0) (.inp 1))))
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
  for name in [``band, ``bor, ``bxor, ``bnot, ``shared, ``nested] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "Bool logic missed proved gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (translateFuelFix (fun rec e h t named =>
        Rec.translateExprToWireCached rec e h t named) translateFuelLimit) name [] false false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "Bool logic semantic/order checks failed"
      let some sv := emitAstModule m | throwError "Bool logic AST emission failed"
      let some pairs := combItems sv.items | throwError "Bool logic body extraction failed"
      let widths := astWidths sv
      let names := (declarationTable sv).map Prod.fst
      let inputs := if name == ``nested then
          (List.range 8).flatMap fun flags => [0, 1, 127, 128, 255].flatMap fun x =>
            [0, 1, 127, 128, 255].map fun y => [flags % 2, flags / 2 % 2, flags / 4, x, y]
        else if name == ``bnot then [[0], [1]]
        else [[0, 0], [0, 1], [1, 0], [1, 1]]
      for values in inputs do
        let a := values[0]! == 1
        let b := values[1]?.getD 0 == 1
        let expected := encodeBool <| if name == ``nested then
            let c := values[2]! == 1
            let x := BitVec.ofNat 8 values[3]!
            let y := BitVec.ofNat 8 values[4]!
            ((a && b) || xor (!c) (BitVec.ult (x + y) y)) == (if x == y then xor a a else !(a || b))
          else if name == ``band then a && b
          else if name == ``bor then a || b
          else if name == ``bxor then xor a b
          else if name == ``bnot then !a else false
        let legacyInit := fun w =>
          (((legacy.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
        unless (evalAssigns (Tools.ShippingEntrySoundness.weOf legacy) (fun _ _ => 0)
            legacy.body legacyInit).map (· "out") == some expected do
          throwError "Bool logic legacy/source mismatch: {name}, {values}"
        for seed in [0, 1, 255] do
          let initial := fun w =>
            match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
            | some (_, v) => v
            | none => mask ((widths w).getD 0) seed
          let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
            throwError "Bool logic SV evaluation failed"
          let mut current := initial
          for _ in [:pairs.length] do
            let some next := parallelRound widths pairs current | throwError "Bool logic delta failed"
            current := next
          let some extra := parallelRound widths pairs current | throwError "Bool logic stable round failed"
          unless observeUnsignedOutput sv current "out" == some expected &&
              names.all (fun x => current x == stable x && extra x == stable x) do
            throwError "Bool logic source/SV/delta mismatch: {name}, {values}"
          count := count + 1
  unless count == 1962 do throwError "Bool logic case count mismatch: {count}"
  logInfo m!"BOOL LOGIC EXECUTION: {count} source/legacy/SV/delta cases; nested mixed comparisons and aliases"

-- User-defined overloads must not be admitted by the canonical Bool recognizer.
run_cmd do
  for (method, kind) in [( ``HAnd.hAnd, SignalBoolBinKind.band), (``HOr.hOr, .bor), (``HXor.hXor, .bxor)] do
    let inst := mkApp (.const `UserDefinedBoolInstance []) (.const ``defaultDomain [])
    unless (signalBoolBinKind? method inst).isNone do throwError "custom Bool instance entered direct route"
    unless (signalBoolBinKind? method (mkApp (.const (signalBoolBinInst kind) [])
        (.const ``defaultDomain []))) == some kind do throwError "canonical Bool instance missed direct route"

run_cmd do
  if (← get).messages.hasErrors then throwError "Bool logic regression failed"
  for name in [``Tools.ShippingMixedRecursion.bool_fuel_contract,
      ``Tools.ShippingMixedOrderSoundness.bool_fuel_orders,
      ``execution_source_of_env, ``nested_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected Bool logic axiom: {name}: {ax}"
  logInfo "BOOL LOGIC ENDPOINT: shipping source, syntax and finite settling; standard axioms only"

end Sparkle.Tests.Compiler.ShippingBoolLogicTest
