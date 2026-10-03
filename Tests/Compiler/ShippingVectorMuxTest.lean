import Tools.ShippingVectorMuxSoundness
import Tests.Compiler.ShippingMixedExecutionTest

namespace Sparkle.Tests.Compiler.ShippingVectorMuxTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingVectorMuxRecursion Tools.ShippingVectorMuxSoundness

def pick1 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 1)) := Signal.mux c a b
def pick8 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) := Signal.mux c a b
def pick65 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 65)) := Signal.mux c a b
def alias8 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux c (a + b) (a + b)
def nested {dom : DomainConfig} (c d : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux (c &&& Signal.ult a b) (Signal.mux d (a + b) (a - b)) (a * b)
-- Existing success paths outside VExpr must still compile and agree in regression tests.
def underArithmetic {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux c a b + a

#def_decl_value nestedValue of nested

def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`d, .bool), (`a, .bits 8), (`b, .bits 8)]
def term : VExpr := .mux (.boolBin .band (.inp 0) (.compare .ult (.inp 0) (.inp 1)))
  (.mux (.inp 1) (.arith (.bin .add (.inp 0) (.inp 1))) (.arith (.bin .sub (.inp 0) (.inp 1))))
  (.arith (.bin .mul (.inp 0) (.inp 1)))
theorem term_wf : term.WF 2 2 8 := by simp [term, VExpr.WF, BExpr.WF, FExpr.WF]
theorem nested_peel : mixedGatePeel nestedValue = some (binders,
    quoteV (.bvar 4) 8 (fun j => inputExpr binders.length (j + 1))
      (fun j => inputExpr binders.length (j + 3)) term) := rfl

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
      ExecutionValue m initial mems
        ((nested (bools 1) (bools 2) (bits 3 8) (bits 4 8)).val tick).toNat := by
  apply Tools.ShippingVectorMuxSoundness.execution_source_of_env hr env (by intro d hd; simp only [certifiedShape?, hd]; rfl)
    nested_peel ⟨_, _, _, rfl⟩ (by decide) term_wf
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`c, rfl⟩
    · exact ⟨`d, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

-- No Bool input is needed: a computed comparison condition also reaches the
-- final source theorem, even though the old telescope peeler succeeds.
def computed {dom : DomainConfig} (a b : Signal dom (BitVec 8)) := Signal.mux (Signal.ult a b) a b
#def_decl_value computedValue of computed

def computedBinders : List (Name × MixedGateBinder) := [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]
def computedTerm : VExpr := .mux (.compare .ult (.inp 0) (.inp 1)) (.arith (.inp 0)) (.arith (.inp 1))

theorem computed_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``computed) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``computed computedValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = computedBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``computed computedBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems ((computed (bits 1 8) (bits 2 8)).val tick).toNat := by
  have peel : mixedGatePeel computedValue = some (computedBinders,
      quoteV (.bvar 2) 8 (fun j => inputExpr computedBinders.length j)
        (fun j => inputExpr computedBinders.length (j + 1)) computedTerm) := rfl
  apply Tools.ShippingVectorMuxSoundness.execution_source_of_env (kb := 0) (kv := 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) peel ⟨_, _, _, rfl⟩ (by decide)
    (by simp [computedTerm, VExpr.WF, BExpr.WF, FExpr.WF])
  · intro j hj; omega
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
  let mut count := 0
  for name in [``pick1, ``pick8, ``pick65, ``alias8, ``nested, ``underArithmetic] do
    let ci ← getConstInfo name
    if name != ``underArithmetic then
      unless (mixedCertifiedShape? false [] ci).isSome do throwError "Vector mux missed proved gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (translateFuelFix (fun rec e h t named =>
        Rec.translateExprToWireCached rec e h t named) translateFuelLimit) name [] false false
    let (actual, _) ← synthesizeCombinational name
    let n := if name == ``pick1 then 1 else if name == ``pick65 then 65 else 8
    let samples := if n == 1 then [0, 1] else [0, 1, 2^(n-1)-1, 2^(n-1), 2^n-1]
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "Vector mux semantic/order checks failed: {name}"
      let some sv := emitAstModule m | throwError "Vector mux AST emission failed"
      let some pairs := combItems sv.items | throwError "Vector mux body extraction failed"
      let widths := astWidths sv
      unless widths "out" == some n do throwError "Vector mux output width lost: {name}"
      let names := (declarationTable sv).map Prod.fst
      for flags in List.range (if name == ``nested then 4 else 2) do
        for x in samples do
          for y in samples do
            let c := flags % 2 == 1
            let d := flags / 2 == 1
            let values := if name == ``nested then [flags % 2, flags / 2, x, y] else [flags % 2, x, y]
            let a := BitVec.ofNat n x
            let b := BitVec.ofNat n y
            let expected := (if name == ``nested then
                if c && BitVec.ult a b then (if d then a + b else a - b) else a * b
              else if name == ``alias8 then a + b
              else if name == ``underArithmetic then (if c then a else b) + a
              else if c then a else b).toNat
            let legacyInit := fun w =>
              (((legacy.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
            unless (evalAssigns (Tools.ShippingEntrySoundness.weOf legacy) (fun _ _ => 0)
                legacy.body legacyInit).map (· "out") == some expected do
              throwError "Vector mux legacy/source mismatch: {name}, {values}"
            for seed in [0, 1, 2^n-1] do
              let initial := fun w =>
                match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
                | some (_, v) => v
                | none => mask ((widths w).getD 0) seed
              let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
                throwError "Vector mux SV evaluation failed"
              let mut current := initial
              for _ in [:pairs.length] do
                let some next := parallelRound widths pairs current | throwError "Vector mux delta failed"
                current := next
              let some extra := parallelRound widths pairs current | throwError "Vector mux stable round failed"
              unless observeUnsignedOutput sv current "out" == some expected &&
                  names.all (fun x => current x == stable x && extra x == stable x) do
                throwError "Vector mux source/SV/delta mismatch: {name}, {values}"
              count := count + 1
  unless count == 2772 do throwError "Vector mux case count mismatch: {count}"
  logInfo m!"VECTOR MUX EXECUTION: {count} source/legacy/SV/delta cases; widths 1/8/65 and nested branches"

run_cmd do
  if (← get).messages.hasErrors then throwError "Vector mux regression failed"
  for name in [``Tools.ShippingVectorMuxSoundness.synthesizeMixedCertified_vector_sound,
      ``Tools.ShippingVectorMuxSoundness.execution_source_of_env, ``nested_execution, ``computed_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected vector mux axiom: {name}: {ax}"
  logInfo "VECTOR MUX ENDPOINT: shipping source, syntax and finite settling; standard axioms only"

end Sparkle.Tests.Compiler.ShippingVectorMuxTest
