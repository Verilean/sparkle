import Tools.ShippingUnifiedInvariant
import Tests.Compiler.ShippingMixedExecutionTest

/-! Source/cache foundation tests. Compilation comparisons below are regression
witnesses for existing success paths, NOT new source-to-RTL theorems. -/
namespace Sparkle.Tests.Compiler.ShippingUnifiedSourceTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness

-- All of these already compile on the existing fallback path.
def arithmetic1 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 1)) := Signal.mux c a b + a
def arithmetic8 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) := Signal.mux c a b + a
def arithmetic65 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 65)) := Signal.mux c a b + a
def comparison {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.ult (Signal.mux c a b + a) (Signal.mux c b a)
def nested {dom : DomainConfig} (c d : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux (Signal.beq (Signal.mux c a b) (a + b))
    (Signal.mux (Signal.ult (Signal.mux d a b + a) b) (a * b) b)
    (Signal.mux c a b - Signal.mux d b a)

def arithmeticTerm : Term .bits := .binary .add
  (.mux (.boolInput 0) (.bitsInput 0) (.bitsInput 1)) (.bitsInput 0)
def comparisonTerm : Term .bool := .compare .ult arithmeticTerm
  (.mux (.boolInput 0) (.bitsInput 1) (.bitsInput 0))
def nestedTerm : Term .bits := .mux
  (.compare .eq (.mux (.boolInput 0) (.bitsInput 0) (.bitsInput 1))
    (.binary .add (.bitsInput 0) (.bitsInput 1)))
  (.mux (.compare .ult
    (.binary .add (.mux (.boolInput 1) (.bitsInput 0) (.bitsInput 1)) (.bitsInput 0))
    (.bitsInput 1)) (.binary .mul (.bitsInput 0) (.bitsInput 1)) (.bitsInput 1))
  (.binary .sub (.mux (.boolInput 0) (.bitsInput 0) (.bitsInput 1))
    (.mux (.boolInput 1) (.bitsInput 1) (.bitsInput 0)))

theorem nested_wf (n : Nat) : nestedTerm.WF 2 2 n := by simp [nestedTerm, Term.WF]

theorem arithmetic_library {D : DomainConfig} (bi : Nat → Signal D Bool) (vi : Nat → Signal D (BitVec 8)) :
    denote 8 bi vi arithmeticTerm = arithmetic8 (bi 0) (vi 0) (vi 1) := rfl
theorem comparison_library {D : DomainConfig} (bi : Nat → Signal D Bool) (vi : Nat → Signal D (BitVec 8)) :
    denote 8 bi vi comparisonTerm = comparison (bi 0) (vi 0) (vi 1) := rfl
theorem nested_library {D : DomainConfig} (bi : Nat → Signal D Bool) (vi : Nat → Signal D (BitVec 8)) :
    denote 8 bi vi nestedTerm = nested (bi 0) (bi 1) (vi 0) (vi 1) := rfl

#def_decl_value nestedValue of nested
def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`d, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem nested_peel : mixedGatePeel nestedValue = some (binders,
    quote (.bvar 4) 8 (fun j => inputExpr binders.length (j + 1))
      (fun j => inputExpr binders.length (j + 3)) nestedTerm) := rfl

/-- Quoted real source, at arbitrary Signal observations, has the unified
meaning required by the new cache invariant. No compiler run is claimed here. -/
theorem nested_meaning {inputs : FVarId → Option Value} {dom : Lean.Expr}
    {bi vi : Nat → FVarId} {D : DomainConfig}
    (bools : Nat → Signal D Bool) (bits : Nat → Signal D (BitVec 8)) (tick : Nat)
    (hb : ∀ j, j < 2 → inputs (bi j) = some (.bool ((bools j).val tick)))
    (hv : ∀ j, j < 2 → inputs (vi j) = some (.bits 8 ((bits j).val tick))) :
    Meaning inputs (quote dom 8 (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) nestedTerm)
      (.bits 8 ((nested (bools 0) (bools 1) (bits 0) (bits 1)).val tick)) := by
  have meaning := meaning_quote (dom := dom) hb hv nestedTerm (nested_wf 8)
  rw [← denote_val 8 bools bits tick, nested_library] at meaning
  exact meaning

open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.SVParser.AST Tools.SVParser.EmitSem Tools.SVParser.EmitAst
open Tools.ShippingDeclWidths Tools.ShippingModulePrintSoundness Tools.ShippingSVBridge
open ShippingMixedExecutionTest in
run_cmd liftTermElabM do
  let mut count := 0
  for name in [``arithmetic1, ``arithmetic8, ``arithmetic65, ``comparison, ``nested] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isNone do
      throwError "Unified-source test unexpectedly entered the previously proved gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (translateFuelFix (fun rec e h t named =>
        Rec.translateExprToWireCached rec e h t named) translateFuelLimit) name [] false false
    let (actual, _) ← synthesizeCombinational name
    let n := if name == ``arithmetic1 then 1 else if name == ``arithmetic65 then 65 else 8
    let samples := if n == 1 then [0, 1] else [0, 1, 2^(n-1)-1, 2^(n-1), 2^n-1]
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "Mutual mux semantic/order checks failed: {name}"
      let some sv := emitAstModule m | throwError "Mutual mux AST emission failed"
      let some pairs := combItems sv.items | throwError "Mutual mux body extraction failed"
      let widths := astWidths sv
      let names := (declarationTable sv).map Prod.fst
      for flags in List.range (if name == ``nested then 4 else 2) do
        for x in samples do
          for y in samples do
            let bs := fun j => if j == 0 then flags % 2 == 1 else flags / 2 == 1
            let vs := fun j => BitVec.ofNat n (if j == 0 then x else y)
            let values := if name == ``nested then [flags % 2, flags / 2, x, y] else [flags % 2, x, y]
            let expected := if name == ``comparison then encodeBool (eval n bs vs comparisonTerm)
              else (eval n bs vs (if name == ``nested then nestedTerm else arithmeticTerm)).toNat
            let legacyInit := fun w =>
              (((legacy.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
            unless (evalAssigns (Tools.ShippingEntrySoundness.weOf legacy) (fun _ _ => 0)
                legacy.body legacyInit).map (· "out") == some expected do
              throwError "Mutual mux legacy/source mismatch: {name}, {values}"
            for seed in [0, 1, 2^n-1] do
              let initial := fun w =>
                match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
                | some (_, v) => v
                | none => mask ((widths w).getD 0) seed
              let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
                throwError "Mutual mux SV evaluation failed"
              let mut current := initial
              for _ in [:pairs.length] do
                let some next := parallelRound widths pairs current | throwError "Mutual mux delta failed"
                current := next
              let some extra := parallelRound widths pairs current | throwError "Mutual mux stable round failed"
              unless observeUnsignedOutput sv current "out" == some expected &&
                  names.all (fun x => current x == stable x && extra x == stable x) do
                throwError "Mutual mux source/SV/delta mismatch: {name}, {values}"
              count := count + 1
  unless count == 2322 do throwError "Mutual mux case count mismatch: {count}"
  logInfo m!"UNIFIED SOURCE REGRESSION: {count} source/legacy/SV/delta cases; shipping endpoint extension still open"

-- The source view must not reinterpret a user instance as a library operation.
example : view (mkApp6 (.const ``HAdd.hAdd [.zero, .zero, .zero])
    (sigT (.bvar 0) 8) (sigT (.bvar 0) 8) (sigT (.bvar 0) 8)
    (.const `UserAdd []) (.bvar 1) (.bvar 2)) = none := rfl
example : view (mkApp5 (.const ``Signal.beq []) (.const ``Bool []) (.bvar 0)
    (.const `UserBEq []) (.bvar 1) (.bvar 2)) = none := rfl

run_cmd do
  if (← get).messages.hasErrors then throwError "Unified source/cache regression failed"
  for name in [``denote_val, ``meaning_quote, ``Meaning.deterministic, ``nested_meaning,
      ``Tools.ShippingUnifiedCache.validated_hit, ``Tools.ShippingUnifiedCache.record_preserves,
      ``Tools.ShippingUnifiedCache.cached_action, ``Tools.ShippingUnifiedInvariant.cached_outcome, ``Tools.ShippingUnifiedInvariant.Inv.emit_reserved] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected unified source/cache axiom: {name}: {ax}"
  logInfo "UNIFIED SOURCE/CACHE FOUNDATION: standard axioms only; recursive compiler/entry connection still open"

end Sparkle.Tests.Compiler.ShippingUnifiedSourceTest
