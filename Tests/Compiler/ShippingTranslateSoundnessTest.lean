import Tools.ShippingTranslateSoundness

/-! Axiom audit of the translator-soundness formalization, plus regression pins
for the operator-instance miscompile it exposed. -/

namespace Sparkle.Tests.Compiler.ShippingTranslateSoundnessTest

open Lean Elab Command Tools.ShippingTranslateSoundness
open Sparkle.Core.Domain Sparkle.Core.Signal

/-! ### Operator-instance miscompile, through the ACTUAL synthesis entry

A user instance whose `+` is SUBTRACTION. Before the fix `synthesizeCombinational`
succeeded and emitted an adder: source 3 + 10 = 249, RTL 13. Now it must refuse.
The canonical `+` must still synthesize, and its emitted IR — evaluated by the IR
semantics on the same inputs — must equal the source value. -/

section UserInstance
-- `local`: a global instance here would override `+` on `Signal (BitVec 8)`
-- for every module that imports this test (it broke the "addition works"
-- simulation test in `lake test`: 5 + 3 became 5 - 3 = 2).
local instance weirdAddInst : HAdd (Signal defaultDomain (BitVec 8)) (Signal defaultDomain (BitVec 8))
    (Signal defaultDomain (BitVec 8)) where
  hAdd a b := (fun x y => x - y) <$> a <*> b

def weirdAdd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b
end UserInstance

def canonAdd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b

/-- Evaluate a synthesized combinational module on named input values. -/
def evalOutput (m : Sparkle.IR.AST.Module) (inputs : List (String × Nat)) (out : String) :
    Option Nat :=
  let ports := m.inputs ++ m.outputs ++ m.wires
  let we : Sparkle.IR.Semantics.WEnv := fun n =>
    (ports.find? (·.name == n)).map (·.ty.bitWidth) |>.getD 0
  let initial : Sparkle.IR.Semantics.Env := fun n => (inputs.lookup n).getD 0
  (Sparkle.IR.Semantics.evalAssigns we (fun _ _ => 0) m.body initial).map (· out)

run_cmd liftTermElabM do
  -- source meanings
  unless (weirdAdd (Signal.pure 3#8) (Signal.pure 10#8)).val 0 == 249#8 do
    throwError "source meaning of the user instance changed"
  unless (canonAdd (Signal.pure 3#8) (Signal.pure 10#8)).val 0 == 13#8 do
    throwError "source meaning of canonical + changed"
  -- the user instance is REFUSED by the real entry
  let refused ← try
      let _ ← Sparkle.Compiler.Elab.synthesizeCombinational ``weirdAdd
      pure false
    catch _ => pure true
  unless refused do
    throwError "MISCOMPILE: synthesizeCombinational accepted a user HAdd instance"
  -- the canonical instance synthesizes, and its IR computes the source value
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational ``canonAdd
  let names := m.inputs.map (·.name)
  unless names.length == 2 do throwError "unexpected inputs {names}"
  let got := evalOutput m [(names[0]!, 3), (names[1]!, 10)] "out"
  unless got == some 13 do
    throwError "canonical + : IR gives {got}, source gives 13"

run_cmd do
  if (← get).messages.hasErrors then throwError "translate regression failed"
  for name in [``Returns.bind, ``Returns.pure, ``Returns.liftMetaM, ``Returns.throw,
      ``Returns.get, ``Returns.set, ``Returns.read, ``Returns.modify, ``makeWire_returns,
      ``emitAssign_returns, ``lookupVar_returns, ``cacheLookupValidated_returns,
      ``recordTranslation_returns,
      ``library_add, ``library_sub, ``library_mul, ``library_and, ``library_or,
      ``library_xor, ``library_pure, ``library_ofNat_literal, ``signalBinOpOf_binary,
      ``Denotes.det, ``Inv.transfer, ``Inv.transfer_except, ``RecordOk.insert,
      ``translateFuelFix_spec, ``evalExpr_const_lt, ``bitVecLitValue?_lt,
      ``translateSignalPureLiteral_branch, ``translateCanonicalSignalBinary_branch,
      ``translateStep_core, ``translateStepWith_run, ``translateStepWith_spec,
      ``translateExprToWire_sound,
      ``Sparkle.Compiler.ExprDecEq.exprDecEq, ``Sparkle.Compiler.ExprDecEq.synEq_iff,
      ``Sparkle.Compiler.ExprDecEq.levEq_iff] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected translate axiom: {name}: {a}"
  logInfo "SHIPPING TRANSLATE OK: translateExprToWire_sound — the real entry preserves meaning for any combination of inputs, BitVec literals and canonical + - * &&& ||| ^^^, recursion discharged by fuel induction; validated cache hits via exprDecEq; standard axioms only"

end Sparkle.Tests.Compiler.ShippingTranslateSoundnessTest
