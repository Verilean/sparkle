import Tools.ShippingEntrySoundness

/-! The synthesis-entry theorems on REAL declarations: the quotation matches what
Lean elaborates, the user's definition is `denoteFE` by `rfl`, the certified
front end agrees with the legacy one, the IR computes the source values, and
the axiom audit. -/

namespace Sparkle.Tests.Compiler.ShippingEntrySoundnessTest

open Lean Elab Command Meta Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Compiler.Elab

def fragA {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  ((a + b) ^^^ (Signal.pure (BitVec.ofNat 8 3) : Signal dom (BitVec 8))) - a * b

def feA : FExpr :=
  .bin .sub (.bin .xor (.bin .add (.inp 0) (.inp 1)) (.lit 3)) (.bin .mul (.inp 0) (.inp 1))

def fragB {dom : DomainConfig} (a b c : Signal dom (BitVec 4)) : Signal dom (BitVec 4) :=
  (a + b) + (a + b) * c

def feB : FExpr :=
  .bin .add (.bin .add (.inp 0) (.inp 1)) (.bin .mul (.bin .add (.inp 0) (.inp 1)) (.inp 2))

def fragC {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  x &&& (x ||| (Signal.pure 0x00f5#16 : Signal dom (BitVec 16)))

def feC : FExpr := .bin .and (.inp 0) (.bin .or (.inp 0) (.lit 0x00f5))

def fragD {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a

def feD : FExpr := .inp 0

/-- Shifts are on the certified front end but not in `Denotes`: checked here
only for front-end agreement and against the Lean value. -/
def fragS {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (a <<< b) + (a >>> b)

/-- Outside the certified shape (a width-changing concatenation): the legacy
front end handles it. -/
def notCertified {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  a ++ a

def sigsOf {dom : DomainConfig} {n : Nat} (l : List (Signal dom (BitVec n))) (j : Nat) :
    Signal dom (BitVec n) :=
  l.getD j (Signal.pure 0)

/-! The user's definitions ARE `denoteFE` of their `FExpr`, by `rfl`. -/
example {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    fragA a b = denoteFE 8 (sigsOf [a, b]) feA := rfl
example {dom : DomainConfig} (a b c : Signal dom (BitVec 4)) :
    fragB a b c = denoteFE 4 (sigsOf [a, b, c]) feB := rfl
example {dom : DomainConfig} (x : Signal dom (BitVec 16)) :
    fragC x = denoteFE 16 (sigsOf [x]) feC := rfl
example {dom : DomainConfig} (a : Signal dom (BitVec 8)) :
    fragD a = denoteFE 8 (sigsOf [a]) feD := rfl

/-- Evaluate a synthesized combinational module on input values, under the
widths the module itself declares (`weOf`, as in the theorems). -/
def evalOut (m : Sparkle.IR.AST.Module) (inputs : List (String × Nat)) : Option Nat :=
  let initial : Sparkle.IR.Semantics.Env := fun s => (inputs.lookup s).getD 0
  (Sparkle.IR.Semantics.evalAssigns (weOf m) (fun _ _ => 0) m.body initial).map (· "out")

def cases : List (Name × Name × List Name × Nat × FExpr) :=
  [ (``fragA, `dom, [`a, `b], 8, feA), (``fragB, `dom, [`a, `b, `c], 4, feB),
    (``fragC, `dom, [`x], 16, feC), (``fragD, `dom, [`a], 8, feD) ]

run_cmd liftTermElabM do
  let tr : TranslateFn := fun e h t n => translateExprToWire e h t n
  for (decl, dn, names, n, fe) in cases do
    let ci ← getConstInfo decl
    -- (1) the value IS the quotation, by the Lean-level decidable equality
    let v := ci.value!
    unless @decide (v = quoteDecl dn names n fe) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "{decl}: value is not quoteDecl of its FExpr"
    -- (2) the gate accepts it
    unless (certifiedShape? false [] ci).isSome do
      throwError "{decl}: certified front end did not accept it"
    -- (3) certified front end = legacy front end, as IR and as Verilog
    let (m1, _) ← synthesizeCombinationalCoreWith tr decl [] false true
    let (m2, _) ← synthesizeCombinationalCoreWith tr decl [] false false
    unless toString (repr m1) == toString (repr m2) do
      throwError "{decl}: certified and legacy front ends disagree"
    unless Sparkle.Backend.Verilog.toVerilog m1 == Sparkle.Backend.Verilog.toVerilog m2 do
      throwError "{decl}: Verilog differs between front ends"
    -- (4) the IR computes evalFE (the Lean meaning) on sample inputs
    let ports := m1.inputs.map (·.name)
    unless ports.length == names.length do throwError "{decl}: inputs {ports}"
    for seed in [0, 1, 7, 100, 12345] do
      let vals : Nat → BitVec n := fun j => BitVec.ofNat n (seed * 31 + j * 97 + 5)
      let inputs := (List.range names.length).map fun j => (ports[j]!, (vals j).toNat)
      let got := evalOut m1 inputs
      let want := (evalFE n vals fe).toNat
      unless got == some want do
        throwError "{decl}: IR gives {got}, source gives {want} (seed {seed})"
  -- (5) shifts: certified front end, same IR as legacy, IR = Lean value
  let ciS ← getConstInfo ``fragS
  unless (certifiedShape? false [] ciS).isSome do throwError "fragS: not certified"
  let (s1, _) ← synthesizeCombinationalCoreWith tr ``fragS [] false true
  let (s2, _) ← synthesizeCombinationalCoreWith tr ``fragS [] false false
  unless toString (repr s1) == toString (repr s2) do throwError "fragS: front ends disagree"
  let sp := s1.inputs.map (·.name)
  for (x, y) in [(3, 1), (200, 3), (255, 7), (17, 9), (128, 0)] do
    let want := ((fragS (dom := defaultDomain) (Signal.pure (BitVec.ofNat 8 x))
      (Signal.pure (BitVec.ofNat 8 y))).val 0).toNat
    let got := evalOut s1 [(sp[0]!, x), (sp[1]!, y)]
    unless got == some want do throwError "fragS: IR gives {got}, source gives {want}"
  -- (6) outside the shape: not certified, still synthesized by the legacy front end
  let ci ← getConstInfo ``notCertified
  unless (certifiedShape? false [] ci).isNone do
    throwError "notCertified: gate accepted a concatenation"
  let _ ← synthesizeCombinationalCoreWith tr ``notCertified [] false true

run_cmd do
  if (← get).messages.hasErrors then throwError "entry regression failed"
  for name in [``MReturns.bind, ``MReturns.pure, ``MReturns.throw, ``MReturns.run,
      ``MReturns.try_finally, ``MReturns.ite, ``addInput_returns, ``addOutput_returns,
      ``withVarMapping_returns, ``bindInputPort_returns, ``bindCertifiedInputs_returns,
      ``emitLeaves_single, ``finishSynth_returns, ``addClockReset_facts,
      ``widthsAgree_weOf, ``rhoOf_some, ``translateExprToWire_grows,
      ``synthesizeCertified_sound, ``synthesizeCombinationalCore_sound,
      ``denoteFE_val, ``op_checks, ``instFVars_quoteBody, ``certifiedShape_quote,
      ``rhoOf_at, ``denotes_quote, ``fragmentDecl_sound, ``fragmentDecl_sound_signal,
      ``Tools.ShippingTranslateSoundness.translateExprToWire_sound] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected entry axiom: {name}: {a}"
  logInfo "SHIPPING ENTRY OK: fragmentDecl_sound — synthesizeCombinationalCore success ⇒ the IR computes the declaration's Lean meaning (Inv, WidthsAgree, Denotes discharged; post-processing excluded); standard axioms only"

end Sparkle.Tests.Compiler.ShippingEntrySoundnessTest
