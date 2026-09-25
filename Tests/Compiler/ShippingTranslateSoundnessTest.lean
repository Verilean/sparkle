import Tools.ShippingTranslateSoundness

/-! Axiom audit of the translator-soundness formalization, plus regression pins
for the operator-instance miscompile it exposed. -/

namespace Sparkle.Tests.Compiler.ShippingTranslateSoundnessTest

open Lean Elab Command Tools.ShippingTranslateSoundness
open Sparkle.Core.Domain Sparkle.Core.Signal

-- A user instance whose `+` is SUBTRACTION.  Before the fix the compiler
-- emitted an adder for it (source 3 + 10 = 249, RTL 13).  It must now either
-- be refused or lowered to its real body; silently emitting `.add` is a
-- miscompile.  The source value is pinned so the test documents the meaning.
-- `local`: a global instance here would override `+` on `Signal (BitVec 8)`
-- for every module that imports this test (it broke the "addition works"
-- simulation test in `lake test`: 5 + 3 became 5 - 3 = 2).
local instance weirdAddInst : HAdd (Signal defaultDomain (BitVec 8)) (Signal defaultDomain (BitVec 8))
    (Signal defaultDomain (BitVec 8)) where
  hAdd a b := (fun x y => x - y) <$> a <*> b

def weirdAdd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b

run_cmd do
  unless (weirdAdd (Signal.pure 3#8) (Signal.pure 10#8)).val 0 == 249#8 do
    throwError "source meaning of the user instance changed"

-- The canonical instance still lowers to `.add`: the shape the proof covers.
run_cmd liftTermElabM do
  let some (.defnInfo d) := (← getEnv).find? ``weirdAdd | throwError "no weirdAdd"
  Meta.lambdaTelescope d.value fun _ b => do
    unless Sparkle.Compiler.Elab.canonicalSignalBinKinds ``HAdd.hAdd b.getAppArgs == none do
      throwError "the user instance was classified as canonical"

run_cmd do
  if (← get).messages.hasErrors then throwError "translate regression failed"
  for name in [``Returns.bind, ``Returns.pure, ``Returns.liftMetaM, ``Returns.throw,
      ``Returns.get, ``Returns.set, ``makeWire_returns, ``emitAssign_returns,
      ``library_add, ``library_sub, ``library_mul, ``library_and, ``library_or,
      ``library_xor, ``signalBinOpOf_binary, ``WidthsAgree.mono, ``spec_of_never,
      ``fuelFix_spec, ``runs_of_body_eq, ``translateCanonicalSignalBinary_sound,
      ``library_pure, ``library_ofNat_literal, ``evalExpr_const_lt, ``bitVecLitValue?_lt,
      ``translateSignalPureLiteral_sound] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected translate axiom: {name}: {a}"
  logInfo "SHIPPING TRANSLATE OK: success predicate over the real CompilerM (bind/pure/lift/throw/get/set), lifted makeWire/emitAssign, library agreement for six operators, fuel-knot induction, Signal×Signal operator branch and Signal.pure literal branch preserved, standard axioms only"

end Sparkle.Tests.Compiler.ShippingTranslateSoundnessTest
