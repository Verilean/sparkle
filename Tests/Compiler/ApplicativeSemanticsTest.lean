import Sparkle.Compiler.Elab
import Sparkle.IR.Semantics
import Tools.ApplicativeLowering
import Tools.ShippingBuilderSoundness

/-! Run the SHIPPING compiler, including zero-width cleanup and register
deduplication. Exhaustive small-width tests exercise source/IR values rather
than only compilation or the printed operator. The general theorem audited
below covers the source-side application rule, not the whole compiler. -/

namespace Sparkle.Tests.Compiler.ApplicativeSemanticsTest

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Lean Elab Command

abbrev S := Signal defaultDomain (BitVec 4)

def reversed (a b : S) : S := Signal.ap (Signal.map (fun x y => y - x) a) b
def duplicate (a b : S) : S := Signal.ap (Signal.map (fun x (_ : BitVec 4) => x + x) a) b
def withConstant (a b : S) : S := Signal.ap (Signal.map (fun x y => x + y + 3) a) b
def nested (a b : S) : S := Signal.ap (Signal.map (fun x y => (x + y) ^^^ (y - x)) a) b
def complement (a b : S) : S := Signal.ap (Signal.map (fun x y => ~~~(y - x)) a) b
def concatReverse (a b : S) : Signal defaultDomain (BitVec 8) :=
  Signal.ap (Signal.map (fun x y => y ++ x) a) b
def orderedLess (a b : S) : Signal defaultDomain Bool :=
  Signal.ap (Signal.map (fun x y => BitVec.ult y x) a) b
def rightAssociated (a b c : S) : S :=
  Signal.ap (Signal.ap (Signal.map (fun x y z => x - (y - z)) a) b) c
def permutedFour (a b c d : S) : S :=
  Signal.ap (Signal.ap (Signal.ap (Signal.map (fun w x y z => z - y + x - w) a) b) c) d

private def check (name : Name) (arity : Nat) (expected : List Nat → Nat) : TermElabM Unit := do
  let (m, design) ← synthesizeCombinational name
  unless m.inputs.length == arity && m.outputs.length == 1 && design.modules.isEmpty do
    throwError "unexpected test interface: {name}"
  let ports := m.inputs ++ m.outputs ++ m.wires
  let we : WEnv := fun n => match ports.find? (·.name == n) with
    | some p => match p.ty with | .bit => 1 | .bitVector w => w | _ => 0
    | none => 0
  for code in [:16 ^ arity] do
    let values := (List.range arity).map (fun i => code / 16 ^ i % 16)
    let env : Env := fun n => ((m.inputs.map (·.name)).zip values).lookup n |>.getD 0
    let some result := evalAssigns we (fun _ _ => 0) m.body env
      | throwError "IR evaluation refused: {name}, {values}"
    unless result m.outputs.head!.name == expected values do
      throwError "source/IR mismatch: {name}, {values}, IR={result m.outputs.head!.name}, source={expected values}"

run_cmd liftTermElabM do
  for (name, f) in [(``reversed, reversed), (``duplicate, duplicate),
      (``withConstant, withConstant), (``nested, nested), (``complement, complement)] do
    check name 2 fun xs => ((f (Signal.pure (BitVec.ofNat 4 xs[0]!))
      (Signal.pure (BitVec.ofNat 4 xs[1]!))).val 0).toNat
  check ``concatReverse 2 fun xs => ((concatReverse
    (Signal.pure (BitVec.ofNat 4 xs[0]!)) (Signal.pure (BitVec.ofNat 4 xs[1]!))).val 0).toNat
  check ``orderedLess 2 fun xs => if (orderedLess
    (Signal.pure (BitVec.ofNat 4 xs[0]!)) (Signal.pure (BitVec.ofNat 4 xs[1]!))).val 0 then 1 else 0
  check ``rightAssociated 3 fun xs => ((rightAssociated
    (Signal.pure (BitVec.ofNat 4 xs[0]!)) (Signal.pure (BitVec.ofNat 4 xs[1]!))
    (Signal.pure (BitVec.ofNat 4 xs[2]!))).val 0).toNat
  check ``permutedFour 4 fun xs => ((permutedFour
    (Signal.pure (BitVec.ofNat 4 xs[0]!)) (Signal.pure (BitVec.ofNat 4 xs[1]!))
    (Signal.pure (BitVec.ofNat 4 xs[2]!)) (Signal.pure (BitVec.ofNat 4 xs[3]!))).val 0).toNat

run_cmd do
  if (← get).messages.hasErrors then throwError "applicative regression failed before axiom audit"
  for n in [``Tools.ApplicativeLowering.Arguments.correct, ``Tools.ApplicativeLowering.map_start,
      ``Tools.ShippingBuilderSoundness.emitAssign_body,
      ``Tools.ShippingBuilderSoundness.emitAssign_sound,
      ``Tools.ShippingBuilderSoundness.emitAssign_preserves_live] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected axiom: {n}: {a}"
  logInfo "APPLICATIVE SEMANTICS OK: 9 shipping compilations, exhaustive inputs, general source rule, standard axioms only"

end Sparkle.Tests.Compiler.ApplicativeSemanticsTest
