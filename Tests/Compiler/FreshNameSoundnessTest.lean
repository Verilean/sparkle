import Tools.ShippingAllocationSoundness

namespace Sparkle.Tests.Compiler.FreshNameSoundnessTest

set_option Elab.async false

open Sparkle.IR.Builder Sparkle.IR.FreshNames
open Tools.ShippingAllocationSoundness Tools.ShippingScalarSoundness
open Lean Elab Command

-- Symbolic builder state/hint/type: the generated wire is absent from the
-- complete old reservation set, not just from a hand-picked test list.
example (s : CircuitState) (hint : String) (named : Bool) :
    s.usedNames.contains (CircuitM.freshName hint named s).1 = false :=
  (CircuitM.freshName_spec hint named s).1

-- A live binding that bypasses reservation still violates the invariant.
example : ¬ Reserved (fun (_ : Unit) => some "missing") ({} : Std.HashSet String) := by
  intro h
  have hx := h () "missing" rfl
  simp at hx

run_cmd liftTermElabM do
  let initial := CircuitM.init "names"
  let reserved := ["_tmp_x_0", "_tmp_x_1", "_tmp_x_2", "_gen_x_1"].foldl
    (fun s name => (CircuitM.reserveName name s).2) initial
  let (temp, s1) := CircuitM.freshName "x" false reserved
  unless temp == "_tmp_x_3" && s1.counter == 4 do
    throwError "temporary allocation reused a reserved name: {temp}"
  let (n0, s2) := CircuitM.freshName "x" true s1
  let (n1, s3) := CircuitM.freshName "x" true s2
  unless n0 == "_gen_x" && n1 == "_gen_x_2" && s3.nextSuffix.getD "_gen_x" 0 == 3 do
    throwError "stable naming/suffix cache changed: {n0}, {n1}"
  let (a, sa) := CircuitM.makeWire "a.b" .bit true s3
  let (b, sb) := CircuitM.makeWire "a_b" .bit true sa
  let (hygiene, sh) := CircuitM.freshName "local__@scope" true sb
  let (empty, _) := CircuitM.freshName "" true sh
  unless a == "_gen_a_b" && b == "_gen_a_b_1" && hygiene == "_gen_local" && empty == "_gen_wire" do
    throwError "sanitization/hygiene naming changed"
  let digits := (CircuitM.reserveName "_gen_hot" initial).2
  let digits := (CircuitM.reserveName "_gen_hot_999" digits).2
  let digits := { digits with nextSuffix := digits.nextSuffix.insert "_gen_hot" 999 }
  let (next, _) := CircuitM.freshName "hot" true digits
  unless next == "_gen_hot_1000" do throwError "decimal-boundary collision: {next}"
  -- Public compiler wrapper, not only a standalone builder invocation.
  let (wire, after) ← (Sparkle.Compiler.Elab.CompilerM.makeWire "x" (.bitVector 8) false
    {}).run reserved
  unless wire == "_tmp_x_3" && after.module.wires.head!.name == wire do
    throwError "shipping wrapper bypassed fresh allocation"
  -- Same-base pressure: the suffix cache must advance rather than repeatedly
  -- starting at one. This is a regression check, not a timing claim.
  let mut s := initial
  for i in [:10000] do
    let (name, next) := CircuitM.freshName "hot" true s
    let expected := if i == 0 then "_gen_hot" else s!"_gen_hot_{i}"
    unless name == expected && !s.usedNames.contains name do
      throwError "same-base allocation regression at {i}: {name}"
    s := next
  unless s.nextSuffix.getD "_gen_hot" 0 == 10000 && s.usedNames.size == 10000 do
    throwError "reservation/suffix cache was not preserved"

run_cmd do
  if (← get).messages.hasErrors then throwError "fresh name regression failed"
  for name in [``numbered_injective, ``seek_sound, ``seek_none, ``seek_exists,
      ``freshSuffix_spec, ``CircuitM.freshName_spec, ``CircuitM.makeWire_spec,
      ``Reserved.not_live, ``Reserved.insert, ``Reserved.cons,
      ``makeWire_not_live, ``makeWire_reserved, ``allocate_emit_correct] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected allocation axiom: {name}: {a}"
  logInfo "FRESH NAME OK: total search, actual allocator, reserved collisions, compiler wrapper, 10000 stable names, allocation-to-emission proof, standard axioms only"

end Sparkle.Tests.Compiler.FreshNameSoundnessTest
