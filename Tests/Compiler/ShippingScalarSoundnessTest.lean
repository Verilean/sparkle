import Tools.ShippingScalarSoundness

namespace Sparkle.Tests.Compiler.ShippingScalarSoundnessTest

set_option Elab.async false

open Tools.ShippingScalarSoundness Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Compiler.Elab
open Lean Elab Command

-- These are canonical BitVec functions, the exact names covered by registry.
abbrev S := Signal defaultDomain (BitVec 8)
def add (a b : S) : S := Signal.ap (Signal.map BitVec.add a) b
def sub (a b : S) : S := Signal.ap (Signal.map BitVec.sub a) b
def mul (a b : S) : S := Signal.ap (Signal.map BitVec.mul a) b
def band (a b : S) : S := Signal.ap (Signal.map BitVec.and a) b
def bor (a b : S) : S := Signal.ap (Signal.map BitVec.or a) b
def bxor (a b : S) : S := Signal.ap (Signal.map BitVec.xor a) b

-- Symbolic width and values, including zero width and repeated operand wire.
example (op : Binary) (w : Nat) (x : BitVec w) :
    evalExpr (fun _ => w) (fun _ => x.toNat)
      (.op op.operator [.ref "x", .ref "x"]) = some (op.apply x x).toNat :=
  op.rhs_correct _ _ "x" "x" x x rfl rfl rfl rfl

-- Instantiate the general rule on the actual builder, still universally
-- quantified over operator, width and both values. No RHS proof is supplied.
theorem actual_builder_step (op : Binary) (w : Nat) (x y : BitVec w) :
    ∃ result,
      evalAssigns (fun _ => w) (fun _ _ => 0)
        (Sparkle.IR.Builder.CircuitM.emitAssign "out"
          (.op op.operator [.ref "a", .ref "b"])
          (Sparkle.IR.Builder.CircuitM.init "step")).2.module.finalize.body
        (fun n => if n == "a" then x.toNat else y.toNat) = some result ∧
      result "out" = (op.apply x y).toNat ∧ result "a" = x.toNat := by
  let env : Env := fun n => if n == "a" then x.toNat else y.toNat
  have hb : BindingsAgree (fun (_ : Unit) => some "a") (fun _ => x.toNat) env := by
    intro key wire h
    have hw : wire = "a" := by simpa using h.symm
    subst wire
    rfl
  have hf : ¬ Live (fun (_ : Unit) => some "a") "out" := by
    rintro ⟨_, h⟩
    exact (by decide : ("a" : String) ≠ "out") (Option.some.inj h)
  obtain ⟨_, result, hr, hv, hm⟩ := op.emit_correct
    (Sparkle.IR.Builder.CircuitM.init "step") (fun _ => w) (fun _ _ => 0)
    env env "a" "b" "out" x y (fun (_ : Unit) => some "a") (fun _ => x.toNat)
    rfl rfl rfl rfl rfl hb hf
  exact ⟨result, hr, hv, hm () "a" rfl⟩

-- The width hypothesis is necessary, not an incidental checker restriction.
example : evalExpr (fun _ => 4) (fun n => if n == "x" then 15 else 1)
    (.op .add [.ref "x", .ref "y"]) = some 0 := by decide
example : ((15#8) + (1#8)).toNat = 16 := by decide

-- A stale cache/local binding cannot survive overwriting its live wire.
example : ¬ BindingsAgree (fun (_ : Unit) => some "x") (fun _ => 3)
    (write (fun _ => 3) "x" 7) := by
  intro h
  have hx := h () "x" rfl
  simp [write] at hx

-- The list relation is first-wins, including the actual shadowing case.
example : BindingsAgree (fun k => [(0, "new"), (0, "old")].lookup k)
    (fun (_ : Nat) => 7) (fun n => if n == "new" then 7 else 3) := by
  intro k wire h
  by_cases hk : k = 0
  · subst k
    have hw : wire = "new" := by simpa using h.symm
    subst wire
    rfl
  · have hk' : (k == 0) = false := by simp [hk]
    simp [List.lookup_cons, hk', List.lookup_nil] at h

run_cmd liftTermElabM do
  for (name, op) in [(``add, Binary.add), (``sub, .sub), (``mul, .mul),
      (``band, .and), (``bor, .or), (``bxor, .xor)] do
    let (m, design) ← synthesizeCombinational name
    unless m.inputs.length == 2 && m.outputs.length == 1 && design.modules.isEmpty do
      throwError "unexpected primitive module interface: {name}"
    let ports := m.inputs ++ m.outputs ++ m.wires
    let we : WEnv := fun n => match ports.find? (·.name == n) with
      | some p => match p.ty with | .bitVector w => w | .bit => 1 | _ => 0
      | none => 0
    for x in [0, 1, 15, 16, 127, 128, 254, 255] do
      for y in [0, 1, 15, 16, 127, 128, 254, 255] do
        let env : Env := fun n =>
          if n == m.inputs[0]!.name then x else if n == m.inputs[1]!.name then y else 0
        let some result := evalAssigns we (fun _ _ => 0) m.body env
          | throwError "primitive IR refused: {name}"
        unless result m.outputs[0]!.name == (op.apply (BitVec.ofNat 8 x) (BitVec.ofNat 8 y)).toNat do
          throwError "primitive mismatch: {name}, {x}, {y}"

run_cmd do
  if (← get).messages.hasErrors then throwError "shipping scalar regression failed"
  for name in [``Binary.registry, ``Binary.rhs_correct, ``Binary.emit_correct,
      ``Binary.emit_local, ``BindingsAgree.write_fresh, ``BindingsAgree.cons,
      ``LocalBindingsAgree.extend, ``actual_builder_step] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected scalar axiom: {name}: {a}"
  logInfo "SHIPPING SCALAR OK: six canonical primitives, arbitrary-width rules, local binding invariant, freshness/width negatives, standard axioms only"

end Sparkle.Tests.Compiler.ShippingScalarSoundnessTest
