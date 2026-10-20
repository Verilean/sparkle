import Tools.ShippingBindingsSoundness

namespace Sparkle.Tests.Compiler.ShippingBindingsSoundnessTest

set_option Elab.async false
open Lean Elab Command Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingBindingsSoundness Tools.ShippingScalarSoundness

private def key : FVarId := ⟨`x⟩
private def outer : Persistent := ({} : Persistent).insert `x "outer"
private def inner : CompilerState := { varMap := [(key, "inner")] }
private def env : String → Nat := fun n => if n == "inner" then 7 else 9

-- A visible-only invariant accepts the shadowed state even though the outer
-- binding is wrong. Such an invariant cannot justify scope restoration.
theorem visible_only_is_insufficient :
    BindingsAgree (visible inner outer)
      (visibleValues inner (fun _ => 7) (fun _ => 3)) env ∧
    ¬ BindingsAgree (visible ({} : CompilerState) outer)
      (visibleValues {} (fun _ => 7) (fun _ => 3)) env := by
  constructor
  · intro k wire hw
    rcases k with ⟨name⟩
    by_cases hn : name = `x
    · subst name
      have he : "inner" = wire := Option.some.inj hw
      subst wire
      rfl
    · have hk : ((⟨name⟩ : FVarId) == key) = false := by
        change (name == `x) = false
        simp [hn]
      simp [visible, inner, List.lookup_cons, hk, outer,
        Ne.symm hn] at hw
  · intro h
    have hx := h key "outer" (by simp [visible, outer, key])
    have bad : (9 : Nat) = 3 := hx
    contradiction

-- Actual reader behavior: shadowing is scoped; emitted circuit state persists.
run_cmd liftTermElabM do
  let state : CompilerState := { varMap := [(key, "outer")] }
  let action : CompilerM (Option String × Option String × Option String) := do
    let before ← CompilerM.lookupVar key
    let during ← CompilerM.withVarMapping key "inner" do
      CompilerM.emitAssign "result" (.const 8 7)
      CompilerM.lookupVar key
    let after ← CompilerM.lookupVar key
    return (before, during, after)
  let (observed, result) ← (action state).run (CircuitM.init "scope")
  unless observed == (some "outer", some "inner", some "outer") do
    throwError "reader shadow/restore regression"
  unless result.module.finalize.body.length == 1 do
    throwError "restoring reader unexpectedly discarded emitted statement"

-- Actual persistent fallback, including nested successful and failing actions.
-- Same key in parent and child is intentional: identity alone must not leak
-- a child-module wire into the parent's state.
run_cmd liftTermElabM do
  let child : CompilerM Unit := do
    unless (← CompilerM.lookupVar key).isNone do
      CompilerM.liftMetaM <| throwError "child inherited parent's binding"
    CompilerM.bindSourceVariable key "child"
    unless (← CompilerM.lookupVar key) == some "child" do
      CompilerM.liftMetaM <| throwError "child fallback missing"
  let parent : CompilerM Unit := do
    CompilerM.bindSourceVariable key "parent"
    let localResult ← CompilerM.withVarMapping key "local" (CompilerM.lookupVar key)
    unless localResult == some "local" do
      CompilerM.liftMetaM <| throwError "persistent map overrode local binding"
    let (_, childState) ← CompilerM.liftMetaM <| (child {}).run (CircuitM.init "child")
    unless childState.sourceBindings.get? key.name == some "child" do
      CompilerM.liftMetaM <| throwError "child result table missing"
    let failedChild : CompilerM Unit := do
      child
      CompilerM.liftMetaM <| throwError "deliberate child failure"
    let failed ← CompilerM.liftMetaM do
      try
        let _ ← (failedChild {}).run (CircuitM.init "failedChild")
        pure false
      catch _ => pure true
    unless failed do CompilerM.liftMetaM <| throwError "expected child failure"
    let _ ← CompilerM.makeWire "fresh" (.bitVector 8)
    CompilerM.emitAssign "output" (.const 8 7)
    unless (← CompilerM.lookupVar key) == some "parent" do
      CompilerM.liftMetaM <| throwError "parent fallback lost after scope/child/build operations"
  let (_, result) ← (parent {}).run (CircuitM.init "parent")
  unless result.sourceBindings.get? key.name == some "parent" do
    throwError "parent table missing"
  let (fresh, _) ← (CompilerM.lookupVar key {}).run (CircuitM.init "next")
  unless fresh.isNone do throwError "binding leaked into a later synthesis"

run_cmd do
  if (← get).messages.hasErrors then throwError "binding regression failed"
  for name in [``Valid.visible_correct, ``Valid.visible_reserved, ``visible_local,
      ``withVarMapping_run, ``Valid.enter, ``Valid.insert_persistent,
      ``Valid.allocate_write, ``Valid.scope_allocate_restore, ``Valid.allocate_emit, ``Valid.restore,
      ``lookupVar_run, ``bindSourceVariable_run, ``Valid.lookupVar,
      ``Valid.bindSourceVariable, ``init_sourceBindings,
      ``Valid.allocate_write_state,
      ``CircuitM.freshName_sourceBindings, ``CircuitM.makeWire_sourceBindings,
      ``visible_only_is_insufficient] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected binding axiom: {name}: {a}"
  logInfo "SHIPPING BINDINGS OK: hidden reservations, persistent insert, scoped reader equation, restore, negative invariant check, standard axioms only"
  logInfo "BINDING STATE OK: actual lookup/update equations, local priority, persistent fallback, nested success/failure isolation, fresh synthesis, standard axioms only"

end Sparkle.Tests.Compiler.ShippingBindingsSoundnessTest
