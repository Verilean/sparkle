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

run_cmd do
  if (← get).messages.hasErrors then throwError "binding regression failed"
  for name in [``Valid.visible_correct, ``Valid.visible_reserved, ``visible_local,
      ``withVarMapping_run, ``Valid.enter, ``Valid.insert_persistent,
      ``Valid.allocate_write, ``Valid.scope_allocate_restore, ``Valid.allocate_emit, ``Valid.restore,
      ``visible_only_is_insufficient] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected binding axiom: {name}: {a}"
  logInfo "SHIPPING BINDINGS OK: hidden reservations, persistent insert, scoped reader equation, restore, negative invariant check, standard axioms only"

end Sparkle.Tests.Compiler.ShippingBindingsSoundnessTest
