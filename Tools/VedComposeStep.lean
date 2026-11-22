import Lean
import Tools.VedU2HierState
import Tools.VedU2HierProj
import Tools.VedU2HierNet

/-!
# VED compose: the parent's one-cycle step from LOCAL facts about an abstract environment

`outputsOnHS_of_stepRK` asks, for the open parent (instances replaced by oracle wires), a step fact `hstep`: the oracle fold
of the whole arrangement gives some environment `E`, and `E` satisfies the output equations and the register invariant at the
next cycle.  The generated proof of the H2c/H3 path discharged it by one `simp` that EVALUATES the whole arrangement
(`evalAssignsI` over every statement, a nested `upd` environment); its cost grows faster than linearly in the number of
statements (docs/VED-HIER-H3OPEN.md "Cost").

`step_local` takes the evaluation apart once, in the kernel, for any body: the fold exists (`evalAssignsI_succ_S`), and the
environment `E` it gives satisfies, with no evaluation of the fold,

* `hasg`: every assignment holds, `evalExpr E r = some (E l)`;
* `hEin`: a parent input carries the cycle's input; `hEreg`: a register output carries the pre-update state;
* `hEorc`: an instance output carries the oracle.

The remaining obligation is stated for an ABSTRACT `E` with these facts, so the generated proof proves each register's next
value and each output from the wires of ITS OWN cone (one small `simp` per wire, as the instance-argument nets already are),
not from an evaluation of all the statements.  The statement of `hstep` is unchanged; nothing is assumed.

The option `ved.compose.step` (default `false`) selects this path in `Tools/VedU2HierRegEntry.lean`; with it off the previous
script is generated unchanged.
-/

namespace Tools.VedCompose

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

register_option ved.compose.step : Bool := {
  defValue := false
  descr := "VED compose: prove the parent's one-cycle step from local facts about an abstract environment (cone by cone) instead of evaluating the whole arrangement"
}

theorem step_local (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (b0 : List Stmt) (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (hw0 : WOH d b0) (hai0 : ∀ s ∈ b0, isAsgInstReg s = true) (hsupp : ExprsSupp m b0)
    (hwi : ∀ n ∈ wrsH d b0, n ∉ inNames m) (hri : ∀ n ∈ regOuts b0, n ∉ inNames m)
    (hwr : ∀ n ∈ wrsH d b0, n ∉ regOuts b0)
    (ins : Nat → String → Nat) (t : Nat) (p : String → Nat)
    (hloc : ∀ E : Env,
      (∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l)) →
      (∀ x ∈ inNames m, E x = ins t x) →
      (∀ r ∈ regOuts b0, E r = p r) →
      (∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t) →
      ∃ nx, regNexts (declWidth m) (fun _ _ => 0) b0 E = some nx ∧
        (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
        R ins (t + 1) (applyNexts p nx)) :
    ∃ E nx, evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
        (seedIn m ins t (restrictTo (regOuts b0) p)) = some E ∧
      regNexts (declWidth m) (fun _ _ => 0) b0 E = some nx ∧
      (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
      R ins (t + 1) (applyNexts p nx) := by
  obtain ⟨E, hE⟩ := evalAssignsI_succ_S m (oracleIE d (fun y => Ow ins y t)) b0
    (seedIn m ins t (restrictTo (regOuts b0) p)) hai0 hsupp (by intro mn i cs _ e; exact ⟨_, rfl⟩)
  have hG := good_of_fold d (declWidth m) _ (oracleIE_laws d (fun y => Ow ins y t)) b0 _ E hw0 hE
  have hasg : ∀ l r, asgOf b0 l = some r → evalExpr (declWidth m) E r = some (E l) := by
    intro l r h
    have hl := asgOf_mem h
    obtain ⟨l', hl', hlE⟩ := hG.2 _ hl
    simp only [cellVals] at hl'
    cases hv : evalExpr (declWidth m) E r with
    | none => simp [hv] at hl'
    | some v =>
      simp only [hv, Option.map_some, Option.some.injEq] at hl'
      subst hl'
      have := hlE (l, v) (List.mem_singleton_self _)
      simp only at this
      rw [this]
  have hEin : ∀ x ∈ inNames m, E x = ins t x := by
    intro x hx
    rw [hG.1 x (fun h => hwi x h hx)]
    have h1 : (m.inputs.map (·.name)).contains x = true := List.contains_iff_mem.mpr hx
    unfold seedIn
    rw [if_pos h1]
  have hEreg : ∀ r ∈ regOuts b0, E r = p r := by
    intro r hr
    rw [hG.1 r (fun h => hwr r h hr)]
    have h1 : (m.inputs.map (·.name)).contains r = false := by
      cases h : (m.inputs.map (·.name)).contains r
      · rfl
      · exact absurd (List.contains_iff_mem.mp h) (hri r hr)
    have h2 : (regOuts b0).contains r = true := List.contains_iff_mem.mpr hr
    unfold seedIn restrictTo
    rw [if_neg (by rw [h1]; simp), if_pos h2]
  have hEorc : ∀ mn i cs, Stmt.inst mn i cs ∈ b0 → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t := by
    intro mn i cs hin y hy
    obtain ⟨l, hl, hlE⟩ := hG.2 _ hin
    simp only [cellVals, oracleIE, Option.some.injEq] at hl
    subst hl
    exact hlE (y, Ow ins y t) (List.mem_map.mpr ⟨y, hy, rfl⟩)
  obtain ⟨nx, h1, h2, h3⟩ := hloc E hasg hEin hEreg hEorc
  exact ⟨E, nx, hE, h1, h2, h3⟩

open Lean Meta Elab Tactic in
/-- Clear the evaluation environment `E` and every hypothesis that mentions it (the per-wire facts of the cones).  A goal that
has been rewritten to the atoms (registers, inputs, oracle values) is closed by `omega` from its own bounds; the cone facts
only slow the closers down (each has `if`s over the same atoms). -/
elab "ved_clear_env" : tactic => withMainContext do
  let mut g ← getMainGoal
  let lctx ← getLCtx
  let envs := lctx.decls.toList.filterMap fun d => match d with
    | some d => if d.userName == `E then some d.fvarId else none
    | none => none
  for d in lctx.decls.toList.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    if envs.any fun f => d.type.containsFVar f then
      g ← g.tryClear d.fvarId
  for f in envs do
    g ← g.tryClear f
  replaceMainGoal [g]

end Tools.VedCompose
