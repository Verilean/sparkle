import Tools.ShippingHierSVSoundness
import Tools.ShippingMachineLinked
import Tools.ShippingMachineShipsComb

/-! # A combinational body with instances whose every seeded linked evaluation succeeds has a linked run (round par/b-36)

WRITTEN, NOT BUILT. PURE; connected to no endpoint.

The first of the pieces missing for a design-level endpoint of a parent
WITHOUT a register whose calls are combinational (the gate route's
instance roots and cones over instance leaves — `parentUse`, `parentMix`, …;
`docs/parallel/B-slotless-parents.md`). What exists for such a parent is
ONE linked evaluation (`evalAssignsH`, e.g. `parentMix_entry_observes`);
the generic text theorem `Tools.ShippingHierSVRunH.linked_sv_of_runH` asks a
linked RUN (`runModuleH`). This is the step between them, the instance
analogue of `Tools.ShippingGateDesign.runModule_assigns_total`: a body of
assignments and instances schedules no register and no memory write
(`regNexts_comb`, `memNexts_okI`), so the run is the list of the cycles'
evaluations. -/
namespace Tools.ShippingHierRunTotal
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen
open Tools.ShippingMachineLinked Tools.ShippingHierSVSoundness

/-- One linked cycle of a combinational body with instances is its linked
evaluation: no register update, the memories unchanged. -/
theorem stepModuleH_comb {we : WEnv} {children : String → Option (Module × WEnv)}
    {body : List Stmt} (hall : body.all combStmtI = true)
    {env0 e : Env} {mems : MEnv}
    (he : evalAssignsH we children mems body env0 = some e) :
    stepModuleH we children body env0 mems = some (e, [], mems) := by
  simp [stepModuleH, he, regNexts_comb hall, memNexts_okI (seqStmtOkI_of_comb hall)]

/-- **A combinational body with instances whose seeded linked evaluations
succeed has a linked run.** If, for every cycle index `k < N` and every
state, the linked evaluation of `body` on `seed k st` succeeds with an
environment satisfying `R k`, then for every `T ≤ N` the linked run of `T`
cycles exists, has length `T`, and its element at list index `j` (cycle
`t`, `t + j + 1 = T`: the latest cycle first) satisfies `R t`. -/
theorem runModuleH_comb_total {we : WEnv} {children : String → Option (Module × WEnv)}
    {body : List Stmt} (hall : body.all combStmtI = true)
    {seed : Nat → (String → Nat) → Env} {R : Nat → Env → Prop} {N : Nat}
    (hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < N →
      ∃ e, evalAssignsH we children mems body (seed k st) = some e ∧ R k e) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv), T ≤ N →
      ∃ envs, runModuleH we children body seed T st mems = some envs ∧ envs.length = T ∧
        ∀ (j : Nat) (hj : j < envs.length) (t : Nat), t + j + 1 = T → R t (envs[j]'hj) := by
  intro T
  induction T with
  | zero =>
    intro st mems _
    exact ⟨[], by simp [runModuleH], rfl, fun j hj => absurd hj (by simp)⟩
  | succ k ih =>
    intro st mems hT
    obtain ⟨e, he, hR⟩ := hstep k st mems (by omega)
    obtain ⟨rest, hr, hl, hc⟩ := ih st mems (by omega)
    have hS := stepModuleH_comb hall he
    refine ⟨e :: rest, ?_, by simp [hl], ?_⟩
    · simp only [runModuleH]
      simp [hS, Tools.ShippingMachineShipsComb.applyNexts_nil, hr]
    · intro j hj t ht
      cases j with
      | zero =>
        have e1 : t = k := by omega
        subst e1
        exact hR
      | succ j => exact hc j (by simpa using hj) t (by omega)

end Tools.ShippingHierRunTotal
