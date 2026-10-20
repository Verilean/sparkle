import Sparkle.IR.Semantics

/-! # The trace of a module with any number of registers

`runModule` iterates `stepModule`: each cycle evaluates the assignments on
the seeded environment and replaces the register state by the update list.
This file states the k-cycle trace for a module whose every cycle is known —
"from state `st` at seed index `t` the step returns the update list
`next t st` and drives `out` with `out t st`" — as the run of the state
machine `(next, out)`. Nothing here depends on how many registers there are
or on what the compiler emits; it is the IR-level counterpart of the source
recurrence in `ShippingMachineSource`. -/
namespace Tools.ShippingMachineTrace
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- The register state after `j` cycles of a `k`-cycle run that starts in
`st`. (`runModule` passes the seed index counting down from `k - 1`.) -/
def stateAt (next : Nat → (String → Nat) → List (String × Nat)) :
    Nat → Nat → (String → Nat) → (String → Nat)
  | _, 0, st => st
  | 0, _ + 1, st => st
  | k + 1, j + 1, st => stateAt next k j (applyNexts st (next k st))

/-- **k-cycle trace of an N-register module.** If every cycle from a state
satisfying the invariant `P` steps to the update list `next t st` with `out`
driven to `out t st`, and the invariant is preserved, then a `k`-cycle run
succeeds and cycle `j` observes `out` of the `j`-th state. -/
theorem trace_of_cyclesN {we : WEnv} {body : List Stmt} {mems : MEnv}
    {seed : Nat → (String → Nat) → Env}
    {next : Nat → (String → Nat) → List (String × Nat)}
    {out : Nat → (String → Nat) → Nat} {P : (String → Nat) → Prop}
    (step : ∀ t st, P st → ∃ envF,
      stepModule we body (seed t st) mems = some (envF, next t st, mems) ∧
      envF "out" = out t st)
    (Pstep : ∀ t st, P st → P (applyNexts st (next t st))) :
    ∀ (k : Nat) (st0 : String → Nat), P st0 →
      ∃ envs, runModule we body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length),
          (envs[j]'hj) "out" = out (k - 1 - j) (stateAt next k j st0)
  | 0, _, _ => ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0, P0 => by
    obtain ⟨envF, hstep, hout⟩ := step k st0 P0
    obtain ⟨rest, hrun, hlen, hobs⟩ :=
      trace_of_cyclesN step Pstep k (applyNexts st0 (next k st0)) (Pstep k st0 P0)
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => simpa [stateAt] using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hobs i hi]
        have hidx : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
        rw [hidx]
        rfl

/-- An update list built from distinct register names assigns each of them
its own value. -/
theorem applyNexts_map_mem {st : String → Nat} {rs : List String} {G : String → Nat}
    {r : String} (hr : r ∈ rs) :
    applyNexts st (rs.map fun x => (x, G x)) r = G r := by
  induction rs with
  | nil => cases hr
  | cons x xs ih =>
    by_cases hx : x = r
    · subst hx
      simp [applyNexts]
    · have hne : (x == r) = false := by simpa using hx
      have hmem : r ∈ xs := by
        rcases List.mem_cons.mp hr with h | h
        · exact absurd h.symm hx
        · exact h
      have := ih hmem
      simpa [applyNexts, hne] using this

/-- … and leaves every other name alone. -/
theorem applyNexts_map_not_mem {st : String → Nat} {rs : List String} {G : String → Nat}
    {r : String} (hr : r ∉ rs) :
    applyNexts st (rs.map fun x => (x, G x)) r = st r := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ r := fun h => hr (h ▸ List.mem_cons_self)
    have hne : (x == r) = false := by simpa using hx
    have := ih (fun h => hr (List.mem_cons_of_mem _ h))
    simpa [applyNexts, hne] using this

end Tools.ShippingMachineTrace
