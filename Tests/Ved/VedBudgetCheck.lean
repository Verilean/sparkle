import Tools.VedU1Entry

/-!
# Direct check of `ved_budget n t` (`Tools/VedU1Entry.lean`)

`ved_budget n t` runs `t` under a local heartbeat budget: min(what is left of the ambient budget, `n * 1000`);
with an unlimited ambient budget (`maxHeartbeats 0`) the local budget alone; a runtime exception (heartbeat
timeout) inside `t` makes `ved_budget` fail with `ved_budget: local heartbeat budget exhausted`.

Heartbeats are allocation counts, so the numbers below are fixed and observable (`#guard_msgs`), not wall-clock.
The heavy tactic is the test-only `burn_hb k`: it allocates until `k * 1000` heartbeats have passed, calling
`Core.checkSystem` on the way (so it dies of the heartbeat limit exactly where a real tactic would).

* 1. enough budget: closes the goal;
* 2. ambient unlimited: the local cap still stops a heavy `t`;
* 3. the remaining outer budget is respected (control: `ved_budget_old`, the 4e4c7d2e version, which reset
  `initHeartbeats` and took min(ambient max, local), accepts the same script);
* 4. abort after a partial state change: the later alternative of `first` / `try … <;>` runs from the original goal.
-/

namespace Tests.Ved.VedBudgetCheck

open Lean Elab Tactic

/-- Test-only: burn `k * 1000` heartbeats, honouring the heartbeat limit. -/
elab "burn_hb " k:num : tactic => do
  let start ← IO.getNumHeartbeats
  let target := k.getNat * 1000
  let r ← IO.mkRef ([] : List Nat)
  let mut i := 0
  while (← IO.getNumHeartbeats) - start < target do
    Core.checkSystem "burn_hb"
    r.set (List.replicate 20 i)
    i := i + 1

/-- The 4e4c7d2e version of `ved_budget` (the control of item 3): the local budget restarts the clock
(`initHeartbeats := hb`) and is min(ambient max, local), whatever the ambient budget has already spent. -/
elab "ved_budget_old " n:num t:tactic : tactic => do
  let hb ← IO.getNumHeartbeats
  let loc := n.getNat * 1000
  let r ← withTheReader Core.Context (fun c =>
      { c with maxHeartbeats := if c.maxHeartbeats == 0 then loc else min c.maxHeartbeats loc, initHeartbeats := hb }) do
    tryCatchRuntimeEx (do evalTactic t; pure true) fun e =>
      if e.isRuntime then pure false else throw e
  unless r do throwError "ved_budget_old: local heartbeat budget exhausted"

/-! ## 1. Enough budget -/

example : True := by ved_budget 1000 (burn_hb 20; trivial)

theorem enough : 1 + 1 = 2 := by ved_budget 1000 (burn_hb 20; rfl)
/-- info: 'Tests.Ved.VedBudgetCheck.enough' does not depend on any axioms -/
#guard_msgs in #print axioms enough

/-! ## 2. Ambient unlimited: the local cap applies -/

-- without `ved_budget` the same work succeeds under the unlimited ambient budget
set_option maxHeartbeats 0 in
example : True := by burn_hb 300; trivial

-- with a local budget of 100 thousand it stops (300 thousand needed)
/-- error: ved_budget: local heartbeat budget exhausted -/
#guard_msgs in
set_option maxHeartbeats 0 in
example : True := by ved_budget 100 (burn_hb 300; trivial)

-- and an exactly sufficient local budget does not
set_option maxHeartbeats 0 in
example : True := by ved_budget 400 (burn_hb 300; trivial)

/-! ## 3. The remaining outer budget is respected

Outer budget 100 thousand, 80 thousand burned before `ved_budget`; `t` needs 60 thousand (less than the local
`BIG = 1000` thousand, more than the ~20 thousand left).  The current `ved_budget` fails; `ved_budget_old`
(clock restarted, min(100, 1000) = 100 thousand for `t`) lets the same script through: the outer budget was
exceeded.  This is the control the 4e4c7d2e version would fail. -/

/-- error: ved_budget: local heartbeat budget exhausted -/
#guard_msgs in
set_option maxHeartbeats 100 in
example : True := by burn_hb 80; ved_budget 1000 (burn_hb 60; trivial)

-- control: the old version accepts it (the heartbeat limit is not honoured across `ved_budget`)
set_option maxHeartbeats 100 in
example : True := by burn_hb 80; ved_budget_old 1000 (burn_hb 60; trivial)

-- and `t` within what is left (10 thousand of ~20) passes with the current one
set_option maxHeartbeats 100 in
example : True := by burn_hb 80; ved_budget 1000 (burn_hb 5; trivial)

/-! ## 4. Abort after a partial state change -/

-- `t` splits the goal (`refine`), then runs out; `t2` closes the ORIGINAL goal only (after the `refine` the
-- goal is `True`, which `exact ⟨trivial, trivial⟩` does not fit)
example : True ∧ True := by
  first
    | ved_budget 10 (refine ⟨?_, ?_⟩; burn_hb 300; all_goals trivial)
    | exact ⟨trivial, trivial⟩

example : True ∧ True := by
  (try ved_budget 10 (refine ⟨?_, ?_⟩; burn_hb 300)) <;> exact ⟨trivial, trivial⟩

-- the abort itself is a plain failure, with the same message
/-- error: ved_budget: local heartbeat budget exhausted -/
#guard_msgs in
example : True ∧ True := by ved_budget 10 (refine ⟨?_, ?_⟩; burn_hb 300)

-- a failure of `t` that is not a runtime exception passes through unchanged
/--
error: boom
⊢ True
-/
#guard_msgs in
example : True := by ved_budget 10 (fail "boom")

end Tests.Ved.VedBudgetCheck
