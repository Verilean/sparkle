import Tools.VedU1ScriptSeqGen

/-!
# Regression check: the caches of `ved_omega_c` are reused only on equal inputs

`ved_omega_c` keeps three caches (`Tools.VedU1ScriptSeq.vedOmegaOk`, `vedUbFail`, `vedOmegaFail`, see their docstring):
a failure is reused only when the facts it depended on are EQUAL (the ordered `(x, u)` bound facts
for the interval prover, the ordered types of the relevant hypotheses for `omega`), a proof only when
every free variable it uses is in the context with an equal type; `ved_omega_c_reset` empties them.
The examples pin each rule directly, in one declaration each (the caches live in `IO.Ref`s, so each
example starts with `ved_omega_c_reset`).
-/

namespace Tests.Ved.VedOmegaCacheCheck

-- the recursion bound the generated scripts run under (`ved.u1.proofRecDepth`, default 20000)
set_option maxRecDepth 20000
set_option linter.unusedVariables false

open Lean Elab Tactic

/-- `ved_omega_c` must fail with exactly this message -/
elab "ved_expect_fail " msg:str : tactic => do
  let ok ← try evalTactic (← `(tactic| ved_omega_c)); pure true
    catch e =>
      let m ← e.toMessageData.toString
      unless m == msg.getString do throwError "wrong message: {m}"
      pure false
  if ok then throwError "ved_omega_c unexpectedly succeeded"

/-- `ved_omega_c` must fail, and not from a cache -/
elab "ved_expect_fail_fresh" : tactic => do
  let ok ← try evalTactic (← `(tactic| ved_omega_c)); pure true
    catch e =>
      let m ← e.toMessageData.toString
      if m.endsWith "(cached)" then throwError "refused from the cache: {m}"
      pure false
  if ok then throwError "ved_omega_c unexpectedly succeeded"

/-- replace the cached proofs by `id` of themselves: a goal closed from the cache is then closed by an
`id` application (`ved_expect_cached`), one closed by a fresh run is not (`ved_expect_fresh`) -/
elab "ved_mark_cached" : tactic => do
  let m ← Tools.VedU1ScriptSeq.vedOmegaOk.get
  if m.isEmpty then throwError "no cached proof"
  let mut m' := m
  for (tgt, e) in m.toList do
    let pf' ← Meta.mkAppM ``id #[e.proof]
    m' := m'.insert tgt { e with proof := pf' }
  Tools.VedU1ScriptSeq.vedOmegaOk.set m'

def vedClosedBy (isId : Bool) : TacticM Unit := do
  let g ← getMainGoal
  evalTactic (← `(tactic| ved_omega_c))
  let v ← instantiateMVars (mkMVar g)
  unless v.isAppOf ``id == isId do
    throwError "the goal was closed {if isId then "by a fresh run" else "from the cache"}"

/-- `ved_omega_c` closes the goal from the cache -/
elab "ved_expect_cached" : tactic => vedClosedBy true
/-- `ved_omega_c` closes the goal by a fresh run -/
elab "ved_expect_fresh" : tactic => vedClosedBy false

/-! ## interval prover (`vedUbFail`) -/

-- swap to an equally-many stronger hypothesis: `x < 10` fails with `hx : x < 100`; after
-- `clear hx` and `hy : x < 5` the context has the same NUMBER of bound facts (2), but different ones,
-- and the goal is provable.  The identical context is refused from the cache; `ved_omega_c_reset`
-- makes the refusal a fresh one.
example (x : Nat) (hx : x < 100) (hz : 3 * x < 15) : x < 10 := by
  ved_omega_c_reset
  ved_expect_fail "ved_omega_c: bound exceeds"
  ved_expect_fail "ved_omega_c: bound exceeds (cached)"
  ved_omega_c_reset
  ved_expect_fail "ved_omega_c: bound exceeds"
  ved_expect_fail "ved_omega_c: bound exceeds (cached)"
  clear hx
  have hy : x < 5 := by omega
  ved_omega_c

-- the old rule (reuse when the number of facts is `≤` the stored one) would refuse the retry above
#guard (let old : Array (String × Nat) := #[("x", 99), ("3x", 14)]
        let new : Array (String × Nat) := #[("3x", 14), ("x", 4)]
        new.size ≤ old.size && new != old)

-- the same facts with a hypothesis added: the key differs, the retry is a fresh run (it fails again, uncached)
example (x : Nat) (hx : x < 100) (hw : x < 99) (hq : x * 2 < 8) : x < 10 := by
  ved_omega_c_reset
  ved_expect_fail "ved_omega_c: bound exceeds"
  have hv : x < 98 := by omega
  ved_expect_fail "ved_omega_c: bound exceeds"
  ved_expect_fail "ved_omega_c: bound exceeds (cached)"
  have hu : x < 4 := by omega
  -- a different array of facts again: a fresh run (the first fact with this atom still decides)
  ved_expect_fail "ved_omega_c: bound exceeds"
  omega

/-! ## `omega` failures (`vedOmegaFail`) -/

-- fails (y is unbounded); the identical context is refused from the cache; with a new linear fact
-- (`hy`, a changed list of relevant hypotheses) it is tried again and succeeds; reset makes the
-- refusal of the identical context fresh again
example (x y : Nat) (P : Prop) (hp : P → y ≤ 5) (hP : P) (h : x ≤ 5) : x + y ≤ 10 := by
  ved_omega_c_reset
  ved_expect_fail_fresh
  ved_expect_fail "ved_omega_c: no proof (cached)"
  ved_omega_c_reset
  ved_expect_fail_fresh
  ved_expect_fail "ved_omega_c: no proof (cached)"
  have hy : y ≤ 5 := hp hP
  ved_omega_c

-- a `Bool` equation is not a relevant hypothesis: the equation `hb` that `cases` adds does not
-- change the key, so the refusal is still the cached one
example (x y : Nat) (P : Prop) (hp : P → y ≤ 5) (hP : P) (b : Bool) (h : x ≤ 5) : x + y ≤ 10 := by
  ved_omega_c_reset
  ved_expect_fail_fresh
  cases hb : b
  all_goals ved_expect_fail "ved_omega_c: no proof (cached)"
  all_goals have hy : y ≤ 5 := hp hP
  all_goals ved_omega_c

/-! ## success proofs (`Tools.VedU1ScriptSeq.vedOmegaOk`) -/

-- the second identical goal is closed from the cache (the stored proof is marked with `id`; an
-- unrelated hypothesis added meanwhile does not matter)
theorem reuse (x y : Nat) (z : Nat) (hz : z = 0) (hx : x < 2 ^ 256) (hy : y < 2 ^ 4097) :
    x * 2 ^ 4097 + y < 2 ^ 4353 ∧ x * 2 ^ 4097 + y < 2 ^ 4353 := by
  ved_omega_c_reset
  refine ⟨?_, ?_⟩
  · ved_expect_fresh
    ved_mark_cached
  · ved_expect_cached

/-- info: 'Tests.Ved.VedOmegaCacheCheck.reuse' does not depend on any axioms -/
#guard_msgs in #print axioms reuse

-- the same through `omega` (no bound fact for the atoms: the interval prover does not apply)
theorem reuse_omega (x y : Nat) (h : x + y ≤ 5) : x + y < 7 ∧ x + y < 7 := by
  ved_omega_c_reset
  refine ⟨?_, ?_⟩
  · ved_expect_fresh
    ved_mark_cached
  · ved_expect_cached

/-- info: 'Tests.Ved.VedOmegaCacheCheck.reuse_omega' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reuse_omega

-- a proof is reused only when the free variables it uses are in the context with equal types: here
-- the hypothesis it used (`hx`) is gone (`hx' : x < 5` has another `FVarId`), so a fresh run is made
example (x : Nat) (hx : x < 5) (h7 : x < 7) : x < 10 ∧ x < 10 := by
  ved_omega_c_reset
  refine ⟨?_, ?_⟩
  · ved_expect_fresh
    ved_mark_cached
  · have hx' : x < 5 := hx
    clear hx
    ved_expect_fresh

-- and after `ved_omega_c_reset` nothing is reused although the context is identical
example (x : Nat) (hx : x < 5) : x < 10 ∧ x < 10 := by
  ved_omega_c_reset
  refine ⟨?_, ?_⟩
  · ved_expect_fresh
    ved_mark_cached
  · ved_omega_c_reset
    ved_expect_fresh

end Tests.Ved.VedOmegaCacheCheck
