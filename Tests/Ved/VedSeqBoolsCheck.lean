import Tools.VedU1ScriptSeqGen

/-!
# Regression check: `ved_seq_bools` (and `vedSplitBool`) split only the `Bool`s that occur in a goal

`ved_seq_bools` splits the conjuncts of the goal first, then every `Bool` loop-state variable
(`ved_b… : Bool.toNat e ≤ 1`) that occurs in a goal, with `vedSplitBool` (the goals
`hbool : e = true ⊢ G[true]` and `hbool : e = false ⊢ G[false]`).  Direct controls: both branches are
produced in this order and each is closed with its own fact; a `Bool` that does not occur in the goal
is not split; the goal count of a conjunction of `k` goals with their own `Bool` is the sum, not `2^k`.
-/

namespace Tests.Ved.VedSeqBoolsCheck

set_option linter.unusedVariables false

open Lean Elab Tactic

/-- the number of goals is exactly `n` -/
elab "ved_goal_count " n:num : tactic => do
  let k := (← getGoals).length
  unless k == n.getNat do throwError "expected {n.getNat} goals, found {k}"

-- both branches, true first; each closes with its own fact, and has its own `hbool`
theorem both_branches (f : Bool → Nat) (b : Bool) (ved_b1 : b.toNat ≤ 1) (hf1 : f true = 1) (hf2 : f false = 2) :
    f b = if b then 1 else 2 := by
  ved_seq_bools
  ved_goal_count 2
  · have _ : b = true := hbool
    simp [hf1]
  · have _ : b = false := hbool
    simp [hf2]

-- an unrelated `Bool` (its `ved_b…` fact is there, the `Bool` does not occur in the goal) is not split
theorem unrelated_not_split (f : Bool → Nat) (b c : Bool) (ved_b1 : b.toNat ≤ 1) (ved_b2 : c.toNat ≤ 1)
    (hf1 : f true = 1) (hf2 : f false = 2) : f b = if b then 1 else 2 := by
  ved_seq_bools
  ved_goal_count 2
  all_goals simp [hf1, hf2]

-- a goal without any of the `Bool`s is left as it is (one goal, no `hbool`)
theorem no_bool (b : Bool) (ved_b1 : b.toNat ≤ 1) (n : Nat) : n = n := by
  ved_seq_bools
  ved_goal_count 1
  rfl

-- both occur: all four combinations
theorem both_occur (f : Bool → Bool → Nat) (b c : Bool) (ved_b1 : b.toNat ≤ 1) (ved_b2 : c.toNat ≤ 1)
    : f b c = f b c := by
  ved_seq_bools
  ved_goal_count 4
  all_goals rfl

-- the conjuncts are split first: three conjuncts, each with its own `Bool`, give 2 + 2 + 2 goals (not 2^3)
theorem conjuncts_first (p : Bool → Nat) (b c d : Bool) (ved_b1 : b.toNat ≤ 1) (ved_b2 : c.toNat ≤ 1) (ved_b3 : d.toNat ≤ 1)
    (hp1 : p true = 1) (hp2 : p false = 1) : p b = 1 ∧ p c = 1 ∧ p d = 1 := by
  ved_seq_bools
  ved_goal_count 6
  all_goals first | exact hp1 | exact hp2

/-- info: 'Tests.Ved.VedSeqBoolsCheck.both_branches' depends on axioms: [propext] -/
#guard_msgs in #print axioms both_branches

/-- info: 'Tests.Ved.VedSeqBoolsCheck.unrelated_not_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms unrelated_not_split

/-- info: 'Tests.Ved.VedSeqBoolsCheck.no_bool' does not depend on any axioms -/
#guard_msgs in #print axioms no_bool

/-- info: 'Tests.Ved.VedSeqBoolsCheck.both_occur' does not depend on any axioms -/
#guard_msgs in #print axioms both_occur

/-- info: 'Tests.Ved.VedSeqBoolsCheck.conjuncts_first' does not depend on any axioms -/
#guard_msgs in #print axioms conjuncts_first


end Tests.Ved.VedSeqBoolsCheck
