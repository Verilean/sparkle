import Tools.VedStrictAudit

/-!
# Checks for `#ved_strict_audit` (Tools/VedStrictAudit.lean)

Every NEGATIVE example below is labelled `NEGATIVE`.  The axioms declared
here exist only to show that the audit rejects them; nothing outside this
file imports it.  Expected outcome per example (reviewer ruling 2026-11-08,
items 8/9):

| example | expected |
|---|---|
| `by decide` | OK |
| `by native_decide` | rejected, auxiliary axiom named |
| `Lean.ofReduceBool` used directly | rejected, `Lean.ofReduceBool` and `Lean.trustCompiler` named |
| user axiom `ax_fake : False` | rejected |
| user axiom named like a native_decide auxiliary | rejected |
| `sorry` | rejected (`sorryAx`) |
| nonexistent name | error |
| a `def` / an `axiom` | error (not a theorem) |
| only `propext` / `Classical.choice` / `Quot.sound` | OK |
| G1-style finite check by `native_decide` / by `decide +kernel` | rejected / OK |

Note (Lean v4.32.1): `native_decide` no longer goes through
`Lean.ofReduceBool`; its closure is the single auxiliary axiom
`<decl>._native.native_decide.ax_1_1`.  `Lean.ofReduceBool` is therefore
exercised by its own example.
-/

namespace Tests.Ved.StrictAuditCheck

/-! ## Accepted -/

theorem okDecide : (List.range 10).foldl (· + ·) 0 = 45 := by decide

/-- info: VED STRICT OK Tests.Ved.StrictAuditCheck.okDecide: [] -/
#guard_msgs in
#ved_strict_audit okDecide

theorem okStd (p : Prop) : p ∨ ¬p := Classical.em p

/-- info: VED STRICT OK Tests.Ved.StrictAuditCheck.okStd: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
#ved_strict_audit okStd

/-! ## NEGATIVE: native_decide (closure = its auxiliary axiom) -/

theorem negNative : (List.range 10).foldl (· + ·) 0 = 45 := by native_decide

/--
error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.negNative REJECTED: non-standard axioms [Tests.Ved.StrictAuditCheck.negNative._native.native_decide.ax_1_1] (closure [Tests.Ved.StrictAuditCheck.negNative._native.native_decide.ax_1_1])
-/
#guard_msgs in
#ved_strict_audit negNative

/-! ## NEGATIVE: Lean.ofReduceBool used directly -/

def negCheck : Bool := (List.range 10).foldl (· + ·) 0 == 45

set_option linter.deprecated false in
theorem negReduceBool : negCheck = true := Lean.ofReduceBool negCheck true rfl

/--
error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.negReduceBool REJECTED: non-standard axioms [Lean.ofReduceBool, Lean.trustCompiler] (closure [Lean.ofReduceBool, Lean.trustCompiler])
-/
#guard_msgs in
#ved_strict_audit negReduceBool

/-! ## NEGATIVE: user axioms, including auxiliary-looking names -/

/-- NEGATIVE test axiom: only here to be rejected. -/
axiom ax_fake : False

theorem negUser : 1 = 2 := ax_fake.elim

/--
error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.negUser REJECTED: non-standard axioms [Tests.Ved.StrictAuditCheck.ax_fake] (closure [Tests.Ved.StrictAuditCheck.ax_fake])
-/
#guard_msgs in
#ved_strict_audit negUser

/-- NEGATIVE test axiom with the exact shape of a native_decide auxiliary
(the shape the shared route's name pattern admits). -/
axiom negSpoof._native.native_decide.ax_1_1 : False

theorem negSpoof : 1 = 2 := negSpoof._native.native_decide.ax_1_1.elim

/--
error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.negSpoof REJECTED: non-standard axioms [Tests.Ved.StrictAuditCheck.negSpoof._native.native_decide.ax_1_1] (closure [Tests.Ved.StrictAuditCheck.negSpoof._native.native_decide.ax_1_1])
-/
#guard_msgs in
#ved_strict_audit negSpoof

/-! ## NEGATIVE: sorry -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem negSorry : 1 = 2 := by sorry

/--
error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.negSorry REJECTED (depends on sorry): non-standard axioms [sorryAx] (closure [sorryAx])
-/
#guard_msgs in
#ved_strict_audit negSorry

/-! ## Errors: missing declaration, not a theorem -/

/-- error: #ved_strict_audit: unknown declaration doesNotExist -/
#guard_msgs in
#ved_strict_audit doesNotExist

/-- error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.negCheck is a def, not a theorem -/
#guard_msgs in
#ved_strict_audit negCheck

/-- error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.ax_fake is an axiom, not a theorem -/
#guard_msgs in
#ved_strict_audit ax_fake

/-! ## Raw closure (measurement only, accepts nothing) -/

/-- info: VED AXIOMS RAW Tests.Ved.StrictAuditCheck.negUser: [Tests.Ved.StrictAuditCheck.ax_fake] -/
#guard_msgs in
#ved_axioms_raw negUser

namespace Gen
theorem genA : 2 + 2 = 4 := by decide
theorem genB : 2 + 2 = 4 := by native_decide
end Gen

/--
info: VED AUDIT Tests.Ved.StrictAuditCheck.Gen.genA strict=OK axioms=[]
---
info: VED AUDIT Tests.Ved.StrictAuditCheck.Gen.genB strict=REJECTED axioms=[Tests.Ved.StrictAuditCheck.Gen.genB._native.native_decide.ax_1_1]
-/
#guard_msgs in
#ved_audit_generated Tests.Ved.StrictAuditCheck.Gen

/-! ## Ruling 9: a G1-style finite check, native_decide vs kernel decide

A miniature of the per-cone G1 obligations of `Tools/DeepElab.lean`
(`mkG1`: the refs of the cone lie in the stop set, and the width table
agrees with the if-chain width environment `weM`), over a 64-leaf cone.
The same proposition is closed once by `native_decide` (rejected) and once
by `decide +kernel` (accepted, standard axioms only). -/

inductive E where
  | ref (s : String)
  | lit (n : Nat)
  | add (a b : E)
  | mux (c a b : E)

def E.refs : E → List String
  | .ref s => [s]
  | .lit _ => []
  | .add a b => a.refs ++ b.refs
  | .mux c a b => c.refs ++ a.refs ++ b.refs

def stopL : List String := ["in0", "in1", "in2", "in3", "r0", "r1", "r2", "r3"]

def wtL : List (String × Nat) :=
  [("in0", 8), ("in1", 8), ("in2", 1), ("in3", 16), ("r0", 8), ("r1", 8), ("r2", 1), ("r3", 16)]

def weM (n : String) : Nat :=
  if n == "in0" then 8 else if n == "in1" then 8 else if n == "in2" then 1 else
  if n == "in3" then 16 else if n == "r0" then 8 else if n == "r1" then 8 else
  if n == "r2" then 1 else if n == "r3" then 16 else 0

/-- a balanced cone with `2^d` leaves, leaves cycling through `stopL` -/
def mkCone : Nat → Nat → E
  | 0, k => .ref (stopL.getD (k % 8) "")
  | d + 1, k => if d % 2 == 0 then .add (mkCone d (2 * k)) (mkCone d (2 * k + 1))
                else .mux (.ref "r2") (mkCone d (2 * k)) (mkCone d (2 * k + 1))

def cone : E := mkCone 6 0

/-- the G1-style obligation -/
def G1Obl : Prop := (∀ n ∈ cone.refs, n ∈ stopL) ∧ (∀ p ∈ wtL, weM p.1 = p.2)

theorem g1Native : G1Obl := by unfold G1Obl; native_decide

theorem g1Kernel : G1Obl := by unfold G1Obl; decide +kernel

/--
error: #ved_strict_audit: Tests.Ved.StrictAuditCheck.g1Native REJECTED: non-standard axioms [Tests.Ved.StrictAuditCheck.g1Native._native.native_decide.ax_1_1] (closure [Tests.Ved.StrictAuditCheck.g1Native._native.native_decide.ax_1_1, propext])
-/
#guard_msgs in
#ved_strict_audit g1Native

/-- info: VED STRICT OK Tests.Ved.StrictAuditCheck.g1Kernel: [propext] -/
#guard_msgs in
#ved_strict_audit g1Kernel

end Tests.Ved.StrictAuditCheck
