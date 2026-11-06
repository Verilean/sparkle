import Tests.Gen5.FGCircuitCmp
set_option autoImplicit false
-- FG circuit pilot S2w: regression controls of the shared comparator FGCircuitCmp (docs/FG-CIRCUIT-PILOT.md §47). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.
namespace Tests.Gen5.FGCircuitCmpRegress
open Lean Meta Tests.Gen5.FGCircuitCmp

def _proof_a : Nat := 0
def _proof_b : Nat := 1
theorem thmA : 1 + 1 = 2 := rfl
theorem thmB : 1 + 1 = 2 := by decide
theorem thmC : 2 + 2 = 4 := rfl

/-- a non-standard `BEq Nat` (always `false`) -/
@[reducible] def badBEq : BEq Nat := ⟨fun _ _ => false⟩
/-- a non-standard `OfNat Nat` instance -/
@[reducible] def badOfNat (n : Nat) : OfNat Nat n := ⟨n + 1⟩

def n (e : Lean.Expr) : MetaM Lean.Expr := normCommon e

def ctl (what : String) (ok : Bool) : MetaM Unit := do
  unless ok do throwError "FGCIRCUITCMPREGRESS control failed: {what}"

run_cmd Lean.Elab.Command.liftTermElabM do
  -- 1. name-only data erasure: two `_proof_`-named Nat defs with different values stay DIFFERENT
  let a ← n (.const ``_proof_a [])
  let b ← n (.const ``_proof_b [])
  ctl "_proof_ data defs are different" (!stmtEq a b)
  let a ← n (mkApp (.const ``Nat.succ []) (.const ``_proof_a []))
  let b ← n (mkApp (.const ``Nat.succ []) (.const ``_proof_b []))
  ctl "_proof_ data defs under an application are different" (!stmtEq a b)
  -- 2. proofs of the SAME proposition may be equal
  let a ← n (.const ``thmA [])
  let b ← n (.const ``thmB [])
  ctl "two proofs of one proposition are equal" (stmtEq a b)
  -- 3. proofs of DIFFERENT propositions are different (the proposition is kept)
  let c ← n (.const ``thmC [])
  ctl "proofs of different propositions are different" (!stmtEq a c)
  -- 4. proofs under a binder (type has a bound variable)
  let t ← Lean.Elab.Term.elabTerm (← `(fun (x : Nat) => (Nat.le_refl x : x ≤ x))) none
  let t2 ← Lean.Elab.Term.elabTerm (← `(fun (x : Nat) => (Nat.le_succ_of_le (Nat.le_refl x) |> fun _ => Nat.le_refl x : x ≤ x))) none
  ctl "proofs under a binder, same proposition" (stmtEq (← n t) (← n t2))
  let t3 ← Lean.Elab.Term.elabTerm (← `(fun (x : Nat) => (Nat.zero_le x : 0 ≤ x))) none
  ctl "proofs under a binder, different proposition" (!stmtEq (← n t) (← n t3))
  -- 5. BEq: standard instance is evaluated, non-standard is NOT treated as the standard one
  let natT := Lean.Expr.const ``Nat []
  let lit (k : Nat) : Lean.Expr := .lit (.natVal k)
  let ite' (inst : Lean.Expr) (x y : Nat) : Lean.Expr :=
    let b := mkApp4 (.const ``BEq.beq [0]) natT inst (lit x) (lit y)
    let c := mkApp3 (.const ``Eq [1]) (.const ``Bool []) b (.const ``Bool.true [])
    mkAppN (.const ``ite [1]) #[natT, c, mkApp2 (.const ``instDecidableEqBool []) b (.const ``Bool.true []), lit 10, lit 20]
  let stdInst ← synthInstance (mkApp (.const ``BEq [0]) natT)
  let badInst := Lean.Expr.const ``badBEq []
  ctl "standard BEq: 3 == 3 selects then-branch" (stmtEq (← n (ite' stdInst 3 3)) (lit 10))
  ctl "standard BEq: 3 == 4 selects else-branch" (stmtEq (← n (ite' stdInst 3 4)) (lit 20))
  ctl "always-false BEq is NOT the standard one (3 == 3 not selected)" (!stmtEq (← n (ite' badInst 3 3)) (lit 10))
  ctl "always-false BEq: the if is left alone" (!stmtEq (← n (ite' badInst 3 3)) (lit 20))
  -- 6. OfNat
  let ofN (inst : Lean.Expr) : Lean.Expr := mkApp3 (.const ``OfNat.ofNat [0]) natT (lit 5) inst
  ctl "standard OfNat Nat is the raw literal" (stmtEq (← n (ofN (mkApp (.const ``instOfNatNat []) (lit 5)))) (lit 5))
  ctl "custom OfNat Nat instance is NOT the raw literal" (!stmtEq (← n (ofN (mkApp (.const ``badOfNat []) (lit 5)))) (lit 5))
  logInfo "FGCIRCUITCMPREGRESS controls: all passed (name-only erasure, proof pair same/different proposition, proofs under binders, standard/always-false BEq, standard/custom OfNat)"

end Tests.Gen5.FGCircuitCmpRegress
