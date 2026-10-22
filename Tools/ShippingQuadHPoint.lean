import Tools.ShippingQuadCallFacts
-- BUILT (unit SR18): h1 exit 0 (Tools.ShippingQuadHPoint; 684 jobs); final-SHA rebuild in REPORT-SR18.md.
-- SCOPE (binding, ledger L8ax): the PER-CALL residue of `callFactF_of_fam` (SR17) as a definition `HPointAt … k`, and `callFactF_of_hPointAt`: `CallFactF` follows from the dispatch equation `hS`
-- (PROVED generically: `quadSrcF_eq` / `leafSrcC_eq`) and one `HPointAt … k` per call `k < dP.shape.insts.length`.  `HPointAt … k` is EXACTLY the pointwise hypothesis of `callFactF_of_fam`
-- for the call `k` (decoded Bool / bit-vector families = families `A`/`B`, and the output defeq at the call-output position); the generator `Tools/ShippingSeqParentGenD2MS.lean` (opt-in
-- `sparkle.sharedLeafCandidate`) EMITS one kernel-checked theorem `HPointAt … k` per call of every accepted parent and callee.  Nothing here is a class theorem over abstract data: the residue
-- is a statement about GENERATED definitions and is checked per declaration.  No sorry / axiom / native_decide.
namespace Tools.ShippingQuadHPoint
open Tools.ShippingQuadCalls Tools.ShippingQuadComposed Tools.ShippingQuadCallFacts
open Tools.ShippingMachineAuto Tools.ShippingMachineChild
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine Sparkle.Compiler.Elab Lean

/-- **The residue of ONE call `k`** (one conjunct of the `hPoint` hypothesis of `callFactF_of_fam`). -/
def HPointAt (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig} (D : ι → DomainConfig)
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (outsC : Name → List OutField)
    (bsOf : Name → List (Name × MixedGateBinder))
    (src : (i : ι) → Name → (Nat → Signal (D i) Bool) → ((j : Nat) → (n : Nat) → Signal (D i) (BitVec n)) → List (Nat → Nat))
    (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < dP.shape.insts.length),
      ∃ (A : Nat → Signal (D i) Bool) (B : (j : Nat) → (n : Nat) → Signal (D i) (BitVec n)),
        boolsOf (D := D i) (bsOf (dP.shape.insts[k]).1)
          (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1) = A ∧
        bitsOf (D := D i) (bsOf (dP.shape.insts[k]).1)
          (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1) = B ∧
        ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
          (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
          (src i (dP.shape.insts[k]).1 A B)[k']? = some f ∧
          ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
            (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ

/-- **`CallFactF` from the dispatch equation and one `HPointAt` per call.**  Exactly `callFactF_of_fam` with its pointwise hypothesis split per call. -/
theorem callFactF_of_hPointAt (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig} (D : ι → DomainConfig)
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {outsC : Name → List OutField}
    {S : ι → Name → (Nat → List Nat) → List (Nat → Nat)}
    (bsOf : Name → List (Name × MixedGateBinder))
    (src : (i : ι) → Name → (Nat → Signal (D i) Bool) → ((j : Nat) → (n : Nat) → Signal (D i) (BitVec n)) → List (Nat → Nat))
    (hS : ∀ (i : ι) (n : Name) (vals : Nat → List Nat),
      S i n vals = src i n (boolsOf (D := D i) (bsOf n) vals) (bitsOf (D := D i) (bsOf n) vals))
    (hP : ∀ k, k < dP.shape.insts.length → HPointAt dP nP D lsrc ext extB outsC bsOf src k) :
    CallFactF dP nP lsrc ext extB outsC S :=
  callFactF_of_fam dP nP D bsOf src hS (fun i bools bits k hk => hP k hk i bools bits hk)

end Tools.ShippingQuadHPoint

#print axioms Tools.ShippingQuadHPoint.callFactF_of_hPointAt
