import Tools.ShippingKaryCalls
import Tools.ShippingQuadHPoint
-- BUILT (unit SR21): k12 exit 0 (dev run); the final-SHA rebuild is in REPORT-SR21.md.
-- SCOPE (binding, ledger L8ba): the K-ary dispatch equation for the callee-source table, used to build the parent's `CallFactF` (`hFP` of `kary_composed_split`) from one `HPointAt` per call
-- (`Tools.ShippingQuadHPoint.callFactF_of_hPointAt`, untouched): `kSrcA` (the callees' sources on decoded families, by name) and `kSrcF_eq` (`kSrcF` is `kSrcA` on the decoded families).
-- The per-call residues `HPointAt … k` themselves are facts about GENERATED definitions and stay per declaration (an instance proves them; see `Tests/Compiler/KaryThreeTest.lean`).
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingKaryFacts
open Tools.ShippingKaryRun Tools.ShippingKaryComposed
open Tools.ShippingMachineAuto Tools.ShippingMachineChild
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine Sparkle.Compiler.Elab Lean

/-- the callees' sources on decoded families, by name -/
def kSrcA {ι : Type} (cs : List KCal) (_i : ι) (n : Name) (A : Nat → Signal defaultDomain Bool)
    (B : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)) : List (Nat → Nat) :=
  match kFind cs n with
  | some e => e.src defaultDomain A B
  | none => []

/-- **The dispatch equation `hS` for the K-ary tables, PROVED** (`kSrcF` is `kSrcA` on the decoded families of the callee's binder table `kBsF`). -/
theorem kSrcF_eq {ι : Type} (cs : List KCal) (i : ι) (n : Name) (vals : Nat → List Nat) :
    kSrcF cs i n vals = kSrcA cs i n (boolsOf (D := defaultDomain) (kBsF cs n) vals) (bitsOf (D := defaultDomain) (kBsF cs n) vals) := by
  unfold kSrcF kSrcA kBsF
  cases kFind cs n <;> rfl

end Tools.ShippingKaryFacts

#print axioms Tools.ShippingKaryFacts.kSrcF_eq
