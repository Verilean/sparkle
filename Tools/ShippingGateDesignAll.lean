import Tools.ShippingGateCombSide
import Tools.ShippingGateNamesFinal
import Tools.ShippingChecksDerived
import Tools.ShippingChecksGate
import Tools.ShippingDesignSVBack
import Tools.ShippingShipsDesignSV

/-! # Gate-route parents: EVERY closed run of the emitted texts (worker N, round 15)

WRITTEN, NOT BUILT. PURE: no run.

The seven `…_gate_designSVN3` (`Tests.Compiler.GateConeDesignTypedTest`) conclude
only the EXISTENCE of a closed run `envsO` of the shipped design's emitted texts
(`DesignSV (childMap ms) 0 (checkedOptimize b) (seedIn b ins) T …`) showing the
source on `out`. The counted machine-route form
(`Tools.ShippingShipsDesignSVAll.ships_design_svN_all`) also concludes that EVERY
closed run from the same seeding and states has length `T` and shows the
source, by `Tools.ShippingDesignSVBack.design_sv_all`, which asks

* `designCheck (childMap ms) n (checkedOptimize b) = true`,
* `outsCheck (childMap ms) n (checkedOptimize b) = true`,
* the seeding keeps `weS`-bounded states bounded (from the inputs fitting
  `weS (checkedOptimize b)`),
* `Bounded (weS (checkedOptimize b)) st0`,
* every instance state of the shipped module `InvN … n`.

Here, at depth `0`, for a gate parent:

* `outsCheck0_of_kidsComb`: `outsCheck … 0 o` from `kidsComb ms o.body`
  (every instance resolves to an assignment-only module writing each output:
  each output is ASSIGNED, so `outsLeaf`);
* `gate_shipped_checks`: `designCheck … 0 (checkedOptimize b)` and
  `outsCheck … 0 (checkedOptimize b)` from `hierGate b`, the six facts of `b`
  that `Tools.ShippingGateParentRun.gate_combFacts` derives from the run, and
  `designSideB3` (derived by `gate_typedFacts`). NO new premise: `outsCheck`
  comes from `kidsComb` of the shipped module (`shipped_factsG`);
* `gate_sv_all`: under the same facts and the run-level width premises
  `DesignSideR` (the antecedent the `…_gate_designSVN3` already carry; its
  third, fourth and fifth conjuncts are exactly the three width premises of
  `design_sv_all`, the fifth moved from `b`'s instance statements to the
  shipped module's by `checkedOptimize_inst_iff_gate`), any property of ONE
  closed run holds of EVERY closed run from the same seeding and states. -/
namespace Tools.ShippingGateDesignAll
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (hierGate)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingDesignSV (DesignSV designCheck weS)
open Tools.ShippingSeqOptSoundness (seedIn)

/-- **`outsCheck` at depth 0 from `kidsComb`**: every instance's child is
assignment-only and writes each output, so each output is assigned. -/
theorem outsCheck0_of_kidsComb {ms : List Sparkle.IR.AST.Module} {o : Sparkle.IR.AST.Module}
    (h : Tools.ShippingMachineDepthH.kidsComb ms o.body = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap ms) 0 o = true :=
  Tools.ShippingChecksDerived.outsCheck0_of_insts fun mn iname conns hm => by
    have hs := List.all_eq_true.mp h _ hm
    cases hc : Sparkle.IR.Machine.moduleByName ms mn with
    | none => simp [hc] at hs
    | some c =>
      simp only [hc, Bool.and_eq_true] at hs
      obtain ⟨⟨⟨⟨hA, -⟩, hW⟩, -⟩, -⟩ := hs
      refine ⟨c, _, congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hc, ?_⟩
      apply Tools.ShippingChecksDerived2.outsLeaf_of_assigned
      intro p hp
      exact Tools.ShippingChecksGate.assign_of_writes hA
        (List.contains_iff_mem.mp (List.all_eq_true.mp hW p hp))

/-- **The two checks `design_sv_all` asks, of the shipped module at depth 0**,
from the gate, the six run-derived facts of `b` (`gate_combFacts`) and
`designSideB3` (`gate_typedFacts`). -/
theorem gate_shipped_checks {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (hg : hierGate b = true)
    (hwfB : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true)
    (hndB : (Tools.ShippingHierState.instNames b.body).Nodup)
    (hself : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true)
    (hout : Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb ms b.body = true)
    (hkidsB : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) 0) b.body = true)
    (hDB : Tools.ShippingGateParentRun.designSideB3 ms b = true) :
    designCheck (childMap ms) 0 (checkedOptimize b) = true ∧
      Tools.ShippingDesignSVBack.outsCheck (childMap ms) 0 (checkedOptimize b) = true := by
  refine ⟨Tools.ShippingGateCombSide.designCheck0_of hg hwfB hndB hself hout hcomb
    (Tools.ShippingGateParentRun.designSideB_of3 hDB hkidsB), ?_⟩
  obtain ⟨-, -, -, hcombS⟩ :=
    Tools.ShippingGateCombSide.shipped_factsG hg hwfB hndB hself hout hcomb
  exact outsCheck0_of_kidsComb hcombS

/-- **Every closed run shows what one does**, for a gate parent at depth 0:
`design_sv_all` with its checks from `gate_shipped_checks` and its width
premises from `DesignSideR`. -/
theorem gate_sv_all {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (hg : hierGate b = true)
    (hwfB : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true)
    (hndB : (Tools.ShippingHierState.instNames b.body).Nodup)
    (hself : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true)
    (hout : Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb ms b.body = true)
    (hkidsB : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) 0) b.body = true)
    (hDB : Tools.ShippingGateParentRun.designSideB3 ms b = true)
    {ins : Nat → String → Nat} {st0 : String → Nat} {kids : String → Tools.ShippingHierState.KidState}
    (hR : Tools.ShippingGateCombSide.DesignSideR ms b ins st0 kids)
    {T : Nat} {mems : MEnv} {envsO : List Env}
    (hD : DesignSV (childMap ms) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO)
    (P : List Env → Prop) (hP : P envsO) :
    ∀ envs', DesignSV (childMap ms) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
      P envs' := by
  intro envs' h'
  obtain ⟨hdc, hoc⟩ := gate_shipped_checks hg hwfB hndB hself hout hcomb hkidsB hDB
  obtain ⟨-, -, hinsW, hstW, hkidsR⟩ := hR
  exact Tools.ShippingDesignSVBack.design_sv_all ms 0 (checkedOptimize b) (seedIn b ins) T
    ⟨st0, mems, kids⟩ envsO P hdc hoc (Tools.ShippingShipsDesignSV.seedIn_bound hinsW) hstW
    (fun mn iname conns gc gcwe hm hc => hkidsR mn iname conns gc gcwe
      ((Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp hm) hc)
    hD hP envs' h'

end Tools.ShippingGateDesignAll

#print axioms Tools.ShippingGateDesignAll.outsCheck0_of_kidsComb
#print axioms Tools.ShippingGateDesignAll.gate_shipped_checks
#print axioms Tools.ShippingGateDesignAll.gate_sv_all
