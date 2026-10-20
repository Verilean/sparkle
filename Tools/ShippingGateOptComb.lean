import Tools.ShippingGateDesignLift
import Tools.ShippingHierOptRunHNoRst
import Tools.ShippingHierPremises

/-! # Gate-route parents: the optimizer keeps `out`, without a reset port (worker Q)

WRITTEN, NOT BUILT.

Obstacle (C) of `Tools.ShippingGateDesignLift`, `OptKeepsOut ms b "out"`, for
a combinational parent (body of assignments and instances, no `rst` port).

What the compiler runs. On a module with an instance statement,
`checkedOptimize b` is NOT of simple shape and NOT all `seqStmtOk`, so it is

* `deinline b (optimizeModule b)` when `hierBinds b` and
  `hierRefineCheck b (deinline b (optimizeModule b))` (the check the
  compiler runs), and
* `b` itself otherwise, PROVIDED `hierGate b` (instances, assignments,
  registers only — true on a body of assignments and instances with an
  instance); without `hierGate` the unchecked `optimizeModule b` would be
  returned, which is why `hierGate b` is a premise.

`checkedOptimize_comb` reads this off the definition: either the fallback
(`checkedOptimize b = b`) or `hierRefineCheck b (checkedOptimize b) = true`.
So the check that the compiler ran and that accepted is DERIVED from the
returned module itself, not assumed.

The accepted branch then goes through
`Tools.ShippingHierOptRunHNoRst.hierRefineCheck_linkedH_noRst` (no `rst`,
since the body has no register: `seqRegs_nil_of_comb`). Its remaining
premises are design facts that the compiler does NOT run — the same ones
the machine route takes from `shipsHierHCheck` minus `hierBinds` (derived
here when needed) and minus `"rst" ∈ b.inputs`, plus `b`'s own linked
well-formedness (the machine route had it from its wiring) and `hierGate b`.
They are bundled as the decidable `combOptSide ms b` (OUTSIDE ALLOWED;
checker-style, like `DesignSide` and the machine route's non-closed forms):

* `hierGate b`;
* `linkedWF (childMap ms) b.body`, `linkedWF (childMap ms) (checkedOptimize b).body`;
* distinct instance names in `b` and `checkedOptimize b`;
* `noSelfRead (childMap ms) (checkedOptimize b).body`;
* `outsExtracted (childMap ms) b`;
* `kidsLocal ms (checkedOptimize b).body`;
* `hierTyped (childMap ms) b`.

The body shape (`b.body.all combStmtI`) is (B)'s first two parts
(`PostKeeps b M`), or a separate premise.

Results:
* `optKeepsOut_comb`: body shape + `combOptSide` + `outName` an output →
  `OptKeepsOut ms b outName`;
* `optKeepsOut_comb_post`: the same with the body shape from `PostKeeps b M`,
  for `outName = "out"`, the form `gate_designSV_of_steps` takes as `hC`. -/
namespace Tools.ShippingGateOptComb
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck (checkedOptimize simpleBody seqStmtOk)
open Sparkle.IR.RefineCheck (hierGate hierBinds hierRefineCheck)
open Tools.ShippingMachineLinked (childMap runModuleH)
open Tools.ShippingSeqOptSoundness (seedIn seqRegsL)
open Tools.ShippingGateDesignLift (OptKeepsOut optKeepsOut_of_eq PostKeeps)

/-! ## The optimizer's branch on an instance-bearing module -/

theorem hasInst_of_hierGate {m : Sparkle.IR.AST.Module} (h : hierGate m = true) :
    Tools.ShippingMachineShipsHier.hasInst m := by
  simp only [hierGate, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨st, hst, hi⟩, -⟩ := h
  cases st with
  | inst mn iname conns => exact ⟨mn, iname, conns, hst⟩
  | _ => simp at hi

/-- **What `checkedOptimize` returns on a `hierGate` module**: the module
itself, or a module the compiler's own `hierRefineCheck` accepted. -/
theorem checkedOptimize_comb {b : Sparkle.IR.AST.Module} (hg : hierGate b = true) :
    checkedOptimize b = b ∨ hierRefineCheck b (checkedOptimize b) = true := by
  have hI := hasInst_of_hierGate hg
  by_cases hbind : hierBinds b = true
  · have hopt : checkedOptimize b =
        (if hierRefineCheck b (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
          then Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
      unfold checkedOptimize
      simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
        Tools.ShippingMachineShipsHier.not_all_seqOk hI, hbind, Bool.false_eq_true,
        if_false, if_true]
    by_cases hacc : hierRefineCheck b
        (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · right
      rw [hopt, if_pos hacc]
      exact hacc
    · left
      rw [hopt, if_neg hacc]
  · left
    have hbind' : hierBinds b = false := by simpa using hbind
    unfold checkedOptimize
    simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
      Tools.ShippingMachineShipsHier.not_all_seqOk hI, hbind', hg, Bool.false_eq_true,
      if_false, if_true]

/-! ## No register in a body of assignments and instances -/

theorem seqRegsL_nil_of_comb :
    ∀ {body : List Stmt}, body.all Tools.ShippingHierSVSoundness.combStmtI = true →
      seqRegsL body = []
  | [], _ => rfl
  | st :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | assign l e =>
      simp only [seqRegsL, List.filterMap_cons]
      exact seqRegsL_nil_of_comb h.2
    | inst mn i c =>
      simp only [seqRegsL, List.filterMap_cons]
      exact seqRegsL_nil_of_comb h.2
    | _ => simp [Tools.ShippingHierSVSoundness.combStmtI] at h

theorem seqRegs_nil_of_comb {b : Sparkle.IR.AST.Module}
    (h : b.body.all Tools.ShippingHierSVSoundness.combStmtI = true) :
    Sparkle.IR.OptCheck.seqRegs b = [] :=
  seqRegsL_nil_of_comb h

/-! ## The side facts (decidable, OUTSIDE ALLOWED) -/

/-- The design facts `hierRefineCheck_linkedH_noRst` needs beyond the
compiler's own check (see the file comment). -/
def combOptSide (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module) : Bool :=
  hierGate b &&
    Tools.ShippingHierOpen.linkedWF (childMap ms) b.body &&
    Tools.ShippingHierOpen.linkedWF (childMap ms) (checkedOptimize b).body &&
    decide (Tools.ShippingHierState.instNames b.body).Nodup &&
    decide (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup &&
    Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) (checkedOptimize b).body &&
    Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b &&
    Tools.ShippingHierOptRunH.kidsLocal ms (checkedOptimize b).body &&
    Tools.ShippingHierTyped.hierTyped (childMap ms) b

/-- What `combOptSide` gives. -/
theorem combOptSide_sound {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h : combOptSide ms b = true) :
    hierGate b = true ∧
    Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true ∧
    Tools.ShippingHierOpen.linkedWF (childMap ms) (checkedOptimize b).body = true ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup ∧
    (∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → ∀ child cwe,
      (childMap ms) mn = some (child, cwe) →
      ∀ c ∈ Tools.ShippingHierState.inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ Tools.ShippingHierOpen.instOutWires child.outputs conns) ∧
    (∀ w ∈ Tools.ShippingHierOpen.bodyInstOuts (childMap ms) b.body,
      w ∈ (Sparkle.IR.HierCheck.openIns b).map (·.name)) ∧
    Tools.ShippingHierOptRunH.kidsLocal ms (checkedOptimize b).body = true ∧
    Tools.ShippingHierTyped.hierTyped (childMap ms) b = true := by
  simp only [combOptSide, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨hg, h1, h2, h3, h4, Tools.ShippingHierPremisesBase.noSelfRead_sound h5,
    Tools.ShippingHierPremisesBase.outsExtracted_sound h6, h7, h8⟩

/-! ## (C) for a combinational parent -/

/-- **The optimizer keeps an output of a combinational parent, without a
reset port.** On a body of assignments and instances whose side facts hold,
`checkedOptimize` keeps `outName` along every linked run from fitting inputs
and a start state bounded off the outputs: in the fallback trivially, in the
accepted branch by the compiler's own `hierRefineCheck` (derived,
`checkedOptimize_comb`) and `hierRefineCheck_linkedH_noRst`. -/
theorem optKeepsOut_comb {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    {outName : String}
    (hcomb : b.body.all Tools.ShippingHierSVSoundness.combStmtI = true)
    (hside : combOptSide ms b = true)
    (hout : outName ∈ b.outputs.map (·.name)) :
    OptKeepsOut ms b outName := by
  obtain ⟨hg, hwfB, hwfO, hndB, hndO, hnofb, hOutM, hloc, hty⟩ := combOptSide_sound hside
  rcases checkedOptimize_comb hg with heq | hacc
  · exact optKeepsOut_of_eq heq
  · intro ins T st0 mems envs hinsFit hbo hrun
    have hfitX := Tools.ShippingHierTyped.fitX_of_typed ms b ins hty hinsFit hrun hbo
    obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ :=
      Tools.ShippingHierOptRunHNoRst.hierRefineCheck_linkedH_noRst ms hacc hwfB hwfO hndB hndO
        hloc hnofb hOutM ins hinsFit hrun hfitX (seqRegs_nil_of_comb hcomb)
    refine ⟨envsO, hrunO, hlenO, fun j hj hj' => ?_⟩
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hout
    rw [← hpn]
    exact hcorr p hp j hj hj'

/-- **(C) for a gate-route parent**, in the form `gate_designSV_of_steps`
takes: the body shape from (B) `PostKeeps b M`, the side facts, and `"out"`
an output port of `b`. -/
theorem optKeepsOut_comb_post {ms : List Sparkle.IR.AST.Module}
    {b M : Sparkle.IR.AST.Module} (hB : PostKeeps b M)
    (hside : combOptSide ms b = true)
    (hout : "out" ∈ b.outputs.map (·.name)) :
    OptKeepsOut ms b "out" := by
  obtain ⟨hcomb, hbody, -⟩ := hB
  exact optKeepsOut_comb (by rw [hbody]; exact hcomb) hside hout

end Tools.ShippingGateOptComb
