import Tools.ShippingSrm22Width
import Tools.ShippingGuardsSound
import Tools.ShippingMachineShipsS
set_option autoImplicit false
-- BUILT (unit SRM23): dev run g1 (exit 0); final-SHA rebuild only in REPORT; see STATUS-SRM23.md / REPORT-SRM23.md for the runs.
-- SCOPE (generic, every Module b): the SRM22 gap Prop `ShippedRegsFromSource b` is PROVED from `hierGate b = true` alone.
-- Route: `checkedOptimize` on a `hierGate` module is `b` or the accepted guarded candidate `o'`; acceptance is `hierRefineCheck b o'`, whose
-- `refineCheck` on the extracted pair pairs every register of `o'` with a register of `b` of the same name (`refineCheck_regWidth`).
-- Nothing is assumed of the front-end run; the instances get `hierGate` from `core_hierGate_anyAM` (Tests/Compiler/Srm23RegsTest.lean).
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm23Regs
open Sparkle.IR.AST Sparkle.IR.HierCheck Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Tools.ShippingSrm22Width (ShippedRegsFromSource mem_seqRegs_openFlat)

/-- **PROVED**: on a `hierGate` module every register of the shipped module has a register of the same output name in the source. -/
theorem shippedRegsFromSource_of_hierGate {b : Module} (hgate : hierGate b = true) : ShippedRegsFromSource b := by
  intro r c rs inp init hm
  by_cases hbind : hierBinds b = true
  · rw [Tools.ShippingGuardsSound.checkedOptimize_binding hbind] at hm
    split at hm
    · rename_i hacc
      have h := hacc
      simp only [hierRefineCheck, Bool.and_eq_true] at h
      obtain ⟨_, hrc⟩ := h
      have hr : (r, c, rs, inp, init) ∈ seqRegs
          (openFlat (deinline b (Sparkle.IR.Optimize.optimizeModule b)) (openIns b) (openOuts b)) := by
        unfold seqRegs
        refine List.mem_filterMap.mpr ⟨Stmt.register r c rs inp init, ?_, rfl⟩
        exact List.mem_filter.mpr ⟨hm, rfl⟩
      obtain ⟨rm, hrm, hname, -⟩ := Tools.ShippingMachineShipsS.refineCheck_regWidth hrc _ hr
      have hb := mem_seqRegs_openFlat.mp hrm
      have hn : rm.1 = r := hname
      rw [hn] at hb
      exact ⟨_, _, _, _, hb⟩
    · exact ⟨c, rs, inp, init, hm⟩
  · rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate (by simpa using hbind)] at hm
    exact ⟨c, rs, inp, init, hm⟩

end Tools.ShippingSrm23Regs

#print axioms Tools.ShippingSrm23Regs.shippedRegsFromSource_of_hierGate
