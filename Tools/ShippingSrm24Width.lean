import Tools.ShippingSrm22Width
import Tools.ShippingSrm23Regs
import Tools.ShippingWidthTables
set_option autoImplicit false
-- BUILT (unit SRM24): dev runs h1 (exit 1, split syntax), h2 (exit 0); the final-SHA rebuild in REPORT-SRM24.md is the only final evidence.
-- SCOPE (generic, every Module b): the SRM22 gap Prop `ShippedRegWidthLe b` (G4) is PROVED from `hierGate b = true` and sanitize-stability of `b.wires`.
-- Route: (1) on both branches of `checkedOptimize b` the declared width of a shipped register's name agrees between `b` and the shipped module
-- (`refineCheck_regWidth` inside `hierRefineCheck`; `openFlat` leaves wires unchanged); (2) in the shipped module a positive declared width is a wire
-- (`declWidth = 0` otherwise), and `declWidth_eq_weS` turns the declared width of a wire of a sanitize-stable wire table into `weS`;
-- the shipped wires are a sublist of `b`'s (`checkedOptimize_ports_wires`).  No nodup and no register-output-is-a-wire fact is needed.
-- G1 / G3 / G5 are not touched.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm24Width
open Sparkle.IR.AST Sparkle.IR.HierCheck Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingDesignSV (weS)
open Tools.ShippingSrm22Width (ShippedRegWidthLe)

/-- **PROVED**: on a `hierGate` module the declared width of a shipped register's name is the same in the source and in the shipped module. -/
theorem regWidth_eq_of_hierGate {b : Module} (hgate : hierGate b = true)
    (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int) :
    Stmt.register r c rs inp init ∈ (checkedOptimize b).body → declWidth b r = declWidth (checkedOptimize b) r := by
  intro hm
  by_cases hbind : hierBinds b = true
  · have e := Tools.ShippingGuardsSound.checkedOptimize_binding hbind
    by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · rw [if_pos hacc] at e
      rw [e] at hm ⊢
      have h := hacc
      simp only [hierRefineCheck, Bool.and_eq_true] at h
      obtain ⟨_, hrc⟩ := h
      have hr : (r, c, rs, inp, init) ∈ seqRegs
          (openFlat (deinline b (Sparkle.IR.Optimize.optimizeModule b)) (openIns b) (openOuts b)) := by
        unfold seqRegs
        refine List.mem_filterMap.mpr ⟨Stmt.register r c rs inp init, ?_, rfl⟩
        exact List.mem_filter.mpr ⟨hm, rfl⟩
      obtain ⟨rm, -, hname, hw⟩ := Tools.ShippingMachineShipsS.refineCheck_regWidth hrc _ hr
      have hn : rm.1 = r := hname
      rw [hn] at hw
      exact hw
    · rw [if_neg hacc] at e
      rw [e]
  · rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate (by simpa using hbind)]

/-- **PROVED** (G4): on a `hierGate` module with sanitize-stable wire names, every register of the shipped module has `b`'s declared width at most its emitted width. -/
theorem shippedRegWidthLe_of_hierGate {b : Module} (hgate : hierGate b = true)
    (hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) : ShippedRegWidthLe b := by
  intro r c rs inp init hm
  rw [regWidth_eq_of_hierGate hgate r c rs inp init hm]
  obtain ⟨-, -, hsub⟩ := Tools.ShippingNoPortsTypedI.checkedOptimize_ports_wires hgate
  by_cases h0 : declWidth (checkedOptimize b) r = 0
  · omega
  · have hx : r ∈ (checkedOptimize b).wires.map (·.name) := by
      cases hf : (checkedOptimize b).wires.find? (fun p => p.name == r) with
      | none => exact absurd (by simp [declWidth, hf]) h0
      | some p =>
        have hp := List.mem_of_find?_eq_some hf
        have hpn : p.name = r := by simpa using List.find?_some hf
        exact List.mem_map.mpr ⟨p, hp, hpn⟩
    exact Nat.le_of_eq (Tools.ShippingWidthTables.declWidth_eq_weS (fun p hp => hwn p (hsub p hp)) hx)

end Tools.ShippingSrm24Width

#print axioms Tools.ShippingSrm24Width.regWidth_eq_of_hierGate
#print axioms Tools.ShippingSrm24Width.shippedRegWidthLe_of_hierGate
