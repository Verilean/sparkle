import Tools.ShippingSrm22Width
import Tools.ShippingSrm23Regs
import Tools.ShippingMachineShipsS
set_option autoImplicit false
-- BUILT (unit SRM25): dev runs i1 (exit 1, audit file only; this module Built), i6 (exit 0); the final-SHA rebuild in REPORT-SRM25.md is the only final evidence.
-- SCOPE (generic, every Module b): (1) `refineCheck` pairs every register of the candidate with a register of the source of the same name AND THE SAME RESET VALUE
-- (SRM23's `shippedRegsFromSource_of_hierGate` forgets the reset value; `refineCheck_regWidth` discards that conjunct); (2) on a `hierGate` module a shipped register
-- therefore has a source register of the same name and reset value; (3) REDUCTION: G5 `ShippedRegsAreSlots b regs slots` follows from `hierGate b` and the SOURCE fact
-- `SourceRegsAreSlots b regs slots` (a PREMISE here).  The source fact is NOT proved for the `regs` witness of ComposedG(W) of topshare{M,Q}: see scripts/srm25/G5_INVENTORY.txt §4-5.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm25Init
open Sparkle.IR.AST Sparkle.IR.HierCheck Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.IR.Machine (SlotField)
open Tools.ShippingRefineSoundness (regOf_some)
open Tools.ShippingSrm22Width (ShippedRegsAreSlots mem_seqRegs_openFlat)

/-- **PROVED**: `refineCheck` keeps the reset value of every register it keeps. -/
theorem refineCheck_regInit {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    ∀ ro ∈ seqRegs o, ∃ rm ∈ seqRegs m, rm.1 = ro.1 ∧ rm.2.2.2.2 = ro.2.2.2.2 := by
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hpairs⟩, _⟩ := h1
  intro ro hro
  have hf := List.all_eq_true.mp hpairs ro hro
  cases hrm : regOf (seqRegs m) ro.1 with
  | none => rw [hrm] at hf; cases hf
  | some rm =>
    rw [hrm] at hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
    obtain ⟨hmem, hname⟩ := regOf_some hrm
    exact ⟨rm, hmem, hname, hf.1.1.2⟩

/-- **PROVED**: on a `hierGate` module every register of the shipped module has a register of the same output name AND the same reset value in the source. -/
theorem shippedRegInit_of_hierGate {b : Module} (hgate : hierGate b = true)
    (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int) :
    Stmt.register r c rs inp init ∈ (checkedOptimize b).body →
      ∃ (c' : String) (rs' : String × Sparkle.IR.Type.ResetKind) (inp' : Expr),
        Stmt.register r c' rs' inp' init ∈ b.body := by
  intro hm
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
      obtain ⟨rm, hrm, hname, hinit⟩ := refineCheck_regInit hrc _ hr
      obtain ⟨rn, rc, rrs, rinp, rinit⟩ := rm
      have hb := mem_seqRegs_openFlat.mp hrm
      have hn : rn = r := hname
      have hi : rinit = init := hinit
      subst hn hi
      exact ⟨rc, rrs, rinp, hb⟩
    · exact ⟨c, rs, inp, hm⟩
  · rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate (by simpa using hbind)] at hm
    exact ⟨c, rs, inp, hm⟩

/-- **PREMISE of `shippedRegsAreSlots_of_source` (OPEN for the `regs` witness of topshare{M,Q}).**  Every register statement of the SOURCE module is the `k`-th machine register
with the slot's initial value as reset value (`MachineWired` states it only for machines without calls). -/
def SourceRegsAreSlots (b : Module) (regs : List String) (slots : List SlotField) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ b.body →
      ∃ (k : Nat) (f : SlotField), regs[k]? = some r ∧ slots[k]? = some f ∧ init = Int.ofNat f.init

/-- **PROVED (reduction)**: G5 from `hierGate b` and the source fact `SourceRegsAreSlots b regs slots` (a premise about `b.body`, not about the shipped module). -/
theorem shippedRegsAreSlots_of_source {b : Module} (hgate : hierGate b = true) (regs : List String) (slots : List SlotField)
    (hS : SourceRegsAreSlots b regs slots) : ShippedRegsAreSlots b regs slots := by
  intro r c rs inp init hm
  obtain ⟨c', rs', inp', hb⟩ := shippedRegInit_of_hierGate hgate r c rs inp init hm
  obtain ⟨k, f, hk, hf, he⟩ := hS _ _ _ _ _ hb
  exact ⟨k, f, hk, hf, by rw [he]; rfl⟩

end Tools.ShippingSrm25Init

#print axioms Tools.ShippingSrm25Init.refineCheck_regInit
#print axioms Tools.ShippingSrm25Init.shippedRegInit_of_hierGate
#print axioms Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source
