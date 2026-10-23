import Tools.ShippingNoPortsTypedI
import Tools.ShippingSatInputs
import Tools.ShippingLeafInputWidths
import Tools.ShippingSrm13Supply
import Tools.ShippingHierOpen
import Tools.ShippingHierOptRunHNoRst
set_option autoImplicit false
-- BUILT (unit SRM22): dev run w1 (exit 0); the final-SHA rebuild in REPORT-SRM22.md is the only final evidence.
-- SCOPE (generic, every Module b; `o := checkedOptimize b`): which DIRECTIONS between the ComposedG-side binders (hinsFit / hstX / hstR, over `declWidth b`, `openIns b`, `seqRegs (openFlat b …)`)
-- and the SRM19-side binders (hin / hst₁ / hst₂ / hst₃, over `weS o`, `RegsAtInit o`, `RegsFit o`, `NonRegBounded o`) are PROVED here, each under its EXACT premises.
-- The gap Props (`InputsAreWires`, `ShippedRegsFromSource`, `SourceRegsKept`, `ShippedRegWidthLe`, `ShippedRegsAreSlots`) are PREMISES of the lemmas that name them; none is a binder of either side and none is proved here.
-- A replacement is not a discharge: a lemma that turns one side's binder into the other's plus structural premises REPLACES it.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm22Width
open Sparkle.IR.AST Sparkle.IR.HierCheck Sparkle.IR.OptCheck
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingDesignSV (weS)
open Tools.ShippingLeafInputWidths (tyW)
open Tools.ShippingSrm13Supply (RegsAtInit RegsFit NonRegBounded)
open Tools.ShippingHierOpen (bodyInstOuts)
open Sparkle.IR.Machine (SlotField)

/-- **GAP (PREMISE; OPEN for the concrete `topshare{M,Q}` modules).**  Every input of `b` is also a wire of `b`. -/
def InputsAreWires (b : Module) : Prop := ∀ p ∈ b.inputs, p ∈ b.wires

/-- **GAP (PREMISE; OPEN).**  Every register statement of the shipped module has a register statement of the same output name in `b`. -/
def ShippedRegsFromSource (b : Module) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ (checkedOptimize b).body →
      ∃ (c' : String) (rs' : String × Sparkle.IR.Type.ResetKind) (inp' : Expr) (init' : Int), Stmt.register r c' rs' inp' init' ∈ b.body

/-- **GAP (PREMISE; OPEN).**  Every register statement of `b` survives in the shipped module with the same output name and the same reset value. -/
def SourceRegsKept (b : Module) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ b.body →
      ∃ (c' : String) (rs' : String × Sparkle.IR.Type.ResetKind) (inp' : Expr), Stmt.register r c' rs' inp' init ∈ (checkedOptimize b).body

/-- **GAP (PREMISE; OPEN).**  A register of the shipped module has `b`'s declared width at most its emitted width. -/
def ShippedRegWidthLe (b : Module) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ (checkedOptimize b).body → declWidth b r ≤ weS (checkedOptimize b) r

/-- **GAP (PREMISE; OPEN).**  Every register of the shipped module is the `k`-th machine register, whose slot's initial value is the module's reset value. -/
def ShippedRegsAreSlots (b : Module) (regs : List String) (slots : List SlotField) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ (checkedOptimize b).body →
      ∃ (k : Nat) (f : SlotField), regs[k]? = some r ∧ slots[k]? = some f ∧ f.init = init.toNat

/-- **PROVED [A, ComposedG ⇒ SRM19]**: `hinsFit` gives `hin`. -/
theorem hin_of_hinsFit {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hoi : ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name)
    (hIW : ∀ p ∈ b.inputs, declWidth b p.name ≤ tyW p.ty) (ins : Nat → String → Nat) :
    (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x := by
  intro h t x hx
  obtain ⟨hi, ho, hsub⟩ := Tools.ShippingNoPortsTypedI.checkedOptimize_ports_wires hgate
  have hle := Tools.ShippingLeafInputWidths.declWidth_le_weS_input hi ho hsub hnd hs hoi hIW x hx
  exact Nat.lt_of_lt_of_le (h t x hx) (Nat.pow_le_pow_right (by omega) hle)

/-- **PROVED [A, SRM19 ⇒ ComposedG] under the gap `InputsAreWires b`**: `hin` gives `hinsFit`. -/
theorem hinsFit_of_hin {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hoi : ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name)
    (hW : InputsAreWires b) (huniq : ∀ p ∈ b.inputs, ∀ q ∈ b.inputs, q.name = p.name → q = p)
    (hty : ∀ p ∈ b.inputs, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n) (ins : Nat → String → Nat) :
    (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
      ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x := by
  intro h t x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have e1 := Tools.ShippingSatInputs.weS_input hgate hnd hs hoi hp (hW p hp) (huniq p hp) (hty p hp)
  have e2 := Tools.ShippingSatInputs.declWidth_of_wire hnd (hW p hp) (hty p hp)
  have h' := h t p.name hx
  rw [e1] at h'
  rw [e2]
  exact h'

/-- **PROVED [B, SRM19 ⇒ ComposedG] under the gap `ShippedRegsFromSource b`**: `hst₃` gives `hstX`. -/
theorem hstX_of_hst3 {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (how : ∀ q ∈ b.outputs, ∀ p ∈ b.wires, p.name ≠ q.name) (hreg : ShippedRegsFromSource b)
    (C : String → Option (Module × Sparkle.IR.Semantics.WEnv)) (st0 : String → Nat) :
    NonRegBounded (checkedOptimize b) st0 →
      ∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts C b.body → st0 x < 2 ^ declWidth b x := by
  intro h x hx _
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  unfold openIns at hp
  obtain ⟨hpw, hcond⟩ := List.mem_filter.mp hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
  obtain ⟨⟨-, hdr⟩, hin⟩ := hcond
  have hxo : p.name ∉ b.outputs.map (·.name) := by
    intro hm
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hm
    exact how q hq p hpw hqn.symm
  have hxi : p.name ∉ b.inputs.map (·.name) := by
    intro hm
    have : (b.inputs.map (·.name)).contains p.name = true := List.contains_iff_mem.mpr hm
    rw [this] at hin
    exact Bool.noConfusion hin
  have hnr : ¬ ∃ c rs inp init, Stmt.register p.name c rs inp init ∈ (checkedOptimize b).body := by
    rintro ⟨c, rs, inp, init, hm⟩
    obtain ⟨c', rs', inp', init', hm'⟩ := hreg _ _ _ _ _ hm
    have hmem : p.name ∈ drivesOf b.body := by
      unfold drivesOf
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, hm', rfl⟩)
    have : (drivesOf b.body).contains p.name = true := List.contains_iff_mem.mpr hmem
    rw [this] at hdr
    exact Bool.noConfusion hdr
  have h1 := h p.name hnr
  have h2 := Tools.ShippingNoPortsTypedI.weS_checkedOptimize_le hgate hnd hs p.name hxo hxi
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) h2)

theorem mem_seqRegs_openFlat {b : Module} {r : String × String × (String × Sparkle.IR.Type.ResetKind) × Expr × Int} :
    r ∈ seqRegs (openFlat b (openIns b) (openOuts b)) ↔ Stmt.register r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∈ b.body := by
  rw [Tools.ShippingHierOptRunHNoRst.seqRegs_openFlat]
  unfold seqRegs
  constructor
  · intro h
    obtain ⟨st, hst, he⟩ := List.mem_filterMap.mp h
    cases st with
    | register o c rk i iv =>
      simp only [Option.some.injEq] at he
      subst he
      exact hst
    | _ => simp at he
  · intro h
    exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- **PROVED [C/D, SRM19 ⇒ ComposedG] under the gap `SourceRegsKept b`**: `hst₁` and `hst₂` give `hstR`. -/
theorem hstR_of_hst1_hst2 {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hrio : ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
      Stmt.register r c rs inp init ∈ b.body → r ∉ b.outputs.map (·.name) ∧ r ∉ b.inputs.map (·.name))
    (hkeep : SourceRegsKept b) (st0 : String → Nat) :
    RegsAtInit (checkedOptimize b) st0 → RegsFit (checkedOptimize b) →
      ∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1 := by
  intro h1 h2 r hr
  have hm := mem_seqRegs_openFlat.mp hr
  obtain ⟨c', rs', inp', hm'⟩ := hkeep _ _ _ _ _ hm
  obtain ⟨hro, hri⟩ := hrio _ _ _ _ _ hm
  have e1 := h1 _ _ _ _ _ hm'
  have e2 := h2 _ _ _ _ _ hm'
  have e3 := Tools.ShippingNoPortsTypedI.weS_checkedOptimize_le hgate hnd hs r.1 hro hri
  rw [e1]
  exact Nat.lt_of_lt_of_le e2 (Nat.pow_le_pow_right (by omega) e3)

/-- **PROVED [D, ComposedG with `hst₁` ⇒ SRM19] under the gaps `ShippedRegsFromSource b`, `ShippedRegWidthLe b`**: `hst₁` and `hstR` give `hst₂`. -/
theorem regsFit_of_hstR_hst1 {b : Module} (st0 : String → Nat) (hreg : ShippedRegsFromSource b)
    (hW : ShippedRegWidthLe b) :
    RegsAtInit (checkedOptimize b) st0 →
      (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
      RegsFit (checkedOptimize b) := by
  intro h1 hR r c rs inp init hm
  obtain ⟨c', rs', inp', init', hm'⟩ := hreg _ _ _ _ _ hm
  have hr := hR (r, c', rs', inp', init') (mem_seqRegs_openFlat.mpr hm')
  have e1 := h1 _ _ _ _ _ hm
  have e2 := hW _ _ _ _ _ hm
  simp only at hr
  rw [← e1]
  exact Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) e2)

/-- **PROVED [C, machine fact `hinit` ⇒ SRM19] under the gap `ShippedRegsAreSlots b regs slots`**: `hst₁` is supplied by `hinit` (NOT by `hstR`). -/
theorem regsAtInit_of_hinit {b : Module} (regs : List String) (slots : List SlotField) (st0 : String → Nat)
    (hG : ShippedRegsAreSlots b regs slots)
    (hinit : ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → slots[k]? = some f → st0 r = f.init) :
    RegsAtInit (checkedOptimize b) st0 := by
  intro r c rs inp init hm
  obtain ⟨k, f, hk, hf, he⟩ := hG _ _ _ _ _ hm
  rw [hinit k r f hk hf, he]

end Tools.ShippingSrm22Width

#print axioms Tools.ShippingSrm22Width.hin_of_hinsFit
#print axioms Tools.ShippingSrm22Width.hinsFit_of_hin
#print axioms Tools.ShippingSrm22Width.hstX_of_hst3
#print axioms Tools.ShippingSrm22Width.hstR_of_hst1_hst2
#print axioms Tools.ShippingSrm22Width.regsFit_of_hstR_hst1
#print axioms Tools.ShippingSrm22Width.regsAtInit_of_hinit
