import Tools.ShippingMachineAuto
set_option autoImplicit false
-- BUILT (issue sparkle-gen-c4-initw, G-INITW of scripts/c3/GAP_MAP.md): content as at c04f443b, built by the issue-linked focused
-- target Tests.Compiler.C4InitWAuditTest in initw-focused-c04f443b-r2a6b (runner 2a678c60, exit 0, 312/312; standard axioms only). The
-- earlier attempt initw-focused-c04f443b-r2a6 failed on a node toolchain problem (mkvs-macpro elan/glibc) before Lean ran: not Lean evidence.
-- This header change is rebuilt at its own SHA (see the issue record).
-- SCOPE: one generic lemma about MachineData.ok (Tools/ShippingMachineAuto.lean:217-225, its 6th conjunct `zipAllB … d.shape.layout.slots d.slotBs`).
-- No production file is edited; C4 and G3 stay OPEN.
namespace Tools.ShippingC4InitW
open Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Sparkle.IR.Machine Sparkle.Compiler.Elab

/-- Membership extraction for `Zip₂` (the left list's elements satisfy the left projection of `R`). -/
theorem zip₂_left {α β : Type} {R : α → β → Prop} {P : α → Prop} (h : ∀ a b, R a b → P a) :
    ∀ {as : List α} {bs : List β}, Zip₂ R as bs → ∀ a ∈ as, P a
  | _, _, .nil, _, ha => by cases ha
  | _, _, .cons hab hrest, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h _ _ hab
    · exact zip₂_left h hrest a ha'

/-- **G-INITW (unbuilt)**: the machine data check `d.ok` already contains, per slot, `f.init < 2 ^ f.width`. -/
theorem hinitW_of_ok (d : MachineData) (hok : d.ok = true) :
    ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width := by
  have ok' := hok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  have layB := ok'.2.2.2.2.2.1
  have layW : Zip₂
      (fun (f : SlotField) (b : Lean.Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  exact zip₂_left (fun _ _ h => h.2.2) layW

end Tools.ShippingC4InitW
