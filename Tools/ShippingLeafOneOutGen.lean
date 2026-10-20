import Tools.ShippingLeafOneOut
import Tools.ShippingCallsGate

/-! # Two small facts for the generated instances of a SLOTLESS LEAF MACHINE child (G1, round par/a-11)

Used by `#machine_oneout_any` (`Tools/ShippingOneOutAnyGenCommand.lean`) and
by the hand instance of `hftByte` (`Tests/Compiler/OneOutHftByteTest.lean`):

* `gateCallsOk_parts`: the one decided condition `d.gateCallsOk n = true`
  (what the BUILT `f.machine_closes_at` already decides for a slotless
  machine child at its declaration binders) contains `d.callsOk n = true`,
  the slot count, "no domain binder after the first `n`" and
  `instFields = []` — its four conjuncts, read off the definition. So three
  fields of `SlotlessLeaf.any` (`calls`, `ss`, `dom`) need no second kernel
  evaluation of the child's data.
* `leaf_outWidth`: every output port of a real child of a slotless leaf has
  the width `W`, when every layout output has it (a per-declaration decided
  condition). The per-entry form of `hkidW` for a parent whose entries may
  have DIFFERENT callees (where `hkidW_one`'s one `kidOuts` function and
  `callWidthsStrict` would have to be stated over all entries at once).

Nothing here is about a run except through `SlotlessLeaf.outTys`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafOneOutGen
open Lean Meta
open Tools.ShippingMachineAuto Tools.ShippingChildInv

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The four conjuncts of `gateCallsOk`.** -/
theorem gateCallsOk_parts {d : MachineData} {n : Nat}
    (h : Tools.ShippingMachineAuto.MachineData.gateCallsOk d n = true) :
    Tools.ShippingMachineAuto.MachineData.callsOk d n = true ∧
      d.ss.length = d.shape.layout.slots.length ∧
      (∀ b ∈ d.shape.binders.drop n, b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain) ∧
      d.shape.instFields = [] := by
  simp only [Tools.ShippingMachineAuto.MachineData.gateCallsOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, of_decide_eq_true h2, of_decide_eq_true h3, List.isEmpty_iff.mp h4⟩

/-- **Every output port of a real child of a slotless leaf has the width
`W`**, when every output of the child's layout has it. -/
theorem leaf_outWidth {c : Name} {dk : MachineData}
    (K : Tools.ShippingLeafOneOut.SlotlessLeaf mctx mref cctx cref c dk) {W : Nat}
    (hW : ∀ o ∈ dk.shape.layout.outs, o.ty.bitWidth = W) {y : Res}
    (hy : RealChild mref cref c y) :
    ∀ p ∈ y.1.outputs, p.ty.bitWidth = W := by
  intro p hp
  rw [(K.outTys hy).outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  rw [← e]
  exact hW o ho

end Tools.ShippingLeafOneOutGen
