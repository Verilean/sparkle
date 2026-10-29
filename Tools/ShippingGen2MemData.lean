import Tools.ShippingGen2MemParent
import Tools.ShippingC4InitW
set_option autoImplicit false

/-! # M2-a: the data premises of the consumers, from `MemParentDataOk` (MEMPARENT_FREEZE.md rev1 §2.1)

Every row of §2.1's table marked "derived": `hkD`, `hIlen` (from `ok` + `callsOk`), `hSL`, `hSlen`, `hLlen`, `hNIn`
(the generic bodies of `c_ok_slotLet` / `c_parent_*`, Tests/Compiler/C4ComposedTest.lean:130-177), `houtOk`
(`outNameOk`, from `ok`'s outputs conjunct) and `hinitW` (`hinitW_of_ok`). No row is added. -/
namespace Tools.ShippingGen2
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineEntry (machNIn)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

theorem MemParentDataOk.rows {p : SrcPkg ι dom} (h : MemParentDataOk p) :
    p.d.ok = true ∧ p.d.callsOk p.kD = true ∧ p.d.ss.length = p.d.shape.layout.slots.length ∧
    (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) ∧
    (∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain) := by
  unfold MemParentDataOk MemParentDataOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem ok_slotLet (d : MachineData) (h : d.ok = true) :
    (∀ b ∈ d.slotBs, b.2 ≠ .domain) ∧ (∀ b ∈ d.letBs, b.2 ≠ .domain) := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨-, -, -, slotKinds, letKinds, -⟩ := h
  exact ⟨slotKinds, letKinds⟩

theorem ok_outNameOk (d : MachineData) (h : d.ok = true) :
    ∀ o ∈ d.shape.layout.outs, Sparkle.IR.Machine.outNameOk o.name = true := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, -, -, -, -, -, hout, -⟩ := h
  exact fun o ho => (hout o ho).2

theorem data_hkD (d : MachineData) (n : Nat) (hok : d.ok = true) (hco : d.callsOk n = true) :
    n ≤ d.bsIn.length := by
  have h1 := Tools.ShippingQuadCalls.ok_bsIn_length d hok
  have h2 := callsOk_nIn d n hco
  omega

theorem data_hIlen (d : MachineData) (n : Nat) (hok : d.ok = true) (hco : d.callsOk n = true) :
    (d.bsIn.drop n).length = d.shape.insts.length := by
  have h1 := Tools.ShippingQuadCalls.ok_bsIn_length d hok
  have h2 := callsOk_nIn d n hco
  simp only [List.length_drop]
  omega

theorem data_hSL (d : MachineData) (hok : d.ok = true) : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain := by
  intro b hb
  obtain ⟨h1, h2⟩ := ok_slotLet d hok
  rcases List.mem_append.mp hb with h | h
  · exact h1 b h
  · exact h2 b h

theorem data_hSlen (d : MachineData) (hok : d.ok = true) (hslots : d.ss.length = d.shape.layout.slots.length) :
    d.slotBs.length = d.shape.layout.slots.length := by
  have h1 := Tools.ShippingQuadCalls.ok_len d hok
  simp only [MachineData.slotBs, List.length_take, List.length_drop]
  omega

theorem data_hLlen (d : MachineData) (hok : d.ok = true) : d.letBs.length = d.shape.layout.lets :=
  (Tools.ShippingQuadCalls.ok_lets d hok).symm

theorem data_hNIn (d : MachineData) (n : Nat) (hok : d.ok = true) (hco : d.callsOk n = true)
    (hslots : d.ss.length = d.shape.layout.slots.length) :
    machNIn d.shape = ((d.bsIn.take n).filter (fun b => b.2 != .domain)).length := by
  have h1 := Tools.ShippingQuadCalls.ok_len d hok
  have h2 := Tools.ShippingQuadCalls.ok_lets d hok
  have h3 : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp only [MachineData.letBs, List.length_drop]
  have h4 := callsOk_nIn d n hco
  unfold machNIn
  have h6 : d.shape.binders.length - d.shape.insts.length - d.shape.layout.slots.length
      - d.shape.layout.lets = n := by omega
  rw [h6]
  simp only [MachineData.bsIn, List.take_take]
  have h7 : min n d.nIn = n := by omega
  rw [h7]

end Tools.ShippingGen2
