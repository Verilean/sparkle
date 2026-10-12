import Tools.ShippingTransitionTyped
import Tools.ShippingCoreWidth

/-! # The `let`-closed transition of a machine with calls, typed (G1)

What `Tools.ShippingCloseMachineTyped.closeMachine_typed` asks of the
transition `t'` that `closeMachine` closes — here for `t'` the result of
`closeLets` on a real harness run of a machine with calls, from the data
conditions (`d.ok`, `d.callsOk`) alone:

* `t'.body = B ++ [out := core]`, typed in `t'`'s wire table
  (`transition_typed_of_run`; through `closeLets` by the existing
  `closeLets_typed`, whose two premises are discharged here: a `let` port is
  declared at its type's width, the remaining wire has a positive width);
* the targets of `B` are allocated names (`named_of_typed`);
* the wires are the transition's (allocated, distinct), the inputs are
  wires, with distinct names;
* the SLOT ports — the last `|slots|` inputs of `t'`, the transition's
  inputs at positions `machNIn + |insts| + i` — are declared at their slots'
  widths: `Zip₂ (SlotOk (weOf t'))`. (For a machine with calls this fact is
  inside `synthesizeMachineCertified_soundX`, `slotsOk`, and not exported;
  it is re-derived here from `transitionPortTys_of_run` — the port of a
  binder has the binder's type — and the layout check
  `f.width = machWidth binder`.)
* **the remaining wire is declared at the core term's width**:
  `weOf t' core = d.core.1` — the packed wire is typed at the packed term's
  width (`PrintBaseAt.outputTyped`), the spine's high operands are declared
  at the `let` fields' widths (`SpineW`), every link is a typed
  concatenation (`spine_width`), and the packed term's width is the fields'
  plus the core's (`packLets_width`). With `MachineData.ok`'s
  `f.lo + f.width ≤ d.core.1` this is what makes the closed machine's
  part-selects typed.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingClosedTransitionTyped
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome Tools.ShippingCloseChecks Tools.ShippingCloseMachineFacts
open Tools.ShippingInstStmt Tools.ShippingGateChildComb Tools.ShippingKidsComb
open Tools.ShippingCallsParent Tools.ShippingCallsStmts Tools.ShippingDesignWith
open Tools.ShippingRankRun Tools.ShippingRankNames Tools.ShippingCallsRank
open Tools.ShippingClosedOrder Tools.ShippingMachineCloses
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases)
open Tools.ShippingCallsAssembly
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingChildInv
open Tools.ShippingCallsGate

set_option maxHeartbeats 4000000 in
/-- **The `let`-closed transition of a machine with calls**: typed, over
allocated distinct wires, its slot ports at the slots' widths, its remaining
wire at the core term's width. -/
theorem closedTransition_of_run {declName : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {logProf : String → IO Unit} {t t' : Sparkle.IR.AST.Module} {d₀ : Design}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀))
    (hcl : closeLets d.shape.layout.lets t = some t') :
    ∃ (B : List Stmt) (core : String),
      t'.body = B ++ [.assign "out" (.ref core)] ∧
      Tools.ShippingTypedPostSoundness.TypedStmts (Tools.ShippingEntrySoundness.weOf t') t'.body ∧
      (∀ l r, Stmt.assign l r ∈ B → Allocated l) ∧
      (∀ p ∈ t'.wires, Allocated p.name) ∧
      (∀ p ∈ t'.inputs, p ∈ t'.wires) ∧
      (t'.inputs.map Port.name).Nodup ∧ (t'.wires.map Port.name).Nodup ∧
      Tools.ShippingMachineClose.Zip₂
        (Tools.ShippingMachineClose.SlotOk (Tools.ShippingEntrySoundness.weOf t'))
        (t'.inputs.drop (t'.inputs.length - d.shape.layout.slots.length))
        d.shape.layout.slots ∧
      Tools.ShippingEntrySoundness.weOf t' core = d.core.1 := by
  -- the transition: typed, printable at the packed width, with the spine
  obtain ⟨ready, pb, B0, w, hB0, hspine⟩ :=
    Tools.ShippingTransitionTyped.transition_typed_of_run d ok hbody run
  obtain ⟨hwnd, hwalloc, hinW, P1, P2, hsp, hP2len, hP2len', hP2ty⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  -- the data conditions
  have hC' := hC
  simp only [MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq] at hC'
  obtain ⟨⟨⟨hnIn, -⟩, -⟩, -⟩ := hC'
  have ok' := ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok'
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Lean.Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  -- lengths
  have hlenT : t.inputs.length = P1.length +
      (d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets) := by
    rw [hsp, List.length_append, hP2len']
  -- `closeLets`
  have hacy : Acyclic t.body := pb.order
  obtain ⟨w0, al, core, hpw, hops, ht', hord⟩ :=
    Tools.ShippingCallsParent.closeLets_eq' hB0 hacy hcl
  have hti : t'.inputs = t.inputs.take (t.inputs.length - d.shape.layout.lets) := by rw [ht']
  have htw : t'.wires = t.wires := by rw [ht']
  have htb : t'.body = closedBody t al core := by rw [ht']
  clear ht'
  have hpw' : packedWire? t.body = some w := by simp [packedWire?, hB0]
  have hw0 : w0 = w := Option.some.inj (hpw.symm.trans hpw')
  rw [hw0] at hops
  have hdrop : t.body.dropLast = B0 := by simp [hB0]
  have hbody' : t'.body =
      (frontAliases al B0 ++ insertAliases al B0) ++ [.assign "out" (.ref core)] := by
    rw [htb]
    unfold closedBody
    rw [hdrop]
  have hweq : Tools.ShippingEntrySoundness.weOf t' = Tools.ShippingEntrySoundness.weOf t :=
    Tools.ShippingRegisterSoundness.weOf_congr_wires htw
  have hlenT' : t'.inputs.length =
      P1.length + d.shape.insts.length + d.shape.layout.slots.length := by
    rw [hti, List.length_take, hlenT]
    omega
  -- the packed wire is declared at the packed term's width
  have hmemOut : Stmt.assign "out" (.ref w) ∈ t.body := by
    rw [hB0]
    exact List.mem_append_right _ (List.Mem.head _)
  have htout := pb.outputTyped _ hmemOut
  have hwW : Tools.ShippingEntrySoundness.weOf t w = (packLets d.letFields d.core.2).1 :=
    htout.width
  have hwpos : 0 < Tools.ShippingEntrySoundness.weOf t w :=
    htout.refs_positive w (by simp [Sparkle.IR.Reorder.refsOf])
  -- the remaining wire's width
  have typedW : Tools.ShippingTypedPostSoundness.TypedStmts (wireWidth t.wires) t.body := by
    rw [← Tools.ShippingMachineClose.weOf_eq_wireWidth t]
    exact ready.typed
  have houtW : wireWidth t.wires "out" = 0 := by
    rw [← Tools.ShippingMachineClose.weOf_eq_wireWidth t]
    exact ready.outWidthZero
  have hdropLen : (t.inputs.drop (t.inputs.length - d.shape.layout.lets)).length =
      (d.letFields.map (·.1)).length := by
    rw [List.length_drop, List.length_map, hlenT]
    omega
  have hcw := Tools.ShippingCoreWidth.spine_width typedW houtW (d.letFields.map (·.1))
    (t.inputs.drop (t.inputs.length - d.shape.layout.lets)) w al core hspine hdropLen hwpos hops
  rw [← Tools.ShippingMachineClose.weOf_eq_wireWidth t] at hcw
  obtain ⟨hcw1, hcw2⟩ := hcw
  have hpk := Tools.ShippingCoreWidth.packLets_width d.letFields d.core.2
  have hcoreW : Tools.ShippingEntrySoundness.weOf t core = d.core.1 := by
    omega
  -- typedness through `closeLets`
  have typed' : Tools.ShippingTypedPostSoundness.TypedStmts
      (Tools.ShippingEntrySoundness.weOf t') t'.body := by
    by_cases hK : d.shape.layout.lets = 0
    · have ht : t' = t := by
        have h := hcl
        rw [hK] at h
        unfold closeLets at h
        simpa using h.symm
      rw [ht]
      exact ready.typed
    · obtain ⟨-, hmap⟩ := Tools.ShippingMachineClose.letOperands_chain _ _ hops
      refine Tools.ShippingMachineClose.closeLets_typed hK hcl hpw' hops ready.typed ?_ hcw2
      intro pa hpa
      have h1 : pa.1 ∈ al.map (·.1) := List.mem_map.mpr ⟨pa, hpa, rfl⟩
      have h2 : pa.1 ∈ t.inputs.drop (t.inputs.length - d.shape.layout.lets) :=
        Eq.mp (congrArg (fun l => pa.1 ∈ l) hmap) h1
      have hin : pa.1 ∈ t.inputs := List.mem_of_mem_drop h2
      exact Tools.ShippingCoreWidth.weOf_wire_bw hwnd (pb.wires _ (hinW _ hin)) (hinW _ hin)
  -- the names of the closed transition
  have acy' : Acyclic t'.body := by
    rw [htb]
    exact (Tools.ShippingSettledSoundness.assignmentOrderCheck_iff _).mp hord
  have names' : ∀ p ∈ t'.wires, Allocated p.name := by
    rw [htw]
    exact hwalloc
  obtain ⟨hnamed', -⟩ :=
    Tools.ShippingCloseMachineFacts.named_of_typed hbody' acy' typed' names'
  refine ⟨_, core, hbody', typed', fun l r h => (hnamed' l r h).1, names', ?_, ?_, ?_, ?_, ?_⟩
  · -- the inputs are wires
    rw [hti, htw]
    intro p hp
    exact hinW p (List.mem_of_mem_take hp)
  · -- distinct input names
    rw [hti, List.map_take]
    exact pb.inputNames.sublist (List.take_sublist _ _)
  · -- distinct wire names
    rw [htw]
    exact hwnd
  · -- the slot ports are declared at their slots' widths
    refine Tools.ShippingMachineClose.Zip₂.of_get ?_ ?_
    · rw [List.length_drop, hlenT']
      omega
    · intro i p f hp hf
      have hi : i < d.shape.layout.slots.length := (List.getElem?_eq_some_iff.mp hf).1
      rw [List.getElem?_drop] at hp
      have eidx : t'.inputs.length - d.shape.layout.slots.length + i =
          P1.length + (d.shape.insts.length + i) := by
        rw [hlenT']
        omega
      rw [eidx, hti, List.getElem?_take] at hp
      split at hp
      rotate_left
      · cases hp
      rw [hsp, List.getElem?_append_right (Nat.le_add_right P1.length (d.shape.insts.length + i)),
        Nat.add_sub_cancel_left] at hp
      -- the binder of the port
      have hlt : d.shape.insts.length + i < (d.shape.binders.drop nDecl).length := by
        rw [← hP2len]
        exact (List.getElem?_eq_some_iff.mp hp).1
      obtain ⟨bn, hbn⟩ : ∃ bn, (d.shape.binders.drop nDecl)[d.shape.insts.length + i]? =
          some bn := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hbn' := hbn
      rw [List.getElem?_drop] at hbn'
      have hbn2 : d.slotBs[i]? = some bn := by
        show ((d.shape.binders.drop d.nIn).take d.ss.length)[i]? = some bn
        rw [List.getElem?_take, if_pos (show i < d.ss.length by omega), List.getElem?_drop]
        have e : d.nIn + i = nDecl + (d.shape.insts.length + i) := by omega
        rw [e]
        exact hbn'
      have hbmem : bn ∈ d.shape.binders :=
        List.mem_of_mem_drop (List.mem_of_getElem? hbn)
      obtain ⟨hw, hnd, -⟩ := layW.get i f bn hf hbn2
      have hty := hP2ty (d.shape.insts.length + i) p bn hp hbn
      have hpw2 : p ∈ t.wires := hinW p (by
        rw [hsp]
        exact List.mem_append_right _ (List.mem_of_getElem? hp))
      have hwe := Tools.ShippingMachineEntry.weOf_of_port hwnd hpw2
      rw [hty] at hwe
      show Tools.ShippingEntrySoundness.weOf t' p.name = f.width ∧ 0 < f.width
      rw [hweq]
      cases hkb : bn.2 with
      | domain => exact absurd hkb hnd
      | bool =>
        rw [hkb] at hw hwe
        have h1 : Tools.ShippingEntrySoundness.weOf t p.name = 1 := hwe
        have h2 : f.width = 1 := hw
        exact ⟨h1.trans h2.symm, by rw [h2]; exact Nat.one_pos⟩
      | bits k =>
        rw [hkb] at hw hwe
        have h1 : Tools.ShippingEntrySoundness.weOf t p.name = k := hwe
        have h2 : f.width = k := hw
        have hk : 0 < k := hposv bn.1 k (by rw [← hkb]; exact hbmem)
        exact ⟨h1.trans h2.symm, by rw [h2]; exact hk⟩
  · -- the remaining wire is declared at the core term's width
    rw [hweq]
    exact hcoreW

end Tools.ShippingClosedTransitionTyped
