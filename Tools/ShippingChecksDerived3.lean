import Tools.ShippingChecksDerived2

/-! # Outputs assigned: the closed machine, the cleanup, the checked merge (G1)

`outsCheck0_opt` (ShippingChecksDerived2) asks `outsA`: each child's module
assigns its outputs. Here is where that comes from for a machine child with
a register, as PURE facts about the entry's passes:

* `closeMachine_outs_assigned`: the register-closed module of a transition
  that ends in `assign out = w` assigns every output — `closeMachine` ends
  its body with `outAssigns w lay.outs`, one assignment per layout output,
  and its output ports are the layout's;
* `outsAssigned_congr`: a module with the same body and output ports (the
  zero-width cleanup, by the wiring's cleanup clause);
* `entry_outsAssigned`: the full entry's module — the cleaned module or its
  checked merge — assigns every output, when the closed module's body has a
  non-assignment (a register): the merge is then kept only under
  `refineCheck`.

What is NOT proved here
* The composition with a RUN. Three run facts are needed, each available
  where `Tools.ShippingSeqChildIface.seqChild_iface` gets its own:
  the core module is `closeMachine lay t'` (`synthesizeMachineCertified_runs`);
  `packedWire? t'.body = some w` — `closeLets` keeps the final
  `assign out = …` (`closeLets_eq'` describes `t'`; the `packedWire?` of
  that body is not stated anywhere); the cleanup clause and a register
  statement (`MachineWired`, as `machine_ships_wired` uses them).
* A slotless child (assignment-only body): its merge is validated by
  `validateMerge`, not `refineCheck`. -/
namespace Tools.ShippingChecksDerived3
open Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChecksDerived2

/-- **The closed machine assigns every output.** -/
theorem closeMachine_outs_assigned {lay : Layout} {t : Sparkle.IR.AST.Module} {w : String}
    (h : packedWire? t.body = some w) :
    ∀ p ∈ (closeMachine lay t).outputs,
      ∃ r, Stmt.assign p.name r ∈ (closeMachine lay t).body := by
  unfold closeMachine
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i w' heq
    intro p hp
    have hp' : p ∈ lay.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := hp
    obtain ⟨o, ho, hpe⟩ := List.mem_map.mp hp'
    subst hpe
    refine ⟨fieldRhs w' o.lo o.width, ?_⟩
    show Stmt.assign o.name (fieldRhs w' o.lo o.width) ∈
      (t.body.dropLast ++ nextAssigns w' _ lay.slots ++ registers lay.resetKind _ lay.slots) ++
        outAssigns w' lay.outs
    exact List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩)

theorem closeMachine_outsAssigned {lay : Layout} {t : Sparkle.IR.AST.Module} {w : String}
    (h : packedWire? t.body = some w) :
    Tools.ShippingDesignSVBack.outsAssigned (closeMachine lay t) = true :=
  outsAssigned_of_assigned (closeMachine_outs_assigned h)

/-- A module with the same body and output ports assigns the same outputs. -/
theorem outsAssigned_congr {m x : Sparkle.IR.AST.Module} (hb : x.body = m.body)
    (ho : x.outputs = m.outputs)
    (ha : Tools.ShippingDesignSVBack.outsAssigned m = true) :
    Tools.ShippingDesignSVBack.outsAssigned x = true :=
  outsAssigned_of_assigned fun p hp => by
    rw [ho] at hp
    obtain ⟨r, hr⟩ := Tools.ShippingDesignSVBack.outsAssigned_sound ha p hp
    exact ⟨r, by rw [hb]; exact hr⟩

/-- **The full entry's module assigns every output**, from: the core module
does, the zero-width cleanup keeps its body and output ports, and the body
has a non-assignment (so the merge is a checked refinement or the
identity). -/
theorem entry_outsAssigned {M b : Sparkle.IR.AST.Module}
    (hraw : Tools.ShippingDesignSVBack.outsAssigned M = true)
    (hzb : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body = M.body)
    (hzo : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs = M.outputs)
    (hna : M.body.all Sparkle.IR.RegDedup.isAssign = false)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
  have hz := outsAssigned_congr hzb hzo hraw
  rcases hpost with hb | hb
  · rw [hb]
    exact hz
  · rw [hb]
    exact mergeChecked_outsAssigned (by rw [hzb]; exact hna) hz

end Tools.ShippingChecksDerived3
