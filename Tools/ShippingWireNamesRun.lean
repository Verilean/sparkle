import Tools.ShippingNoPortsTypedI
import Tools.ShippingMemKidPorts
import Tools.ShippingChecksWidths
import Tools.ShippingNamesClk
import Tools.ShippingNamesStable
import Tools.ShippingClosedTyped
import Tools.ShippingClosedTransitionTyped
import Tools.ShippingCloseMachineTyped
-- BUILT as written: wn1 (`lake build Tools.ShippingWireNamesRun`, exit 0); used by `Tests.Compiler.MemNameCollisionGateBoundTest` (gb1, exit 0) (round par/wn).

/-! # The full entry's wire names from the core run (round par/wn)

`Tools.ShippingNoPortsTypedI.weS_checkedOptimize_le` reduces the width relation off the ports,
`weS (checkedOptimize b) x ≤ declWidth b x`, to two facts about the full entry's module `b`:

* (hnd) `(b.wires.map (·.name)).Nodup`;
* (hs)  every wire, input and output name of `b` is sanitize-stable.

`wireNames_runMT` derives both for the machine-route full entry with instance calls, from the
core run, with EXACTLY the premises of `Tools.ShippingMemKid.core_closed_typedInMT` (a subset of
those of `Tools.ShippingKidsTyped.core_typedRunMT`):

* wires and outputs sanitize-stable: `TypedIn.wn`, `TypedIn.ostable` of `core_closed_typedInMT`
  (wires `Allocated` or `nextName` of an `Allocated` name, `sanitizeName_of_allocated` /
  `sanitizeName_nextName`; outputs by the data premise `hon`);
* inputs: the raw module's inputs are `Allocated`, `clk` or `rst` (the input list of the
  synthesis' wiring, `hinM`, as in `core_closed_typedInMT`); `dropZeroWidthModule` and
  `mergeChecked` keep the inputs;
* wire names distinct: the raw module's wires are the closed machine's (`CloseCalls`, first
  field), whose names are distinct (`closeMachine_typed`, second conjunct: transition wires
  distinct, `nextName` injective and never `Allocated`); `dropZeroWidthModule` filters the wires
  (a sub-list), `mergeChecked` keeps them.

`boundOffI_runMT` combines it with `core_hierGateMT`, `weS_checkedOptimize_le` and
`boundOffI_of_bounded`: from the same run premises, `Bounded (weS (checkedOptimize b)) st0`
gives the start-state hypothesis `BoundOff (declWidth b) (outputs ++ inputs) st0` that
`machine_design_noPortsTI` adds.

The run part of `wireNames_runMT` is copied verbatim from `core_closed_typedInMT`'s proof.
No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingWireNamesRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMemKid
open Tools.ShippingClosedTyped

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The zero-width cleanup's wires are a sub-list of the module's. -/
theorem dropZW_wires_sublist (M : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).wires.Sublist M.wires := by
  rcases Tools.ShippingClosedTyped.dropZW_wires_cases M with h | h
  · rw [h]
    all_goals exact List.Sublist.refl _
  · rw [h]
    all_goals exact List.filter_sublist

set_option maxHeartbeats 4000000 in
/-- **The full entry's wire names are distinct, and all its port and wire names are
sanitize-stable**, from the core run of a machine with calls (premises of
`core_closed_typedInMT`). -/
theorem wireNames_runMT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- the two data conditions on the output ports (as in `core_closed_typedInMT`)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs,
        Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
  -- wires and outputs: the typing of the full entry's module
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingMemKid.core_closed_typedInMT d ok hbody hC hslots hdomB hins outTy hfne
      hB hcore hpost entry closes hon hoty
  -- the post-processing keeps the inputs and (sub-lists) the wires
  have hbi : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
  have hbw : b.wires = (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).wires := by
    rcases hpost with h | h
    · rw [h]
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2]
  -- the run (copied from `core_closed_typedInMT`)
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  -- the data conditions
  have ok' := ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok'
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  -- the raw module's wiring: its inputs
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hnamesA, -, -, -, -, -, houtsM, -, -, -, -, -, -, -, hcleanAny, hinM, -⟩ := wired
  obtain ⟨outWs, extra, -, -, hextra, hMin⟩ := hinM
  have hMinputs : ∀ p ∈ M.inputs,
      Sparkle.IR.NameHints.Allocated p.name ∨ p.name = "clk" ∨ p.name = "rst" := by
    intro p hp
    rw [hMin] at hp
    have hp' := (List.mem_filter.mp hp).1
    rcases List.mem_append.mp hp' with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (hnamesA p.name (List.mem_map.mpr ⟨p, List.mem_of_mem_take h, rfl⟩))
      · split at h
        · cases h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
    · rcases hextra with he | ⟨he, -⟩
      · rw [he] at h
        cases h
      · rw [he] at h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  -- the `let`-closed transition and the closed machine: its wire names are distinct
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨-, hndCM, -, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hMnd : (M.wires.map Sparkle.IR.AST.Port.name).Nodup := by
    rw [hMw]
    exact hndCM
  refine ⟨?_, ?_⟩
  · -- distinct wire names: a sub-list of the raw module's
    rw [hbw]
    exact List.Nodup.sublist
      (List.Sublist.map (fun p : Sparkle.IR.AST.Port => p.name) (dropZW_wires_sublist M)) hMnd
  · intro p hp
    rcases List.mem_append.mp hp with hp' | hpo
    · rcases List.mem_append.mp hp' with hpw | hpi
      · exact hT.wn p hpw
      · rw [hbi] at hpi
        rcases hMinputs p hpi with ha | hc | hr
        · exact Tools.ShippingNamesStable.sanitizeName_of_allocated ha
        · rw [hc]
          exact Tools.ShippingNamesClk.sanitizeName_clk
        · rw [hr]
          exact Tools.ShippingNamesClk.sanitizeName_rst
    · exact hT.ostable p hpo

set_option maxHeartbeats 4000000 in
/-- **The start state within the declared widths off the ports, from the emitted widths**, for
the machine-route full entry with calls (premises of `wireNames_runMT`): the run hypothesis
`machine_design_noPortsTI` adds follows from its `Bounded (weS (checkedOptimize b)) st0`. -/
theorem boundOffI_runMT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    ∀ st0 : String → Nat,
      Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st0 →
      Tools.ShippingHierTyped.BoundOff (Sparkle.IR.RegDedup.declWidth b)
        (b.outputs.map (·.name) ++ b.inputs.map (·.name)) st0 := by
  obtain ⟨hnd, hs⟩ := wireNames_runMT d ok hbody hC hslots hdomB hins outTy hfne
    hB hcore hpost entry closes hon hoty
  have hg : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingMemKid.core_hierGateMT d ok hbody hC hslots hdomB hins hfne outTy
      hB hcore hpost entry closes
  intro st0 hW
  exact Tools.ShippingNoPortsTypedI.boundOffI_of_bounded hW
    (Tools.ShippingNoPortsTypedI.weS_checkedOptimize_le hg hnd hs)

end Tools.ShippingWireNamesRun
