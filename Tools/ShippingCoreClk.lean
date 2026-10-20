import Tools.ShippingClosedTyped
import Tools.ShippingPortWidthsPure
import Tools.ShippingMachineRanBase
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `clk` and `rst` are one bit in the full entry's module of a machine with calls and slots (G1, port matching)

`hclkB` of `Tools.ShippingPortsMatchRaw.core_portsMatch_raw`, derived from
the parent's core run:

    core_clk : weS b "clk" = 1 ∧ weS b "rst" = 1

for the full entry's module `b` of a machine WITH calls and WITH slots
(`d.shape.layout.slots ≠ []`, data).

The chain: `MachineWired`'s input clause (position 17) gives the raw
module's inputs as a filtered list

    (ports.take K ++ (if slots.isEmpty then [] else [clk, rst]) ++ extra).filter
      fun p => !outWs.contains p.name

with `outWs` the calls' ports — transition port names, hence allocated
names, hence neither `clk` nor `rst`: the filter keeps the two. The ports
before them are allocated names (clause 2), so no earlier input sanitizes to
`clk` / `rst`; the wires of `b` are allocated names or `next…` names
(`closeMachine_typed`; the closing of the calls, the cleanup and the merge
add no wire), so no wire does. The emitter's map reads wires, then inputs:
`Tools.ShippingPortWidthsPure.weS_clk_rst_filtered`.

The proof's prelude is `Tools.ShippingClosedTyped.core_closed_typedIn`'s
(copied), keeping one more component of the input clause.

NOT covered: a parent WITHOUT slots whose clock comes from a sequential
child only (`extra = [clk, rst]`, `slots = []` in the input clause): the
input clause does not say which disjunct of `extra` holds.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCoreClk
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_clk` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_clk` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_clk_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsl : d.shape.layout.slots ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 := by
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
  -- the run
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, hw9, -⟩ := ran0
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
  -- the raw module's wiring: the allocated port names (2), its inputs (17)
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hnamesA, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinM, -⟩ := wired
  obtain ⟨outWs, extra, houtW, -, -, hMin⟩ := hinM
  -- the `let`-closed transition and the closed machine: the wires' names
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨-, -, hwCM, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hMw] at this
    exact this
  -- the calls' ports are allocated names: the filter keeps `clk` and `rst`
  have hnotin : ∀ x : String, ¬ Sparkle.IR.NameHints.Allocated x → outWs.contains x = false := by
    intro x hx
    refine Bool.eq_false_iff.mpr (fun hc => ?_)
    obtain ⟨k, -, hk⟩ := houtW x (List.contains_iff_mem.mp hc)
    exact hx (hnamesA x (List.mem_of_getElem? hk))
  have hc : (!outWs.contains "clk") = true :=
    congrArg (fun v : Bool => !v) (hnotin "clk" Tools.ShippingMachineCleanup.not_allocated_clk)
  have hr : (!outWs.contains "rst") = true :=
    congrArg (fun v : Bool => !v) (hnotin "rst" Tools.ShippingRegisterSoundness.not_allocated_rst)
  have hs' : ¬ (d.shape.layout.slots.isEmpty = true) := fun h => hsl (List.isEmpty_iff.mp h)
  have hPal : ∀ p ∈ machPorts c ids cache d.shape.binders,
      Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => hnamesA p.name (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hbIn := hbi.trans hMin
  exact Tools.ShippingPortWidthsPure.weS_clk_rst_filtered hbIn (if_neg hs') hc hr
    (fun p hp => hwCM p (hwsub p hp)) hPal

set_option maxHeartbeats 4000000 in
/-- **The clock and the reset of the full entry's module of a machine with
calls and slots are one bit in the emitter's width map.** -/
theorem core_clk {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsl : d.shape.layout.slots ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 :=
  core_clk_ran d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

end Tools.ShippingCoreClk
