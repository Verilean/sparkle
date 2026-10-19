import Tools.ShippingWireNamesRun
import Tools.ShippingSlotlessClk
import Tools.ShippingSatInputs
-- Round par/sat. BUILT: sa1 (ComposedGW, NoPortsTypedBW exit ok; SatInputs failed: 7 tactic/term errors, fixed by the worker), sa2 (all, exit 0, 669 jobs).

/-! # The full entry's inputs are wires, from the core run (round par/sat)

`inputWires_runMT`: for the machine-route full entry with calls (premises of `wireNames_runMT`
without the two output data conditions), every input `p` of `b` other than `clk` / `rst` whose
type has positive width is a WIRE of `b`. With `b`'s wire names distinct (`wireNames_runMT`) this
gives the input's declared width (`Tools.ShippingSatInputs.declWidth_of_wire`) and its emitted
width in the shipped module (`Tools.ShippingSatInputs.weS_input`) — the width hypotheses of the
head's conclusion for an input stream.

The chain (all from the run, prelude copied from `Tools.ShippingSlotlessClk.core_seqKid_inputs`):

    b.inputs = M.inputs                                   (cleanup / checked merge keep inputs)
    M.inputs ⊆ (withClockFor children (closeMachine lay t')).inputs   (closeInstsG_inputs: a filter)
             ⊆ (closeMachine lay t').inputs ∪ {clk, rst}  (withClockFor_sub)
             ⊆ t'.inputs ∪ {clk, rst}                     (closeMachine_inputs_sub, below)
    t'.inputs ⊆ t'.wires                                  (closedTransition_of_run)
    t'.wires ⊆ (closeMachine lay t').wires = M.wires      (closeMachine_wires_sub, CloseCalls.some)
    M.wires of positive width ⊆ b.wires                   (dropZW_wires, mergeChecked_ports)

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingInputWiresRun
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

/-- The closed machine's inputs are the transition's, or `clk` / `rst`. -/
theorem closeMachine_inputs_sub (lay : Layout) (t : Sparkle.IR.AST.Module) :
    ∀ p ∈ (closeMachine lay t).inputs, p ∈ t.inputs ∨ p.name = "clk" ∨ p.name = "rst" := by
  unfold closeMachine
  split
  · intro p hp
    exact Or.inl hp
  · intro p hp
    -- (writing-time guess, accepted by build sa1/sa2: the `some w` branch's inputs, as `closeMachine_wires_sup` reads its wires)
    have hp' : p ∈ t.inputs.take (t.inputs.length - lay.slots.length) ++
        (if lay.slots.isEmpty then [] else
          [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)]) := hp
    rcases List.mem_append.mp hp' with h | h
    · exact Or.inl (List.mem_of_mem_take h)
    · exact Or.inr (Tools.ShippingSatInputs.clkrst_of_mem_if h)

/-- The closed machine keeps the transition's wires. -/
theorem closeMachine_wires_sub (lay : Layout) (t : Sparkle.IR.AST.Module) :
    ∀ p ∈ t.wires, p ∈ (closeMachine lay t).wires := by
  unfold closeMachine
  split
  · intro p hp
    exact hp
  · intro p hp
    show p ∈ t.wires ++ (t.inputs.drop (t.inputs.length - lay.slots.length)).map
        (fun p => ({ name := nextName p.name, ty := p.ty } : Port))
    exact List.mem_append_left _ hp

set_option maxHeartbeats 4000000 in
/-- **Every input of the full entry's module other than `clk` / `rst`, of positive width, is a
wire of it**, from the core run of a machine with calls (the general closing). -/
theorem inputWires_runMT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires := by
  -- the post-processing keeps the inputs and the wires of positive width
  have hbi : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
  have hbw : ∀ p ∈ M.wires, p.ty.bitWidth ≠ 0 → p ∈ b.wires := by
    intro p hp hz
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
  -- the run (copied from `core_seqKid_inputs`)
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
  · exact absurd hno hins
  have hG : closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀) = some (M, D) := by
    rcases hcc with ⟨hfe, -⟩ | ⟨-, hG, -⟩
    · exact absurd hfe hfne
    · exact hG
  -- the closed module's wires are the closed machine's
  -- (writing-time guess, accepted by build sa1/sa2: `CloseCalls.some`'s first conjunct is `M.wires = (closeMachine …).wires`)
  obtain ⟨hMw, -⟩ := hcc.some
  -- the let-closed transition's inputs are wires
  -- (writing-time guess, accepted by build sa1/sa2: 11 components, the 7th `∀ p ∈ t'.inputs, p ∈ t'.wires`)
  obtain ⟨-, -, -, -, -, -, inWc, -, -, -, -⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  -- the closing keeps the clocked module's inputs but the call ports
  obtain ⟨outWs, -, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
  intro p hp hc hr hz
  rw [hbi, hMin] at hp
  have hp1 := (List.mem_filter.mp hp).1
  rcases withClockFor_sub children _ p hp1 with hp2 | hpc | hpr
  · rcases closeMachine_inputs_sub d.shape.layout t' p hp2 with hp3 | hpc | hpr
    · have hpw : p ∈ M.wires := by
        rw [hMw]
        exact closeMachine_wires_sub d.shape.layout t' p (inWc p hp3)
      exact hbw p hpw hz
    · exact absurd hpc hc
    · exact absurd hpr hr
  · exact absurd hpc hc
  · exact absurd hpr hr

end Tools.ShippingInputWiresRun
