import Tools.ShippingLeafFive
import Tools.ShippingLeafPorts
import Tools.ShippingWireNamesRun
import Tools.ShippingOptSoundness
import Tools.ShippingOptimizePorts
import Tools.ShippingTransitionPortTys

/-! # The fifth inner antecedent of `leaf_sat_design`, from the run (round par/leaf5)

BUILT by the integrator: iw1 exit 1 (ambiguous `Module` → `Sparkle.IR.AST.Module`; the other errors were its cascade), iw2 exit 0 (561 jobs); axioms standard (ax8) (round par/leaf5, base 92d68f13). Theorems: checkedOptimize_ports_wires_any,
declWidth_le_weS_input, leaf_names, leaf_input_widths, leaf_sat_design_closed5.

`Tools.ShippingLeafFive.leaf_sat_design_closed` keeps one inner antecedent: every input of
`dropZeroWidth raw` has `declWidth (dropZeroWidth raw) x ≤ weS (checkedOptimize b) x`. Here:

* `checkedOptimize` keeps the ports in every branch (`Tools.ShippingOptimizePorts.checkedOptimize_ports`)
  and its wires are a sub-list of the input module's in every branch
  (`Tools.ShippingOptSoundness.checkedOptimize_wires_subset`: the optimizer filters declarations,
  `deinline` too) — no `hierGate` needed.
* `declWidth_le_weS_input` (pure): for `o` with `m`'s ports and a sub-list of its wires, distinct
  wire names, sanitize-stable names, no input sanitizing to an output's name, and every input's
  declared width at most its type's width (`tyW`), each input name has
  `declWidth m x ≤ weS o x`. (The emitter's map reads wires, then inputs, then outputs: a wire hit
  is a wire of `m` of that name, the first one by distinctness; an input hit has its type's width.)
* `leaf_names` (from `LeafKid`, `ChildBnd`, the run): the full entry's module `b` has distinct
  wire names, sanitize-stable wire/input/output names and no wire named `clk` / `rst` (prelude of
  `Tools.ShippingLeafPorts.leaf_run_ports`, copied with `ChildBnd` in place of `InvW`, plus
  `closeMachine_typed`'s wire and input clauses, as `Tools.ShippingWireNamesRun.wireNames_runMT`).
* `leaf_input_widths`: antecedent (5) for every `raw` with `b = drop raw ∨ b = mergeChecked (drop raw)`
  and `MachineWired … raw …` (whose cleanup clause gives the non-clock inputs' wire-table widths);
  `clk` / `rst` have declared width 0 (no such wire).
* `leaf_sat_design_closed5`: `leaf_sat_design_closed` with (5) discharged — NO inner antecedent.

Writing-time guesses (integrator: check first):
* (g1) `declWidth m` and `Tools.ShippingEntrySoundness.weOf m` definitionally equal (`show … from rfl`
  as in `Tools.ShippingTextTyped.pos_wire`);
* (g2) the copied prelude: `synthesizeCombinational_parts` 3-way destructuring with a trailing `-`,
  `rcases hmt … rotate_left`, `closedTransition_of_run d K.ok K.body K.calls K.ss K.dom run hcl`
  with `nDecl` inferred from `K.calls`;
* (g3) the MachineWired destructuring positions (`hclean` 11th, its inner clause
  `⟨⟨-, hzw, hzi, -⟩, -, -, -, -, -, -, hinWd, -⟩`, as in `leaf_run_ports`);
* (g4) `simp` closing the `find?`/`bind`/`getD`/`match` goals once the port type is split.
-/
namespace Tools.ShippingLeafInputWidths
open Sparkle.IR.AST
open Sparkle.IR.RegDedup (declWidth)

/-- A port type's width as the emitter's map and the wire table read it. -/
def tyW : Sparkle.IR.Type.HWType → Nat
  | .bitVector k => k
  | .bit => 1
  | _ => 0

/-- **The shipped module keeps the input module's ports and a sub-list of its wires**, in every
branch of `checkedOptimize` (no `hierGate`). -/
theorem checkedOptimize_ports_wires_any (b : Sparkle.IR.AST.Module) :
    (Sparkle.IR.OptCheck.checkedOptimize b).inputs = b.inputs ∧
      (Sparkle.IR.OptCheck.checkedOptimize b).outputs = b.outputs ∧
      ∀ p ∈ (Sparkle.IR.OptCheck.checkedOptimize b).wires, p ∈ b.wires :=
  ⟨(Tools.ShippingOptimizePorts.checkedOptimize_ports b).1,
    (Tools.ShippingOptimizePorts.checkedOptimize_ports b).2,
    Tools.ShippingOptSoundness.checkedOptimize_wires_subset b⟩

/-- **Antecedent (5), pure.** -/
theorem declWidth_le_weS_input {m o : Sparkle.IR.AST.Module} (hi : o.inputs = m.inputs)
    (ho : o.outputs = m.outputs) (hsub : ∀ p ∈ o.wires, p ∈ m.wires)
    (hnd : (m.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ m.wires ++ m.inputs ++ m.outputs,
      Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hoi : ∀ q ∈ m.outputs, ∀ p ∈ m.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name)
    (hIW : ∀ p ∈ m.inputs, declWidth m p.name ≤ tyW p.ty) :
    ∀ x ∈ m.inputs.map (·.name), declWidth m x ≤ Tools.ShippingDesignSV.weS o x := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
  subst hpx
  have hsp : Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    hs p (List.mem_append_left _ (List.mem_append_right _ hp))
  simp only [Tools.ShippingDesignSV.weS, Tools.ShippingDesignSV.wofOf, Tools.SVParser.EmitSem.weOf,
    Tools.SVParser.RoundtripProof.moduleWof]
  cases hf : (o.wires ++ o.inputs ++ o.outputs).find?
      (fun q => Sparkle.Backend.Verilog.sanitizeName q.name == p.name) with
  | none =>
    exfalso
    have hmem : p ∈ o.wires ++ o.inputs ++ o.outputs := by
      rw [hi]; exact List.mem_append_left _ (List.mem_append_right _ hp)
    have := List.find?_eq_none.mp hf p hmem
    simp [hsp] at this
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hqx : Sparkle.Backend.Verilog.sanitizeName q.name = p.name := by
      have := List.find?_some hf
      simpa using this
    rw [hi, ho] at hq
    rcases List.mem_append.mp hq with hq' | hqo
    · rcases List.mem_append.mp hq' with hqw | hqi
      · -- a wire of `o`: a wire of `m` of that name, the first one (distinct names)
        have hqb := hsub q hqw
        have hname : q.name = p.name :=
          (hs q (List.mem_append_left _ (List.mem_append_left _ hqb))).symm.trans hqx
        have hfd : m.wires.find? (fun r => r.name == p.name) = some q := by
          rw [← hname]; exact Tools.ShippingEntrySoundness.find?_of_nodup hnd hqb
        simp only [declWidth, hfd]
        obtain ⟨qn, qty⟩ := q
        cases qty <;> simp
      · -- an input: its type's width bounds its declared width
        have hqn : q.name = p.name :=
          (hs q (List.mem_append_left _ (List.mem_append_right _ hqi))).symm.trans hqx
        rw [← hqn]
        refine Nat.le_trans (hIW q hqi) ?_
        obtain ⟨qn, qty⟩ := q
        cases qty <;> simp [tyW]
    · exfalso
      have hst := hs q (List.mem_append_right _ hqo)
      exact hoi q hqo p hp (by rw [hsp, ← hqx, hst])

section Run
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingPortWidthsPure

set_option maxHeartbeats 4000000 in
/-- **The full entry's module of a leaf register machine: distinct wire names, sanitize-stable
wire and input names, no wire named `clk` / `rst`**, from the run. -/
theorem leaf_names {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hbnd : ChildBnd mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w') :
    (b.wires.map (·.name)).Nodup ∧
      (∀ p ∈ b.wires ++ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) ∧
      (∀ p ∈ b.wires, p.name ≠ "clk" ∧ p.name ≠ "rst") := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c dk.shape :=
    machineClosesAt_of_closes (K.closes mctx cctx)
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore K.entry hbnd
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd K.leaf hne'
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run dk K.ok K.body K.calls K.ss K.dom
      run hcl
  have ok := K.ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨-, hndCM, hwCM, hinCM, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := dk.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk K.outTy
  have hM' : M = closeMachine dk.shape.layout t' := hMeq
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
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine dk.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have h1 := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hM'] at h1
    exact h1
  have hMnd : (M.wires.map Sparkle.IR.AST.Port.name).Nodup := by
    rw [hM']
    exact hndCM
  refine ⟨?_, ?_, ?_⟩
  · rw [hbw]
    exact List.Nodup.sublist
      (List.Sublist.map (fun p : Sparkle.IR.AST.Port => p.name)
        (Tools.ShippingWireNamesRun.dropZW_wires_sublist M)) hMnd
  · intro p hp
    rcases List.mem_append.mp hp with hpw | hpi
    · exact (wire_ne_clk (hwCM p (hwsub p hpw))).1
    · rw [hbi, hM'] at hpi
      rcases hinCM p hpi with ha | hc | hr'
      · exact Tools.ShippingNamesStable.sanitizeName_of_allocated ha
      · rw [hc]
        exact Tools.ShippingNamesClk.sanitizeName_clk
      · rw [hr']
        exact Tools.ShippingNamesClk.sanitizeName_rst
  · intro p hp
    have h := wire_ne_clk (hwCM p (hwsub p hp))
    exact ⟨h.2.1, h.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **Antecedent (5) of `leaf_sat_design`, from the run**: for every `raw` whose cleanup (or its
checked merge) is the full entry's module `b` and that is wired (`MachineWired`), each input of
`dropZeroWidth raw` has its declared width at most its emitted width in `checkedOptimize b`. -/
theorem leaf_input_widths {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {d : MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hbnd : ChildBnd mref cref w)
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    {raw : Sparkle.IR.AST.Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    {regs lets : List String}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hW : MachineWired declName d.shape ids cache raw D regs lets) :
    ∀ x ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name),
      declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) x ≤
        Tools.ShippingDesignSV.weS (checkedOptimize b) x := by
  generalize hdr : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = dr at hpost ⊢
  -- `b` and `dr` have the same ports and wires
  have hP : dr.inputs = b.inputs ∧ dr.outputs = b.outputs ∧ dr.wires = b.wires := by
    rcases hpost with e | e
    · rw [e]; exact ⟨rfl, rfl, rfl⟩
    · rw [e]
      obtain ⟨a1, a2, a3⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports dr
      exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨hdi, hdo, hdw⟩ := hP
  -- the run's facts about `b`
  obtain ⟨hnd, hsWI, hwc⟩ := leaf_names K hbnd hr
  obtain ⟨-, -, -, -, hPI, -, -⟩ :=
    Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd (nDecl := d.nIn) d K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy hbnd hr K.entry (K.closes mctx cctx) K.outName K.outScalar
  -- the wiring of `raw`: the cleanup keeps the wire table and the inputs; a non-clock input has
  -- its type's width in the wire table
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := hW
  obtain ⟨⟨-, hzw, hzi, -⟩, -, -, -, -, -, -, hinWd, -⟩ := hclean K.leaf K.outTy
  rw [hdr] at hzw hzi
  -- the shipped module: ports kept, wires a sub-list
  have hoi' : (checkedOptimize b).inputs = dr.inputs :=
    (Tools.ShippingOptimizePorts.checkedOptimize_ports b).1.trans hdi.symm
  have hoo' : (checkedOptimize b).outputs = dr.outputs :=
    (Tools.ShippingOptimizePorts.checkedOptimize_ports b).2.trans hdo.symm
  have hsub : ∀ p ∈ (checkedOptimize b).wires, p ∈ dr.wires := by
    intro p hp
    rw [hdw]
    exact Tools.ShippingOptSoundness.checkedOptimize_wires_subset b p hp
  refine declWidth_le_weS_input hoi' hoo' hsub (by rw [hdw]; exact hnd) ?_ ?_ ?_
  · intro p hp
    rw [hdw, hdi, hdo] at hp
    rcases List.mem_append.mp hp with hp' | hpo
    · exact hsWI p hp'
    · exact hPI.ostable p hpo
  · intro q hq p hp
    rw [hdo] at hq
    rw [hdi] at hp
    exact hPI.oi q hq p hp
  · intro p hp
    by_cases hc : p.name = "clk" ∨ p.name = "rst"
    · -- no wire of that name: declared width 0
      have hnone : dr.wires.find? (fun q => q.name == p.name) = none := by
        rw [List.find?_eq_none]
        intro q hq
        rw [hdw] at hq
        have h := hwc q hq
        rcases hc with hc | hc <;> rw [hc] <;> simp [h.1, h.2]
      have h0 : declWidth dr p.name = 0 := by
        first | simp only [declWidth, hnone] | simp [declWidth, hnone]
      rw [h0]; exact Nat.zero_le _
    · have hc1 : p.name ≠ "clk" := fun e => hc (Or.inl e)
      have hc2 : p.name ≠ "rst" := fun e => hc (Or.inr e)
      have hpr : p ∈ raw.inputs := by rw [← hzi]; exact hp
      have h := hinWd p hpr hc1 hc2
      have e : declWidth dr p.name = Tools.ShippingEntrySoundness.weOf raw p.name := by
        show Tools.ShippingEntrySoundness.weOf dr p.name = _
        rw [hzw]
      rw [e, h]
      cases p with
      | mk pn pty => cases pty <;> simp [tyW]

end Run

end Tools.ShippingLeafInputWidths

/-! ## `leaf_sat_design` with all five inner antecedents discharged -/
namespace Tools.ShippingLeafInputWidths
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingSeqSVSoundness
open Tools.ShippingSatAssemblyS (slotInit)
open Tools.ShippingLeafSat
open Sparkle.IR.RegDedup (declWidth)


set_option maxHeartbeats 2000000 in
/-- **A leaf state machine at the full entry, at the design level, from the target start state:
every run hypothesis and every inner check antecedent discharged** — `leaf_sat_design_closed`
with (5) from `leaf_input_widths`. Premises: the run, the reflection bundle `LeafKid`, `ChildBnd`
and the data conditions of `leaf_sat_design`. -/
theorem leaf_sat_design_closed5 {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hlen : d.nIn + d.shape.layout.slots.length + d.shape.layout.lets = d.shape.binders.length)
    (hinitW : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape)
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
        (
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (T : Nat) (mems : MEnv),
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                (leafIns declName d.bsIn ids cache bools bits T) t st)) ∧
            ∃ envsO,
              runModule (declWidth (checkedOptimize b)) (checkedOptimize b).body
                (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                  (leafIns declName d.bsIn ids cache bools bits T)) T
                (tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                  (slotInit regs d.shape.layout.slots)) mems = some envsO ∧
              (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                  (kids : String → Tools.ShippingHierStateG.KT 0),
                Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b)
                  (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                    (leafIns declName d.bsIn ids cache bools bits T)) T
                  ⟨tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                    (slotInit regs d.shape.layout.slots), mems, kids⟩ envsO) ∧
              envsO.length = T ∧
              (∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j) ∧
              ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                (kids : String → Tools.ShippingHierStateG.KT 0)
                (envs' : List Sparkle.IR.Semantics.Env),
                Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b)
                  (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                    (leafIns declName d.bsIn ids cache bools bits T)) T
                  ⟨tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                    (slotInit regs d.shape.layout.slots), mems, kids⟩ envs' →
                envs' = envsO) := by
  obtain ⟨raw, D, hpost, ids, cache, regs, ⟨lets, hW⟩, H⟩ :=
    Tools.ShippingLeafFive.leaf_sat_design_closed d @soundL hnoI hsl hSS houtTy hlen hinitW hr
      entry closes K hbnd
  exact ⟨raw, D, hpost, ids, cache, regs, ⟨lets, hW⟩,
    H (leaf_input_widths K hbnd hr hpost hW)⟩

end Tools.ShippingLeafInputWidths
