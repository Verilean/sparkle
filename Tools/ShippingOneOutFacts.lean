import Tools.ShippingChecksOuts
import Tools.ShippingChecksRaw
import Tools.ShippingChecksDesign
import Tools.ShippingTextShipped
import Tools.ShippingClosedTyped
import Tools.ShippingLinkedFresh
import Tools.ShippingHierGateAny
import Tools.ShippingMachineDepthHR
import Tools.ShippingChildServe
import Tools.ShippingOneOutClose
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

variable {tenv : Lean.Environment}

/-! # The run's facts of a machine whose calls are tied by the ONE-OUTPUT closing (G1, round par/a-6)

`Tools.ShippingChecksRunFacts.core_runFacts` gives the facts of the full
entry's module of a machine with calls for the GROUP closing only
(`instFields ≠ []`): distinct instance names and the self-read test are read
off `MachineWired`'s clause that is conditional on it. Every census parent of
a gate child (`caller`, …) is closed by `closeInsts` (`instFields = []`).
This file derives the same facts for THAT closing, from the closing's own
result (`Tools/ShippingOneOutClose.lean`), for the COMBINATIONAL head
(`machine_ships_hierHC` / `ships_design_svH_all`):

* `core_closeInsts`: the run's closing, exposed (the pure `closeInsts … =
  some (M, D)`, the harness run, `closeLets`, the real children);
* `core_kidsComb₁`: `kidsComb D.modules (checkedOptimize b).body` — the
  closing RUNS `kidsCombB` (`closeInsts_kidsComb`); the shipped module has
  the full entry's instance statements (`checkedOptimize_inst_iff_gate`);
* `core_instNames₁`: `(instNames b.body).Nodup` (`closeInsts_instNames`);
* `core_noSelfRead₁`: `noSelfRead (childMap D.modules) b.body`
  (`noSelfRead_of_calls`);
* `core_outsExtracted₁`: `outsExtracted (childMap D.modules) b` — WITHOUT the
  per-child premise `hkidP` of `core_outsExtracted`: the one-output closing
  itself checks that the child has ONE output port, not named as an argument
  port (`CallStmt`);
* `core_kidsNotSeq₁`: no instance's child has a clock or reset input (the
  closing's own check, any child kind);
* `core_rst_any`: `"rst" ∈ b.inputs` — for a parent WITH a register
  (`hsl`), either closing (`core_raw_facts`' first conjunct, which never used
  `hfne`);
* `RunFactsH`, `core_runFactsH`: the bundle the combinational head takes;
* `designCheckH_rest`, `core_designCheckH`: `designCheck C n (checkedOptimize
  b)` from `RunFactsH`, linked well-formedness, `TypedIn b`, the connection
  widths and the children's check — `core_designCheck_rest2` without the two
  fields of `RunFacts` it never read (`rst`, `wid`).

What is NOT here: `instOutWidthsOk` (the sequential bundle's conjunct 8; the
combinational head does not ask it), `portsMatchB` and `hierTyped` for a
gate child (the child's port widths are not derived: see
`docs/parallel/A-oneout.md`).

SCOPE of every theorem: a machine with calls, `instFields = []`. The
parent's own register is asked ONLY by `core_rst_any` / `core_runFactsH` /
`core_designCheckH` (`hsl`); nothing here covers a parent without a
register.

The statements' hypothesis block and several proof passages are copied by a
script from `Tools/ShippingChecksOuts.lean` (`core_outsExtracted`) and
`Tools/ShippingChecksRaw.lean` (`core_raw_facts`); if those change, these
copies do not follow.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutFacts
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

/-- **The one-output closing of a core run, exposed**: a core run of a
machine with calls and `instFields = []`, at the machine boundary, returns
`closeInsts` of the closed machine of a harness run, with real children. -/
theorem core_closeInsts {c : Name} (d : MachineData)
    (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = [])
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∃ (tenv : Lean.Environment) (logProf : String → IO Unit) (t t' : Sparkle.IR.AST.Module)
      (d₀ : Design)
      (children : List (Sparkle.IR.AST.Module × Design)),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) logProf c
        d.shape.binders d.shape.body) (t, d₀) ∧
      closeLets d.shape.layout.lets t = some t' ∧
      closeInsts (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
        (closeMachine d.shape.layout t', d₀) = some (M, D) ∧
      ChildrenReal mref cref d.shape children := by
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
  rcases hcc with ⟨-, hI⟩ | ⟨hfe, -, -⟩
  · exact ⟨_, _, t, t', d₀, children, run, hcl, hI, hreal⟩
  · exact absurd hf hfe

set_option maxHeartbeats 4000000 in
/-- `kidsComb` of the full entry's module: the one-output closing runs the
children's combinational check (`kidsCombB`) on its result. -/
theorem core_kidsComb_raw₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineDepthH.kidsComb D.modules b.body = true := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInsts d hins hf hB hcore entry closes
  rw [hbody']
  exact Tools.ShippingMachineDepthHR.kidsComb_of_B
    (Tools.ShippingChildServe.closeInsts_kidsComb hI)

set_option maxHeartbeats 4000000 in
/-- **Premise `kidsComb D.modules (checkedOptimize b).body` of the
combinational head, from the run**: the one-output closing runs the
children's combinational check on its result; the shipped module has the
full entry's instance statements. -/
theorem core_kidsComb₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineDepthH.kidsComb D.modules (checkedOptimize b).body = true := by
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingHierGateAny.core_hierGate_any d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  have hM : Tools.ShippingMachineDepthH.kidsComb D.modules b.body = true :=
    core_kidsComb_raw₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB
      hcore hpost entry closes
  exact Tools.ShippingChecksDerived2.all_inst_transfer _
    (fun mn iname conns =>
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hM

set_option maxHeartbeats 4000000 in
/-- **Distinct instance names of the full entry's module, one-output
closing** (conjunct 3 of `hierCheck`; `RunFacts.ndB`). -/
theorem core_instNames₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    (Tools.ShippingHierState.instNames b.body).Nodup := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInsts d hins hf hB hcore entry closes
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  rw [hbody']
  exact Tools.ShippingOneOutClose.closeInsts_instNames hI
    (Tools.ShippingOneOutClose.instNames_nil_of_seqOk hseq0)

set_option maxHeartbeats 4000000 in
/-- **No instance of the full entry's module reads its own output,
one-output closing** (`RunFacts.self`; conjunct 5 of `hierCheck` after the
transfer to the shipped module). -/
theorem core_noSelfRead₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInsts d hins hf hB hcore entry closes
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  rw [hbody']
  refine Tools.ShippingOneOutClose.noSelfRead_of_calls (fun mn iname conns hm => ?_)
  rcases Tools.ShippingMachineInst.closeInsts_insts hI _ hm rfl with
    h0 | ⟨k, args, child, mc, hargs0, hch0, hmc, hcs⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  · have hfind : moduleByName D.modules mc.name = some mc := by
      rw [Tools.ShippingMachineInst.moduleByName_name hmc]
      exact hmc
    exact ⟨_, _, _, _, k, args, mc, hfind, hcs⟩

set_option maxHeartbeats 4000000 in
/-- **In the one-output closing no instance's child is sequential** — for
ANY kind of child, by the closing's own check (`CallStmt`: no `clk` / `rst`
input). So the clock / reset connection case of the port matching
(`hclkB` / `hkidClk` of `core_portsMatch_raw`) is vacuous for these parents.
This is about the CHILDREN; it does not remove the parent's own register
condition where a head asks the parent's `rst` input (`core_rst_any`). -/
theorem core_kidsNotSeq₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ isSeqChild mc = false := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInsts d hins hf hB hcore entry closes
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  intro mn iname conns hm
  rw [hbody'] at hm
  rcases Tools.ShippingMachineInst.closeInsts_insts hI _ hm rfl with
    h0 | ⟨k, args, child, mc, hargs0, hch0, hmc, hcs⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  · obtain ⟨outW, argWs, outP, hmn, -, -, hclk, -, -, -, -⟩ :=
      Tools.ShippingOneOutClose.callStmt_parts hcs
    have hns : isSeqChild mc = false := hclk
    refine ⟨mc, ?_, hns⟩
    rw [hmn, Tools.ShippingMachineInst.moduleByName_name hmc]
    exact hmc

set_option maxHeartbeats 4000000 in
/-- **Every instance-driven wire of the full entry's module is an extracted
input of the optimizer check, one-output closing** (conjunct 6 of
`hierCheck`; `RunFacts.outs`). No premise about the children: the closing
checks the child's single output port. -/
theorem core_outsExtracted₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  -- the full entry's body is the raw module's; no assignment targets an instance output
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  have hasg := Tools.ShippingLinkedFresh.core_instOuts_not_assigned d ok hbody hC hslots hdomB
    hins outTy hnomem hB hcore hpost entry closes
  -- the cleanup and the checked merge keep the inputs and the non-zero wires
  have hbin : b.inputs = M.inputs := by
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
  -- the run: the one-output closing
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInsts d hins hf hB hcore entry closes
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ :=
    Tools.ShippingMachineInst.closeInsts_some hI
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨PI, ls, hin, hPI, hlsL, hndI, hinW, hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  have hlenT : t.inputs.length = PI.length + ls.length := by
    rw [hin, List.length_append]
  -- an instance-driven wire is a call port of the transition
  have hident : ∀ x, x ∈ Tools.ShippingHierOpen.bodyInstOuts (childMap D.modules) M.body →
      ∃ k, k < d.shape.insts.length ∧
        (t.inputs.map (·.name))[machNIn d.shape + k]? = some x := by
    intro x hx
    obtain ⟨st, hst, hxs⟩ := Tools.ShippingOutsExtractedParts.mem_bodyInstOuts M.body x hx
    cases st with
    | inst mn iname conns =>
      rcases Tools.ShippingMachineInst.closeInsts_insts hI _ hst rfl with
        h0 | ⟨k, args, child, mc, hargs0, hch0, hmc, hcs⟩
      · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
      · obtain ⟨outW, argWs, outP, hmn, hout, houts, -, -, -, hall, -⟩ :=
          Tools.ShippingOneOutClose.callStmt_parts hcs
        have hk0 : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hargs0).1
          simpa using this
        have hfind' : moduleByName D.modules mn = some mc := by
          rw [hmn, Tools.ShippingMachineInst.moduleByName_name hmc]
          exact hmc
        obtain ⟨p, hp, hpc⟩ := Tools.ShippingOutsExtractedParts.stmtInstOuts_inst hfind' hxs
        rw [houts] at hp
        have hpe : p = outP := List.mem_singleton.mp hp
        rw [hpe] at hpc
        rcases hall _ hpc with e | ⟨q, -, aw, -, e, hqo⟩
        · have h2 : Sparkle.IR.AST.Expr.ref x = Sparkle.IR.AST.Expr.ref outW :=
            congrArg Prod.snd e
          have hxo : x = outW := Sparkle.IR.AST.Expr.ref.inj h2
          rw [hxo]
          exact ⟨k, hk0, hout⟩
        · exact absurd (congrArg Prod.fst e).symm hqo
    | _ =>
      have hx' : x ∈ ([] : List String) := hxs
      cases hx'
  refine Tools.ShippingOutsExtractedParts.outsExtracted_of_parts ?_ ?_ ?_
  · -- (a) a declared wire
    intro x hx
    rw [hbody'] at hx
    obtain ⟨k, hk, hget⟩ := hident x hx
    rw [List.getElem?_map] at hget
    cases hq : t.inputs[machNIn d.shape + k]? with
    | none =>
      rw [hq] at hget
      cases hget
    | some q =>
      rw [hq] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      obtain ⟨hqw, hqz⟩ := hinW q (List.mem_of_getElem? hq)
      exact ⟨q, hbw q (by rw [hMw]; exact hqw) hqz, hget⟩
  · -- (c) not driven
    intro x hx hdr
    rcases Tools.ShippingOutsExtractedParts.mem_drivesOf hdr with hwr | ⟨c', rs, inp, init, hreg⟩
    · exact hasg x hx hwr
    · rw [hbody'] at hx hreg
      obtain ⟨k, hk, hget⟩ := hident x hx
      have hreg' : Stmt.register x c' rs inp init ∈ (closeMachine d.shape.layout t').body := by
        rcases List.mem_append.mp (hperm.symm.subset hreg) with h0 | h0
        · exact h0
        · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hLinst _ h0)
      obtain ⟨i, p, hi, hpi, hpn⟩ := hregs x c' rs inp init hreg'
      have hgi : (t.inputs.map (·.name))[i]? = some x := by
        rw [List.getElem?_map, hpi]
        exact congrArg some hpn
      have heq : machNIn d.shape + k = i :=
        Tools.ShippingOutsExtractedParts.getElem?_nodup_inj hndI hget hgi
      omega
  · -- (d) not an input
    intro x hx hxin
    rw [hbody'] at hx
    obtain ⟨k, hk, hget⟩ := hident x hx
    obtain ⟨outWsI, hmapI, hMin⟩ := Tools.ShippingMachineInst.closeInsts_inputs hI
    rw [hbin, hMin] at hxin
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hxin
    have hpf : (!outWsI.contains p.name) = true := (List.mem_filter.mp hp).2
    rw [hpn] at hpf
    have hnot : x ∉ outWsI := by simpa [List.contains_eq_mem] using hpf
    obtain ⟨-, hgetI⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hmapI
    obtain ⟨y, hy, hyi⟩ := hgetI k (by simpa using hk)
    simp only [List.getElem_range] at hy
    have hy' : (t.inputs.map (·.name))[machNIn d.shape + k]? = some y := hy
    have hyx : y = x := (Option.some.inj (hget.symm.trans hy')).symm
    rw [hyx] at hyi
    exact hnot (List.mem_of_getElem? hyi)

set_option maxHeartbeats 4000000 in
/-- **The reset input of the full entry's module of a machine with calls and
WITH a register** (conjunct 7 of `hierCheck`; `RunFacts.rst`), either
closing. The parent's register (`hsl`) is what gives it: a slotless parent of
combinational children has no `rst` input. -/
theorem core_rst_any {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) := by
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
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
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
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hAlloc, -, -, -, -, -, -, -, -, -, -, -, -, -, hcleanAny, hInputs, -⟩ := wired
  obtain ⟨-, -, hzi, -⟩ := hcleanAny outTy
  obtain ⟨outWs, extra, houtWs, -, -, hMin⟩ := hInputs
  have hbin : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact hzi
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact hzi
  have hne : d.shape.layout.slots.isEmpty = false := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons _ _ => rfl
  have hnotW : "rst" ∉ outWs := by
    intro hm
    obtain ⟨k, -, hk⟩ := houtWs _ hm
    exact Tools.ShippingChecksRaw.rst_not_allocated (hAlloc _ (List.mem_of_getElem? hk))
  have hrstM : "rst" ∈ M.inputs.map (·.name) := by
    rw [hMin]
    refine List.mem_map.mpr ⟨{ name := "rst", ty := .bit }, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [hne]
      simp
    · simpa using hnotW
  rw [hbin]
  exact hrstM

/-- **What the combinational head takes of the full entry's module** (the
conjuncts of `hierCheck` that are about `b`, and the children's
combinational check): each field is derived from the core run for the
one-output closing (`core_runFactsH`). -/
structure RunFactsH (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module) : Prop where
  gate : Sparkle.IR.RefineCheck.hierGate b = true
  ndB : (Tools.ShippingHierState.instNames b.body).Nodup
  self : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true
  outs : Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true
  rst : "rst" ∈ b.inputs.map (·.name)
  comb : Tools.ShippingMachineDepthH.kidsComb ms b.body = true

set_option maxHeartbeats 4000000 in
/-- **The run's facts for the combinational head**, from the core run of a
machine WITH a register whose calls are tied by the one-output closing. -/
theorem core_runFactsH {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hsl : d.shape.layout.slots ≠ []) :
    RunFactsH D.modules b :=
  { gate := Tools.ShippingHierGateAny.core_hierGate_any d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
    ndB := core_instNames₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB
      hcore hpost entry closes
    self := core_noSelfRead₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB
      hcore hpost entry closes
    outs := core_outsExtracted₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB
      hcore hpost entry closes
    rst := core_rst_any d ok hbody hC hslots hdomB hins hsl outTy hnomem hB hcore hpost entry
      closes
    comb := core_kidsComb_raw₁ d ok hbody hC hslots hdomB hins hf outTy hnomem hB
      hcore hpost entry closes }

/-- The shipped module of a module with `RunFactsH`, linked-well-formed: it
is linked-well-formed, has distinct instance names, no instance reading its
own output, and combinational children. -/
theorem shipped_factsH {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h : RunFactsH ms b)
    (hwfB : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true) :
    Tools.ShippingHierOpen.linkedWF (childMap ms) (checkedOptimize b).body = true ∧
      (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup ∧
      Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) (checkedOptimize b).body = true ∧
      Tools.ShippingMachineDepthH.kidsComb ms (checkedOptimize b).body = true := by
  obtain ⟨hwfS, hndS, -⟩ :=
    Tools.ShippingGuardsSound.checkedOptimize_facts h.gate hwfB h.ndB h.outs
  refine ⟨hwfS, hndS, ?_, ?_⟩
  · exact Tools.ShippingChecksDerived2.all_inst_transfer _
      (fun mn iname conns =>
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate h.gate mn iname conns).mp)
      (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h.self
  · exact Tools.ShippingChecksDerived2.all_inst_transfer _
      (fun mn iname conns =>
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate h.gate mn iname conns).mp)
      (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h.comb

/-- **`designCheck` of the shipped module, at every depth, from `RunFactsH`**:
the structural and the text conjuncts derived; left are the connection
widths (`portsMatchB`) and the children's check. (`core_designCheck_rest2`
for the combinational head: it never read `RunFacts.rst` / `RunFacts.wid`.) -/
theorem designCheckH_rest {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h : RunFactsH ms b)
    (hwfB : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true)
    (ht : Tools.ShippingTextTyped.TypedIn b) (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap ms) (checkedOptimize b) = true)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) n) (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n (checkedOptimize b) = true := by
  obtain ⟨h2, h3⟩ := Tools.ShippingTextShipped.text_shipped_of h.gate ht.seqCheck
  obtain ⟨hwfS, hndS, hselfS, -⟩ := shipped_factsH h hwfB
  rw [Tools.ShippingChecksDesign.designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (Tools.ShippingChecksDesign.textCheckI_of
      (Tools.ShippingChecksDesign.seqStmtOkI_of_linkedWF _ hwfS) h2 h3 hwfS hndS hselfS hports
      (fun mn iname conns hm => by
        obtain ⟨child, cwe, hc, -⟩ :=
          Tools.ShippingGuardsSound.linkedWF_inst _ hwfS mn iname conns hm
        simp [hc]))
    hkids

set_option maxHeartbeats 4000000 in
/-- **Premise `designCheck (childMap D.modules) n (checkedOptimize b)` of the
combinational head, from the run and ONE check premise** — the connection
widths `portsMatchB` of the shipped module — for a machine WITH a register
whose calls are tied by the one-output closing; `hkidK` is the children's
check per real child (`gate_real_kidK` for a gate child). -/
theorem core_designCheckH {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hsl : d.shape.layout.slots ≠ [])
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
        ∀ g ∈ y.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  designCheckH_rest
    (core_runFactsH d ok hbody hC hslots hdomB hins hf outTy hnomem hB
      hcore hpost entry closes hsl)
    (Tools.ShippingLinkedFresh.core_linkedWF d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes)
    (Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes hon hoty)
    n hports
    (Tools.ShippingHierGateAny.core_kidsPass_any d ok hbody hC hslots hdomB hins outTy hnomem
      hkidK hB hcore hpost entry closes n)

end Tools.ShippingOneOutFacts
