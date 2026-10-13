import Tools.ShippingChecksCore
import Tools.ShippingMachineRanBase

/-! # No assignment targets an instance-driven wire (G1, conjunct 6, part (c))

`outsExtracted C b` needs, of every instance-driven wire, that it is not in
`drivesOf b.body` — not an assignment target, not a register output. This
file gives the ASSIGNMENT half, from the linked well-formedness the wiring
states for the raw module.

What `linkedWF` covers, read from its definition
(`Tools/ShippingHierOpen.lean:61`) — BOTH directions:
* an assignment BEFORE an instance: `!(bodyInstOuts children rest).contains l`
  — its target is no output of a later instance;
* an assignment AFTER an instance: the instance's output wires are not in
  `linkedWrites children rest`, which contains every later assignment's
  target (`writes_sub_linked`).
A memory statement makes `linkedWF` false, so `writesOf` (which also lists a
combo-read memory's read wires) is the assignment targets on such a body.

* `writes_sub_linked`: under `linkedWF`, every written name is a linked
  write;
* `instOuts_not_written`: under `linkedWF C body`, no element of
  `bodyInstOuts C body` is in `writesOf body`;
* `core_linkedWF`: for a core run on a machine with calls (the hypotheses
  of `core_kids_facts`), `linkedWF (childMap D.modules) b.body` — the
  wiring's clause 7 with `linkedOk_eq`, moved to the full entry's module by
  `b.body = M.body`. The first part of its proof is `core_kids_facts`' (my
  own), copied by a script;
* `core_instOuts_not_assigned`: the two together.

NOT here: the register half of (c) (a register statement's output is not an
instance-driven wire), and (a) (the wire is declared). See
`Tools/ShippingChecksExtract.lean`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLinkedFresh
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
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)

/-- Under `linkedWF`, every written name is a linked write. -/
theorem writes_sub_linked {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)} :
    ∀ (body : List Stmt), linkedWF C body = true →
      ∀ n, n ∈ Sparkle.IR.Reorder.writesOf body → n ∈ linkedWrites C body
  | [], _, n, hn => by
    simp [Sparkle.IR.Reorder.writesOf] at hn
  | st :: rest, h, n, hn => by
    cases st with
    | assign l r =>
      simp only [linkedWF, Bool.and_eq_true] at h
      have hW : Sparkle.IR.Reorder.writesOf (Stmt.assign l r :: rest) =
          l :: Sparkle.IR.Reorder.writesOf rest := by
        simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
      rw [hW] at hn
      have hL : linkedWrites C (Stmt.assign l r :: rest) = l :: linkedWrites C rest := rfl
      rw [hL]
      rcases List.mem_cons.mp hn with e | hn'
      · rw [e]
        exact List.Mem.head _
      · exact List.Mem.tail _ (writes_sub_linked (C := C) rest h.2 n hn')
    | inst mn i conns =>
      have hrest : linkedWF C rest = true := by
        simp only [linkedWF, Bool.and_eq_true] at h
        exact h.2
      have hW : Sparkle.IR.Reorder.writesOf (Stmt.inst mn i conns :: rest) =
          Sparkle.IR.Reorder.writesOf rest := by
        simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
      rw [hW] at hn
      have hL : linkedWrites C (Stmt.inst mn i conns :: rest) =
          stmtInstOuts C (Stmt.inst mn i conns) ++ linkedWrites C rest := rfl
      rw [hL]
      exact List.mem_append_right _ (writes_sub_linked (C := C) rest hrest n hn)
    | register o c rk inp iv =>
      have hrest : linkedWF C rest = true := by
        simp only [linkedWF] at h
        exact h
      have hW : Sparkle.IR.Reorder.writesOf (Stmt.register o c rk inp iv :: rest) =
          Sparkle.IR.Reorder.writesOf rest := by
        simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
      rw [hW] at hn
      have hL : linkedWrites C (Stmt.register o c rk inp iv :: rest) =
          stmtInstOuts C (Stmt.register o c rk inp iv) ++ linkedWrites C rest := rfl
      rw [hL]
      exact List.mem_append_right _ (writes_sub_linked (C := C) rest hrest n hn)
    | _ => simp [linkedWF] at h

/-- **Under `linkedWF`, no instance-driven wire is written.** -/
theorem instOuts_not_written {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)} :
    ∀ (body : List Stmt), linkedWF C body = true →
      ∀ w, w ∈ bodyInstOuts C body → w ∉ Sparkle.IR.Reorder.writesOf body
  | [], _, w, hw => by
    have h' : w ∈ ([] : List String) := hw
    cases h'
  | st :: rest, h, w, hw => by
    have hw' : w ∈ stmtInstOuts C st ++ bodyInstOuts C rest := hw
    cases st with
    | assign l r =>
      simp only [linkedWF, Bool.and_eq_true] at h
      obtain ⟨⟨h1, -⟩, hrest⟩ := h
      have hl : l ∉ bodyInstOuts C rest := by simpa using h1
      have hW : Sparkle.IR.Reorder.writesOf (Stmt.assign l r :: rest) =
          l :: Sparkle.IR.Reorder.writesOf rest := by
        simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
      rw [hW]
      rcases List.mem_append.mp hw' with h0 | h0
      · have h0' : w ∈ ([] : List String) := h0
        cases h0'
      · intro hm
        rcases List.mem_cons.mp hm with e | hm'
        · exact hl (by rw [← e]; exact h0)
        · exact instOuts_not_written (C := C) rest hrest w h0 hm'
    | inst mn i conns =>
      have hW : Sparkle.IR.Reorder.writesOf (Stmt.inst mn i conns :: rest) =
          Sparkle.IR.Reorder.writesOf rest := by
        simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
      rw [hW]
      cases hc : C mn with
      | none => simp [linkedWF, hc] at h
      | some cw =>
        obtain ⟨child, cwe⟩ := cw
        simp only [linkedWF, hc, Bool.and_eq_true] at h
        obtain ⟨⟨⟨hall, -⟩, -⟩, hrest⟩ := h
        rcases List.mem_append.mp hw' with h0 | h0
        · unfold Tools.ShippingHierOpen.stmtInstOuts at h0
          simp only [hc] at h0
          have h2 := List.all_eq_true.mp hall w h0
          have hnl : w ∉ linkedWrites C rest := by simpa using h2
          exact fun hm => hnl (writes_sub_linked (C := C) rest hrest w hm)
        · exact instOuts_not_written (C := C) rest hrest w h0
    | register o c rk inp iv =>
      have hrest : linkedWF C rest = true := by
        simp only [linkedWF] at h
        exact h
      have hW : Sparkle.IR.Reorder.writesOf (Stmt.register o c rk inp iv :: rest) =
          Sparkle.IR.Reorder.writesOf rest := by
        simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]
      rw [hW]
      rcases List.mem_append.mp hw' with h0 | h0
      · have h0' : w ∈ ([] : List String) := h0
        cases h0'
      · exact instOuts_not_written (C := C) rest hrest w h0
    | _ => simp [linkedWF] at h

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_linkedWF` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_linkedWF` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_linkedWF_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingHierOpen.linkedWF (childMap D.modules) b.body = true := by
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, hw9, -⟩ := ran0
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
  obtain ⟨-, -, -, -, -, -, hlink, -⟩ := wired
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
  rw [hbody', ← Tools.ShippingMachineLinked.linkedOk_eq]
  exact hlink

set_option maxHeartbeats 4000000 in
/-- **The full entry's body is linked-well-formed over the core run's
design**, for a machine with calls. -/

theorem core_linkedWF {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierOpen.linkedWF (childMap D.modules) b.body = true :=
  core_linkedWF_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

/-- `core_instOuts_not_assigned` over `MachineRan` (round par/g-1): the statement and the proof of
`core_instOuts_not_assigned` (`Tools/ShippingLinkedFresh.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_instOuts_not_assigned_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    ∀ x, x ∈ bodyInstOuts (childMap D.modules) b.body →
      x ∉ Sparkle.IR.Reorder.writesOf b.body :=
  instOuts_not_written b.body
    (core_linkedWF_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran)

/-- **No assignment of the full entry's module targets an instance-driven
wire** — the assignment half of `outsExtracted`'s "not driven". -/
theorem core_instOuts_not_assigned {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ x, x ∈ bodyInstOuts (childMap D.modules) b.body →
      x ∉ Sparkle.IR.Reorder.writesOf b.body :=
  instOuts_not_written b.body
    (core_linkedWF d ok hbody hC hslots hdomB hins outTy hnomem hB hcore hpost entry closes)

end Tools.ShippingLinkedFresh
