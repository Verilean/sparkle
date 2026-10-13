import Tools.ShippingLeafEntryBnd

/-! # The two guards of the leaf register entry, as theorems (candidate branch `fix/opt-print-guard`)

On poc `cfbab0db` the two binders `hmergeReg` and `hoptPrint` of
`Tools.ShippingLeafEntryBnd.leaf_entry_ships_bnd` are NOT theorems of the
compiler (`docs/parallel/A-leaf-entry-2.md`; `mergeCex`, `optCex` of
`Tests/Compiler/LeafEntryCexProbe.lean`, confirmed by evaluation). This
branch adds two guards to `Sparkle/IR/RefineCheck.lean`:

* `checkedOptimize`, instance-free assign + register branch:
  `if refineCheck m o && printOk o then o else m`;
* `mergeChecked`, last branch (reached only when the input body is not
  assignment-only): the innermost conjunct `!(r.body.all isAssign)`.

Each falls back to the INPUT module; neither rejects.

With them the two facts are theorems:

* `checkedOptimize_instFree_print`: in the assign + register branch the
  shipped module is the input module or passes the print guard;
* `mergeChecked_keeps_reg`: the checked merge of a body that is not
  assignment-only is not assignment-only.

and the two binders are discharged for every leaf register entry:

* `mergeReg_closed` — `hmergeReg`, for every module `b`;
* `leaf_entry_optPrint` — `hoptPrint`, from the run (`leaf_entry_raw_bnd`);
* `leaf_entry_textChecks_closed`, `leaf_entry_shipped_seq_closed`,
  `leaf_entry_ships_closed`: the theorems of `Tools/ShippingLeafEntryBnd.lean`
  without the two binders.

SCOPE: one module (`MachineShips` at the emitter's own width map), leaf
register machines; the run, the reflection and the runtime boundary
(`ChildBnd`) stay premises.

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingGuardsLeaf

/-- `(!a) = true` is `a = false`. -/
theorem bnot_true_false {a : Bool} (h : (!a) = true) : a = false := by
  cases a
  · rfl
  · simp at h

/-- **The print guard of the optimizer, instance-free assign + register
branch**: the shipped module is the input module or passes the print
guard. -/
theorem checkedOptimize_instFree_print {m : Sparkle.IR.AST.Module}
    (hs : Sparkle.IR.OptCheck.simpleBody m = false)
    (hok : m.body.all Sparkle.IR.OptCheck.seqStmtOk = true) :
    Sparkle.IR.OptCheck.checkedOptimize m = m ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize m) = true := by
  unfold Sparkle.IR.OptCheck.checkedOptimize
  dsimp only
  simp only [hs, Bool.false_eq_true, if_false, hok, if_true]
  split
  · rename_i hc; exact Or.inr (Sparkle.IR.RefineCheck.and_right_true hc)
  · exact Or.inl rfl

/-- **The checked merge keeps a non-assignment statement**: on a body that
is not assignment-only, the kept module's body is not assignment-only. -/
theorem mergeChecked_keeps_reg {m : Sparkle.IR.AST.Module}
    (h : m.body.all Sparkle.IR.RegDedup.isAssign = false) :
    (Sparkle.IR.RefineCheck.mergeChecked m).body.all Sparkle.IR.RegDedup.isAssign = false := by
  unfold Sparkle.IR.RefineCheck.mergeChecked
  dsimp only
  split
  · rename_i hall
    exact absurd (hall.symm.trans h) (by decide)
  · split
    · rename_i _ hc
      exact bnot_true_false (Sparkle.IR.RefineCheck.and_right_true
        (Sparkle.IR.RefineCheck.and_right_true (Sparkle.IR.RefineCheck.and_right_true hc)))
    · exact h

/-- `hmergeReg` of the leaf entry, for every module. -/
theorem mergeReg_closed (b : Sparkle.IR.AST.Module) :
    ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false := by
  intro m0 e h
  rw [e]
  exact mergeChecked_keeps_reg h

section Entry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)

/-- The full entry's module of a leaf register machine is not of simple
shape and is an assign + register module. -/
theorem leaf_entry_seqBranch {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    Sparkle.IR.OptCheck.simpleBody b = false ∧
      b.body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  obtain ⟨hs, -, m0, hpost, hna⟩ := Tools.ShippingLeafEntryBnd.leaf_entry_raw_bnd K hbnd hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact Tools.ShippingLeafEntry.simpleBody_false_of hna
    · exact Tools.ShippingLeafEntry.simpleBody_false_of (mergeReg_closed b m0 e hna)
  exact ⟨hsB, hs⟩

/-- `hoptPrint` of the leaf entry, from the run. -/
theorem leaf_entry_optPrint {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true := by
  obtain ⟨hsB, hs⟩ := leaf_entry_seqBranch K hbnd hr
  exact checkedOptimize_instFree_print hsB hs

/-- `Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd` without
`hmergeReg` and `hoptPrint`: the three check premises of
`machine_ships_wired` at the emitter's own width map of the shipped module,
from the run. -/
theorem leaf_entry_textChecks_closed {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    Sparkle.IR.OptCheck.simpleBody b = false ∧
      Tools.SVParser.EmitSem.seqCheck
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
        (Tools.SVParser.EmitSem.weOf
          (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)))
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      ((Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
        fun n => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) n ==
          Tools.SVParser.EmitSem.weOf
            (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n) = true :=
  Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd K hbnd hr (mergeReg_closed b)
    (leaf_entry_optPrint K hbnd hr)

/-- `Tools.ShippingLeafEntryBnd.leaf_entry_shipped_seq_bnd` without
`hmergeReg`. -/
theorem leaf_entry_shipped_seq_closed {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true :=
  Tools.ShippingLeafEntryBnd.leaf_entry_shipped_seq_bnd K hbnd hr (mergeReg_closed b)

/-- **A leaf register machine at the full entry, to the emitted Verilog at
the emitter's own width map, from the run, the reflection and `ChildBnd`
only.** `Tools.ShippingLeafEntryBnd.leaf_entry_ships_bnd` with `hmergeReg`
and `hoptPrint` discharged by the two guards. -/
theorem leaf_entry_ships_closed {declName : Name} (d : MachineData)
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
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w') :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
        (checkedOptimize b) (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) dom src :=
  Tools.ShippingLeafEntryBnd.leaf_entry_ships_bnd d @soundL K hbnd hr (mergeReg_closed b)
    (leaf_entry_optPrint K hbnd hr)

end Entry

end Tools.ShippingGuardsLeaf
