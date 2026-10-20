import Tools.ShippingLeafEntryBnd
import Tools.ShippingMergeKeepsBridge

/-! # `hmergeReg` discharged for a leaf register machine (round par/a-30)

`Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd` and
`leaf_entry_ships_bnd` take

    hmergeReg : ∀ m0, b = mergeChecked m0 → m0.body.all isAssign = false →
      b.body.all isAssign = false

It is not a theorem about all modules (`docs/parallel/A-leaf-entry-2.md` §1).
With `Tools.ShippingMergeKeeps.mergeChecked_keeps` it follows for a module
with `LastNonAssign`. This file is the SUPPLY side:

* `closeMachine_lastNonAssign` — the closed machine's body is

      B ++ nextAssigns ++ registers ++ outAssigns

  (`Sparkle/IR/Machine.lean` 112–114). With a slot, the first register
  `register p.name …` is followed by registers and by the output
  assignments only; an output's name is not an allocated name
  (`outNameOk_facts`), a slot port's name is (`names`, `inWires`). So no
  assignment AFTER the register drives its name. Nothing is asked about `B`:
  the weaker hypothesis (`LastNonAssign`, not distinct names) is what makes
  the built facts enough — "no statement of `B` drives a slot port" is NOT
  among the facts `closedTransition_of_run` returns.
* `leaf_run_lastNonAssign` — the full entry's module is `m0` or
  `mergeChecked m0` with `LastNonAssign m0.body`. Its proof is the PREFIX of
  `Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd` (the run taken apart, up
  to `M = closeMachine lay t'` and the cleanup's body equation) — REPEATED:
  that theorem's statement hides `M`, and the file may not be edited. The
  lines are extracted, not retyped; `hon` / `hoty` are not needed.
* `leaf_nonAssign_bnd`, `leaf_mergeReg` — `b.body.all isAssign = false`, and
  `hmergeReg` in its exact form.
* `leaf_entry_textChecks_bndR`, `leaf_entry_shipped_seq_bndR`,
  `leaf_entry_ships_bndR` — the entry theorems with `hmergeReg` discharged;
  `hoptPrint` is the one underived hypothesis left.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMergeKeepsLeaf

section Close
open Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.NameHints (Allocated)
open Sparkle.IR.RegDedup (definedNode isAssign)
open Tools.ShippingMergeKeeps (LastNonAssign)

/-- **The closed machine has a register no later assignment drives.** -/
theorem closeMachine_lastNonAssign {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inWires : ∀ p ∈ t.inputs, p ∈ t.wires)
    (slots : Tools.ShippingMachineClose.Zip₂
      (Tools.ShippingMachineClose.SlotOk (Tools.ShippingEntrySoundness.weOf t))
      (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (hsl : lay.slots ≠ []) :
    LastNonAssign (closeMachine lay t).body := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  generalize hps : t.inputs.drop (t.inputs.length - lay.slots.length) = ps at slots
  have hMb : (closeMachine lay t).body =
      B ++ nextAssigns w ps lay.slots ++ registers lay.resetKind ps lay.slots ++
        outAssigns w lay.outs := by
    simp [closeMachine, hpw, hdrop, hps]
  have psIn : ∀ p ∈ ps, p ∈ t.inputs := fun p hp => List.mem_of_mem_drop (hps ▸ hp)
  have hlen := slots.length_eq
  obtain ⟨f, fs, hfs⟩ : ∃ f fs, lay.slots = f :: fs := by
    cases h : lay.slots with
    | nil => exact absurd h hsl
    | cons f fs => exact ⟨f, fs, rfl⟩
  obtain ⟨p, ps', hps'⟩ : ∃ p ps', ps = p :: ps' := by
    cases h : ps with
    | nil =>
      rw [h, hfs] at hlen
      simp at hlen
    | cons p ps' => exact ⟨p, ps', rfl⟩
  have hreg : registers lay.resetKind ps lay.slots =
      Stmt.register p.name "clk" ("rst", lay.resetKind) (.ref (nextName p.name))
        (Int.ofNat f.init) :: registers lay.resetKind ps' fs := by
    rw [hps', hfs]
    first
      | done
      | rfl
  have hpa : Allocated p.name := by
    have hp : p ∈ ps := by
      rw [hps']
      exact List.mem_cons_self ..
    exact names p (inWires p (psIn p hp))
  refine ⟨B ++ nextAssigns w ps lay.slots,
    Stmt.register p.name "clk" ("rst", lay.resetKind) (.ref (nextName p.name))
      (Int.ofNat f.init),
    registers lay.resetKind ps' fs ++ outAssigns w lay.outs, ?_, rfl, ?_⟩
  · rw [hMb, hreg]
    first
      | done
      | simp [List.append_assoc]
  · intro l r hm hdn
    have hl : p.name = l := Option.some.inj hdn
    rcases List.mem_append.mp hm with h1 | h1
    · obtain ⟨k, q, g, -, -, he⟩ :=
        Tools.ShippingMachineCleanup.registers_mem lay.resetKind ps' fs _ h1
      cases he
    · have h2 : Stmt.assign l r ∈
          lay.outs.map (fun o => Stmt.assign o.name (fieldRhs w o.lo o.width)) := h1
      obtain ⟨o, ho, he⟩ := List.mem_map.mp h2
      have hlo : o.name = l := (Stmt.assign.inj he).1
      have hno := (Tools.ShippingMachineClose.outNameOk_facts (outsOk o ho).2).1
      apply hno
      rw [hlo, ← hl]
      exact hpa

end Close

section Typed
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChecksDerived (ff_absurd)
open Tools.ShippingChecksDepth (and_true_intro)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **A leaf machine's returned module is a module with `LastNonAssign`, or
its checked merge**, over every run of the full entry that starts in a world
with the runtime laws. The module is the `m0` of
`Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd` (the cleaned
`closeMachine lay t'`), by the same steps. -/
theorem leaf_run_lastNonAssign {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hbnd : ChildBnd mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
      (d.shape.layout.slots ≠ [] → Tools.ShippingMergeKeeps.LastNonAssign m0.body) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c d.shape := machineClosesAt_of_closes closesM
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hbnd
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hSS hdomB run hcl
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
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
  -- the raw module's wiring: the core entry's theorem at this run
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeCombinationalCore_machine_sound hcore entry closesM d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, rlen, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, hzw, -, hzo⟩, -, hregs, -, -, -, -, -, hseq⟩ := hclean hno outTy
  have hM' : M = closeMachine d.shape.layout t' := hMeq
  refine ⟨Sparkle.IR.ZeroWidth.dropZeroWidthModule M, hpost, ?_⟩
  intro hsl
  rw [hzb, hM']
  exact closeMachine_lastNonAssign hbodyc namesc inWc slotsc outsOk hsl

end Typed

section Entry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)

/-- **The full entry's module of a leaf register machine is not assignments
only** — whether or not the checked merge was kept. No hypothesis about the
merge. -/
theorem leaf_nonAssign_bnd {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    b.body.all Sparkle.IR.RegDedup.isAssign = false := by
  obtain ⟨m0, hpost, hL⟩ :=
    leaf_run_lastNonAssign (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy hbnd hr K.entry (K.closes mctx cctx)
  have hL' := hL K.slots
  rcases hpost with e | e
  · rw [e]
    exact hL'.nonAssign
  · rw [e]
    exact Tools.ShippingMergeKeeps.mergeChecked_keeps hL'

/-- **`hmergeReg`, in the exact form `leaf_entry_textChecks_bnd` asks, for a
leaf register machine.** -/
theorem leaf_mergeReg {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false :=
  fun _ _ _ => leaf_nonAssign_bnd K hbnd hr

/-- `Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd` with `hmergeReg`
discharged. `hoptPrint` is NOT derived. -/
theorem leaf_entry_textChecks_bndR {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
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
  Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd K hbnd hr (leaf_mergeReg K hbnd hr)
    hoptPrint

/-- `Tools.ShippingLeafEntryBnd.leaf_entry_shipped_seq_bnd` with `hmergeReg`
discharged: no underived hypothesis. -/
theorem leaf_entry_shipped_seq_bndR {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true :=
  Tools.ShippingLeafEntryBnd.leaf_entry_shipped_seq_bnd K hbnd hr (leaf_mergeReg K hbnd hr)

/-- **A leaf register machine at the full entry, to the emitted Verilog at
the emitter's own width map — with `hmergeReg` discharged.**
`Tools.ShippingLeafEntryBnd.leaf_entry_ships_bnd` without its `hmergeReg`;
the one underived hypothesis left is `hoptPrint`. -/
theorem leaf_entry_ships_bndR {declName : Name} (d : MachineData)
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
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
        (checkedOptimize b) (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) dom src :=
  Tools.ShippingLeafEntry.leaf_entry_ships_of
    (Tools.ShippingMachineShipsW.machine_ships_wired d @soundL K.leaf K.slots K.ss K.outTy hr
      K.entry (K.closes mctx cctx))
    (leaf_entry_textChecks_bndR K hbnd hr hoptPrint)

end Entry

end Tools.ShippingMergeKeepsLeaf
