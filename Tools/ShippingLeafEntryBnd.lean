import Tools.ShippingLeafEntry

/-! # A leaf register machine as an entry, from `ChildBnd` at the start world (G1, round par/a-24)

`Tools.ShippingLeafTyped.leaf_run_typedIn` (`Tools/ShippingLeafTyped.lean`
354–588) asks `hw : InvW mref cref w` of the run's start world and uses it
ONCE, as `ChildBnd.of_invW mctx cctx hw` — the argument of
`machine_run_of_core`. `InvW` is not an allowed premise of the final goal;
`ChildBnd` is. The theorems of `Tools/ShippingLeafEntry.lean` inherit the
`InvW`.

This file is the GENERALISATION, and the old statements re-derived from it:

* `leaf_run_typedIn_bnd`: `leaf_run_typedIn` with `hbnd : ChildBnd mref cref w`
  in place of `hw`. Its proof is the old proof with that one argument
  changed. The old proof is NOT factored (the whole of it comes after the
  `obtain` on `machine_run_of_core … (ChildBnd.of_invW mctx cctx hw)`), and
  the old file may not be edited, so the body is REPEATED here: 215 lines
  (old 374–588), produced by extraction from the old file, with exactly these
  differences — the theorem's name; the hypothesis; the argument of
  `machine_run_of_core`; `PortsIn` written with its namespace (three
  occurrences; this file is in another namespace).
* `leaf_run_typedIn_again`: the OLD statement, from `leaf_run_typedIn_bnd`
  and `ChildBnd.of_invW` — one line. (Once built, the old proof body is
  redundant; replacing it by this line is an edit of an existing file — not
  made here.)
* `leaf_entry_raw_bnd`, `leaf_entry_textChecks_bnd`,
  `leaf_entry_shipped_seq_bnd`, `leaf_entry_ships_bnd`: the theorems of
  `Tools/ShippingLeafEntry.lean` with `ChildBnd` in place of `InvW`. Their
  proofs are the old ones (6, 8, 7 and 4 lines) over `leaf_run_typedIn_bnd`;
  the pure lemmas (`text_post_reg`, `simpleBody_false_of`,
  `text_shipped_of_print`, `checkedOptimize_seqBody`, `leaf_entry_ships_of`)
  are used as built.
* `leaf_entry_raw_again`: the old `leaf_entry_raw`, from `leaf_entry_raw_bnd`.

`hmergeReg` and `hoptPrint` are unchanged: see
`docs/parallel/A-leaf-entry-2.md` (the first is FALSE as a statement about
`mergeChecked` on all modules, the second is FALSE for the optimizer — both
by reading, with probe modules in `Tests/Compiler/LeafEntryCexProbe.lean`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafEntryBnd

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
/-- **A leaf machine's returned module is a typed module or its checked
merge**, over every run of the full entry that starts in a world with the
runtime laws (`ChildBnd`); its ports and statement kinds are the typed
module's either way. `Tools.ShippingLeafTyped.leaf_run_typedIn` with
`ChildBnd` in place of `InvW`. -/
theorem leaf_run_typedIn_bnd {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
      Tools.ShippingLeafTyped.PortsIn b ∧ b.body.all seqStmtOk = true ∧
      (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false) := by
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
  -- with a slot, the core module has a register: the cleaned body is not
  -- assignments only (the steps of `leaf_run_masked`, copied)
  have hnAZ : d.shape.layout.slots ≠ [] →
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all Sparkle.IR.RegDedup.isAssign =
        false := by
    intro hsl
    obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
      cases hs : d.shape.layout.slots with
      | nil => exact absurd hs hsl
      | cons f _ => exact ⟨f, rfl⟩
    obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
      cases hrs : regs with
      | nil =>
        have hreg0 : regs.length = 0 := by simp [hrs]
        have hsb : d.slotBs.length = d.ss.length := by
          simp only [MachineData.slotBs, List.length_take, List.length_drop]
          omega
        have : d.shape.layout.slots.length = 0 := by omega
        rw [List.length_eq_zero_iff] at this; exact absurd this hsl
      | cons r _ => exact ⟨r, rfl⟩
    obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
    have hnA : M.body.all Sparkle.IR.RegDedup.isAssign = false := by
      apply List.all_eq_false.mpr
      exact ⟨_, hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
    rw [hzb]
    exact hnA
  obtain ⟨-, -, hwCM, hiCM, hoCM, hkCM, haCM, hrCM⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hM' : M = closeMachine d.shape.layout t' := hMeq
  -- the cleaned module against the closed machine
  have hZb : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body =
      (closeMachine d.shape.layout t').body := by
    rw [hzb, hM']
  have hZi : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs =
      (closeMachine d.shape.layout t').inputs := by
    rw [Tools.ShippingOutsExtractedParts.dropZW_inputs M, hM']
  have hZo : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := by
    rw [hzo, hM']
    exact hoCM
  have hweZ : Tools.ShippingEntrySoundness.weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) =
      Tools.ShippingEntrySoundness.weOf (closeMachine d.shape.layout t') :=
    hzw.trans (congrArg Tools.ShippingEntrySoundness.weOf hM')
  have hwsub : ∀ p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).wires,
      p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    have h1 := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hM'] at h1
    exact h1
  have outFacts : ∀ q ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs,
      ∃ o ∈ d.shape.layout.outs,
        q = ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port) := by
    intro q hq
    rw [hZo] at hq
    obtain ⟨o, ho, he⟩ := List.mem_map.mp hq
    exact ⟨o, ho, he.symm⟩
  have hseqZ : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all seqStmtOk = true := by
    rw [hzb]
    exact hseq
  have hT : Tools.ShippingTextTyped.TypedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
    refine
      { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_, kinds := ?_,
        asg := ?_, reg := ?_ }
    · -- the wire names are sanitize-stable
      intro p hp
      rcases hwCM p (hwsub p hp) with ha | ⟨y, hy, hpn⟩
      · exact Tools.ShippingNamesStable.sanitizeName_of_allocated ha
      · rw [hpn]
        exact Tools.ShippingNamesNext.sanitizeName_nextName hy
    · -- no wire has an output port's name
      intro q hq p hp heq
      obtain ⟨o, ho, hqo⟩ := outFacts q hq
      have hpo : p.name = o.name := heq.trans (congrArg Sparkle.IR.AST.Port.name hqo)
      obtain ⟨hna, -, hnn⟩ := Tools.ShippingMachineClose.outNameOk_facts (outsOk o ho).2
      rcases hwCM p (hwsub p hp) with ha | ⟨y, hy, hpn⟩
      · rw [hpo] at ha
        exact hna ha
      · exact hnn y (hpo.symm.trans hpn)
    · -- no input's sanitized name is an output port's name
      intro q hq p hp heq
      obtain ⟨o, ho, hqo⟩ := outFacts q hq
      have hqn : q.name = o.name := congrArg Sparkle.IR.AST.Port.name hqo
      rw [hqn] at heq
      have hok := (outsOk o ho).2
      simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      obtain ⟨hna, -, -⟩ := Tools.ShippingMachineClose.outNameOk_facts (outsOk o ho).2
      rw [hZi] at hp
      rcases hiCM p hp with ha | hc | hr
      · rw [Tools.ShippingNamesStable.sanitizeName_of_allocated ha] at heq
        rw [heq] at ha
        exact hna ha
      · rw [hc, Tools.ShippingNamesClk.sanitizeName_clk] at heq
        exact hok.2 heq.symm
      · rw [hr, Tools.ShippingNamesClk.sanitizeName_rst] at heq
        exact hok.1.2 heq.symm
    · -- the output port names are sanitize-stable
      intro q hq
      obtain ⟨o, ho, hqo⟩ := outFacts q hq
      rw [hqo]
      exact hon o ho
    · -- distinct output names
      rw [hZo, List.map_map]
      exact outsNodup
    · -- scalar output ports
      intro q hq
      obtain ⟨o, ho, hqo⟩ := outFacts q hq
      rw [hqo]
      exact Tools.ShippingTextTyped.scalarTy_spec (hoty o ho)
    · -- the statement kinds
      intro st hst
      rw [hZb] at hst
      rcases hkCM st hst with ⟨l, r, he⟩ | ⟨o, c', rk, i, iv, he⟩
      · subst he
        rfl
      · subst he
        rfl
    · -- the assignments
      intro l r hm
      rw [hZb] at hm
      obtain ⟨n, ht, hl⟩ := haCM l r hm
      refine ⟨n, ?_, ?_⟩
      · rw [hweZ]
        exact ht
      · rcases hl with hl | ⟨q, hq, h1, h2⟩
        · left
          rw [hweZ]
          exact hl
        · right
          have e : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs =
              (closeMachine d.shape.layout t').outputs := hZo.trans hoCM.symm
          refine ⟨q, ?_, h1, h2⟩
          rw [e]
          exact hq
    · -- the registers
      intro o c' rk i iv hm
      rw [hZb] at hm
      have ht := hrCM o c' rk i iv hm
      rw [hweZ]
      exact ht
  have hPZ : Tools.ShippingLeafTyped.PortsIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    Tools.ShippingLeafTyped.PortsIn.of_typedIn hT
  refine ⟨Sparkle.IR.ZeroWidth.dropZeroWidthModule M, hpost, hT, hseqZ, ?_, ?_, hnAZ⟩
  · rcases hpost with h | h
    · rw [h]
      exact hPZ
    · rw [h]
      exact hPZ.of_ports
        (Sparkle.IR.RefineCheck.mergeChecked_ports _).1
        (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.1
        (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2
  · rcases hpost with h | h
    · rw [h]
      exact hseqZ
    · rw [h]
      exact mergeChecked_seqOk hseqZ

/-- **The old statement, re-derived**: `leaf_run_typedIn` (with `InvW`) from
the generalisation. -/
theorem leaf_run_typedIn_again {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
      Tools.ShippingLeafTyped.PortsIn b ∧ b.body.all seqStmtOk = true ∧
      (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false) :=
  leaf_run_typedIn_bnd d ok hbody hC hdomB hno hSS outTy (ChildBnd.of_invW mctx cctx hw) hr
    entry closesM hon hoty

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

/-- `Tools.ShippingLeafEntry.leaf_entry_raw` with `ChildBnd` in place of
`InvW`: the full entry's module of a leaf register machine — its statement
kinds, conjuncts 2 and 3 of `textCheckI` at the module itself, and that it is
a module with a register or the checked merge of one. -/
theorem leaf_entry_raw_bnd {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    b.body.all Sparkle.IR.OptCheck.seqStmtOk = true ∧
      (Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
          (Tools.ShippingDesignSV.weS b) b.body = true ∧
        (Tools.ShippingSeqSVSoundness.seqNames b.body).all
          (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) =
            true) ∧
      ∃ m0 : Sparkle.IR.AST.Module,
        (b = m0 ∨ b = Sparkle.IR.RefineCheck.mergeChecked m0) ∧
          m0.body.all Sparkle.IR.RegDedup.isAssign = false := by
  obtain ⟨m0, hpost, hT, -, -, hs, hna⟩ :=
    leaf_run_typedIn_bnd (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy hbnd hr K.entry (K.closes mctx cctx) K.outName K.outScalar
  have hna' : m0.body.all Sparkle.IR.RegDedup.isAssign = false := hna K.slots
  have htext := Tools.ShippingLeafEntry.text_post_reg hpost hT hna'
  exact ⟨hs, htext, m0, hpost, hna'⟩

/-- **The old statement, re-derived**: `leaf_entry_raw` (with `InvW`). -/
theorem leaf_entry_raw_again {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : Tools.ShippingChildInv.InvW mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    b.body.all Sparkle.IR.OptCheck.seqStmtOk = true ∧
      (Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
          (Tools.ShippingDesignSV.weS b) b.body = true ∧
        (Tools.ShippingSeqSVSoundness.seqNames b.body).all
          (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) =
            true) ∧
      ∃ m0 : Sparkle.IR.AST.Module,
        (b = m0 ∨ b = Sparkle.IR.RefineCheck.mergeChecked m0) ∧
          m0.body.all Sparkle.IR.RegDedup.isAssign = false :=
  leaf_entry_raw_bnd K (Tools.ShippingChildInv.ChildBnd.of_invW mctx cctx hw) hr

/-- `Tools.ShippingLeafEntry.leaf_entry_textChecks` with `ChildBnd` in place
of `InvW`: the three check premises of `machine_ships_wired` at the emitter's
own width map of the shipped module. `hmergeReg` and `hoptPrint` are NOT
derived. -/
theorem leaf_entry_textChecks_bnd {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false)
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
            (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n) = true := by
  obtain ⟨-, htext, m0, hpost, hna⟩ := leaf_entry_raw_bnd K hbnd hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact Tools.ShippingLeafEntry.simpleBody_false_of hna
    · exact Tools.ShippingLeafEntry.simpleBody_false_of (hmergeReg m0 e hna)
  obtain ⟨h2, h3⟩ := Tools.ShippingLeafEntry.text_shipped_of_print htext hoptPrint
  exact ⟨hsB, h2, h3⟩

/-- `Tools.ShippingLeafEntry.leaf_entry_shipped_seq` with `ChildBnd` in place
of `InvW`. -/
theorem leaf_entry_shipped_seq_bnd {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false) :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  obtain ⟨hs, -, m0, hpost, hna⟩ := leaf_entry_raw_bnd K hbnd hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact Tools.ShippingLeafEntry.simpleBody_false_of hna
    · exact Tools.ShippingLeafEntry.simpleBody_false_of (hmergeReg m0 e hna)
  exact Tools.ShippingLeafEntry.checkedOptimize_seqBody hsB hs

/-- **A leaf register machine at the full entry, to the emitted Verilog at
the emitter's own width map — `machine_ships_wired` without its three check
premises, from `ChildBnd` at the start world.**
`Tools.ShippingLeafEntry.leaf_entry_ships` with `ChildBnd` in place of
`InvW`. The two underived hypotheses `hmergeReg`, `hoptPrint` stay. -/
theorem leaf_entry_ships_bnd {declName : Name} (d : MachineData)
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
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false)
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
    (leaf_entry_textChecks_bnd K hbnd hr hmergeReg hoptPrint)

end Entry

end Tools.ShippingLeafEntryBnd
