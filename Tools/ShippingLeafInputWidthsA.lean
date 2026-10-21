import Tools.ShippingLeafInputWidths
import Tools.ShippingCallWidthsChildRealA
import Tools.ShippingChildRunA
-- BUILT (unit L8, par/u-l8): l8a exit 1 (missing opens), l8b exit 0, audit l8c exit 0 (no RefLaws in closure). See REPORT-L8.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Law witness `O : RefLawsAOps MkRefd mref cref`.

/-! # Unit L8: `leaf_sat_design_closed5A` — the first leaf head on the NEW boundary

`Tools.ShippingLeafInputWidths.leaf_sat_design_closed5` with `hbnd : ChildBnd mref cref w` (an old
`RefLaws` witness) replaced by `(O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
(hw : JQ O.quiet 0 w)` — no `cv w = {}`: the entry clears the child cache itself.

Where the old chain consumed `hbnd`: only in `machine_run_of_core` (-> `core_reads_inv L`,
`InvW`/`DepthPos` of the machine-synthesis start world) followed by `synthesizeMachineCertified_runs`
(needs `InvW`), in `leaf_run_typedIn_bnd`, `leaf_names`; everything else passes it along
(`leaf_entry_*_bnd`, `ShippingGuardsLeaf.leaf_entry_*`, `ShippingLeafFive.leaf_sat_design_closed`,
`leaf_input_widths`). Here the one use is `leaf_core_factsA` (`machine_run_of_coreA` +
`synthesizeMachineCertified_leaf_runs`: a leaf has `insts = []`, the closing of calls is not reached,
so NO `BodyStepC`/`htr`/`RefLawsATele` is needed). The rest are copies of the old proofs with the
binder changed (`...A` names). `MachineCloses` (old, every world / logger) stays a premise as before;
`MachineDefines`, `LeafKid`, `soundL` and the data conditions are unchanged.

SCOPE: a leaf state machine's design-level statement under the new boundary; not runtime fit; the
start premise `JQ O.quiet 0 w` is a run hypothesis (command -> entry link not formalised). -/
namespace Tools.ShippingLeafInputWidthsA

section Facts
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildInv
open Sparkle.IR.AST

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The one consumer of the start world**: a returning run of the core entry from a `JQ O.quiet 0`
world, for a leaf shape whose machine synthesis does not fall back (`MachineCloses`), contains a
returning machine-synthesis run, whence the closing of the transition. -/
theorem leaf_core_factsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hno : shape.insts = []) :
    ∃ (tenv : Lean.Environment) (b : Bool) (t t' : _) (d₀ : Sparkle.IR.AST.Design),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀ := by
  obtain ⟨tenv, b, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hr entry hw (Or.inl rfl)
  have hne := closes (profLogIO b) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
  exact ⟨tenv, b, t, t', d₀, run, hcl, hMeq, hDeq⟩

end Facts

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
theorem leaf_run_typedInA {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
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
  obtain ⟨_, _, t, t', d₀, run, hcl, hMeq, hDeq⟩ :=
    leaf_core_factsA O hA hw hcore entry closesM hno
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
theorem leaf_entry_rawA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
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
    leaf_run_typedInA (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy O hA hw hr K.entry (K.closes mctx cctx) K.outName K.outScalar
  have hna' : m0.body.all Sparkle.IR.RegDedup.isAssign = false := hna K.slots
  have htext := Tools.ShippingLeafEntry.text_post_reg hpost hT hna'
  exact ⟨hs, htext, m0, hpost, hna'⟩

/-- `Tools.ShippingLeafEntry.leaf_entry_textChecks` with `ChildBnd` in place
of `InvW`: the three check premises of `machine_ships_wired` at the emitter's
own width map of the shipped module. `hmergeReg` and `hoptPrint` are NOT
derived. -/
theorem leaf_entry_textChecksA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
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
  obtain ⟨-, htext, m0, hpost, hna⟩ := leaf_entry_rawA K O hA hw hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact Tools.ShippingLeafEntry.simpleBody_false_of hna
    · exact Tools.ShippingLeafEntry.simpleBody_false_of (hmergeReg m0 e hna)
  obtain ⟨h2, h3⟩ := Tools.ShippingLeafEntry.text_shipped_of_print htext hoptPrint
  exact ⟨hsB, h2, h3⟩

/-- `Tools.ShippingLeafEntry.leaf_entry_shipped_seq` with `ChildBnd` in place
of `InvW`. -/
theorem leaf_entry_shipped_seqA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false) :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  obtain ⟨hs, -, m0, hpost, hna⟩ := leaf_entry_rawA K O hA hw hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact Tools.ShippingLeafEntry.simpleBody_false_of hna
    · exact Tools.ShippingLeafEntry.simpleBody_false_of (hmergeReg m0 e hna)
  exact Tools.ShippingLeafEntry.checkedOptimize_seqBody hsB hs

/-- The full entry's module of a leaf register machine is not of simple
shape and is an assign + register module. -/
theorem leaf_entry_seqBranchA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    Sparkle.IR.OptCheck.simpleBody b = false ∧
      b.body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  obtain ⟨hs, -, m0, hpost, hna⟩ := leaf_entry_rawA K O hA hw hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact Tools.ShippingLeafEntry.simpleBody_false_of hna
    · exact Tools.ShippingLeafEntry.simpleBody_false_of (Tools.ShippingGuardsLeaf.mergeReg_closed b m0 e hna)
  exact ⟨hsB, hs⟩

/-- `hoptPrint` of the leaf entry, from the run. -/
theorem leaf_entry_optPrintA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true := by
  obtain ⟨hsB, hs⟩ := leaf_entry_seqBranchA K O hA hw hr
  exact Tools.ShippingGuardsLeaf.checkedOptimize_instFree_print hsB hs

/-- `leaf_entry_textChecksA` without
`hmergeReg` and `hoptPrint`: the three check premises of
`machine_ships_wired` at the emitter's own width map of the shipped module,
from the run. -/
theorem leaf_entry_textChecks_closedA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
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
  leaf_entry_textChecksA K O hA hw hr (Tools.ShippingGuardsLeaf.mergeReg_closed b)
    (leaf_entry_optPrintA K O hA hw hr)

/-- `leaf_entry_shipped_seqA` without
`hmergeReg`. -/
theorem leaf_entry_shipped_seq_closedA {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true :=
  leaf_entry_shipped_seqA K O hA hw hr (Tools.ShippingGuardsLeaf.mergeReg_closed b)


end Entry

section Run
open Sparkle.IR.AST
open Sparkle.IR.RegDedup (declWidth)
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
theorem leaf_namesA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w') :
    (b.wires.map (·.name)).Nodup ∧
      (∀ p ∈ b.wires ++ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) ∧
      (∀ p ∈ b.wires, p.name ≠ "clk" ∧ p.name ≠ "rst") := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  obtain ⟨_, _, t, t', d₀, run, hcl, hMeq, hDeq⟩ :=
    leaf_core_factsA O hA hw hcore K.entry (K.closes mctx cctx) K.leaf
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
theorem leaf_input_widthsA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {d : MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w)
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
  obtain ⟨hnd, hsWI, hwc⟩ := leaf_namesA K O hA hw hr
  obtain ⟨-, -, -, -, hPI, -, -⟩ :=
    leaf_run_typedInA (nDecl := d.nIn) d K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy O hA hw hr K.entry (K.closes mctx cctx) K.outName K.outScalar
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
  refine Tools.ShippingLeafInputWidths.declWidth_le_weS_input hoi' hoo' hsub (by rw [hdw]; exact hnd) ?_ ?_ ?_
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
      | mk pn pty => cases pty <;> simp [Tools.ShippingLeafInputWidths.tyW]


end Run

section Five
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingSeqSVSoundness
open Tools.ShippingSatAssemblyS (slotInit)
open Tools.ShippingLeafSat
open Sparkle.IR.RegDedup (declWidth)

theorem leaf_sat_design_closedA {declName : Name} (d : MachineData)
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
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
        (
          (∀ x ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name),
            declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) x ≤
              Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
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
  obtain ⟨raw, D, hpost, ids, cache, regs, hW, H⟩ :=
    Tools.ShippingLeafSatDesign.leaf_sat_design d @soundL hnoI hsl hSS houtTy hlen hinitW hr entry closes
  have h1 := leaf_entry_shipped_seq_closedA K O hA hw hr
  obtain ⟨h2, h3, h4⟩ := leaf_entry_textChecks_closedA K O hA hw hr
  exact ⟨raw, D, hpost, ids, cache, regs, hW, H h1 h2 h3 h4⟩


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
theorem leaf_sat_design_closed5A {declName : Name} (d : MachineData)
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
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hw : Tools.ShippingChildVCA.JQ O.quiet 0 w) :
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
    leaf_sat_design_closedA d @soundL hnoI hsl hSS houtTy hlen hinitW hr
      entry closes K O hA hw
  exact ⟨raw, D, hpost, ids, cache, regs, ⟨lets, hW⟩,
    H (leaf_input_widthsA K O hA hw hr hpost hW)⟩


end Five

end Tools.ShippingLeafInputWidthsA
