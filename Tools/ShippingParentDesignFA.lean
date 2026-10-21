import Tools.ShippingParentRunFactsA
import Tools.ShippingParentPortsA
import Tools.ShippingParentDesignA
import Tools.ShippingParentTailsA
import Tools.ShippingLeafPorts
import Tools.ShippingLeafTyped
import Tools.ShippingCoreClk
import Tools.ShippingPortsMatchRaw
import Tools.ShippingPortsMatchShipped
import Tools.ShippingTextShipped
import Tools.ShippingSeqChildIfaceA
-- BUILT (unit SR3f, par/u-sr3f): fa2 exit 0 (fa1 exit 1: unqualified mergeChecked_seqOk).
-- SCOPE (binding): the `designCheck` success condition of the shipped module of a machine with calls, a register and
-- `instFields ≠ []`, on the NEW boundary (`MachineRanA O`, `RealChildA O` children = a HISTORY of past synthesis results).
-- NOT a parent semantic-equivalence head; not runtime fit. No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR3f: `designCheck` of a parent with `instFields ≠ []` over `MachineRanA O`

`designCheck C n o = textCheckI C o && kidsPass C (designCheck C (n-1)) o.body` (`Tools.ShippingDesignSV.designCheck`);
`textCheckI` is the conjunction of: `seqStmtOkI`, `seqCheck`, the `declWidth = weS` names check, `linkedWF`,
`instNames.Nodup`, `noSelfRead`, **`portsMatchB`**, and "every instance resolves". The old chain
(`Tools.ShippingTextShipped.core_designCheck_run_ran`) splits it as: the run facts (`RunFacts`: gate, `linkedWF`, names,
self-read, outputs, reset, widths), `TypedIn` (the text checks), **`portsMatchB`** of the shipped module, and
**`kidsPass (kidCheck …)`**.  The first two are SR3e's `core_runFacts_ranA` and PH's `core_closed_typedIn_ranA`.
This file supplies the other two for `instFields ≠ []` on `MachineRanA O` by mechanical ports (generator
`.cluster/logs/gen_sr3f.py`: verbatim proof text, head and run preamble replaced) of

* the child side (leaf register machine, `RealChildA O`): `leaf_run_portsA`/`leaf_real_portsA` (`LeafPorts`:
  `inWidths`, `clk`), `leaf_run_typedInA`/`leaf_real_typedInA`/`leaf_real_portsInA`, `leaf_real_kidK_regA`;
* the parent side: `core_callConns_ranA`, `core_portsMatch_raw_ranA` (the raw module's `portsMatchB`), `core_clk_ranA`;
* assembled `core_designCheck_ranFA` (the old `core_designCheck_run_ran` on the new boundary, with `portsMatchB` and
  `kidsPass` DERIVED from the per-child facts instead of taken as premises). -/

namespace Tools.ShippingParentDesignFA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIfaceA Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped Tools.ShippingParentRanA
open Tools.ShippingParentTailsA Tools.ShippingParentDesignA
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingLeafTyped Tools.ShippingLeafPorts Tools.ShippingPortWidthsPure
open Tools.ShippingPortsMatchRaw
open Tools.ShippingChecksDerived (ff_absurd)
open Tools.ShippingChecksDepth (and_true_intro)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `leaf_run_ports` on the new boundary (port of `Tools.ShippingLeafPorts.leaf_run_ports`; the run is from a `JQ` world with the cache half). -/
theorem leaf_run_portsA {Dq : Nat} (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet Dq w) (hc : Dq = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    LeafPorts c d b := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closesM (profLogIO bb) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
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
  -- the leaf clause (position 9) and the cleanup clause for a machine
  -- without calls (position 11) of `MachineWired`
  obtain ⟨-, -, -, -, -, -, -, -, hleafIn, -, hclean, -⟩ := wired
  -- in the cleanup clause: the wire table is kept (1.2), an input other than
  -- the clock and the reset has its type's width in the wire table (8)
  obtain ⟨⟨-, hzw, -, -⟩, -, -, -, -, -, -, hinWd, -⟩ := hclean hno outTy
  obtain ⟨-, -, hwCM, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  have hM' : M = closeMachine d.shape.layout t' := hMeq
  -- the returned module's inputs, wires and wire table are the raw module's
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
  have hweb : Tools.ShippingEntrySoundness.weOf b = Tools.ShippingEntrySoundness.weOf M :=
    (Tools.ShippingRegisterSoundness.weOf_congr_wires hbw).trans hzw
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have h1 := Tools.ShippingClosedTyped.dropZW_wires_sub hp
    rw [hM'] at h1
    exact h1
  have hbIn : inPortsOf b = inPortsOf M := by
    unfold Tools.ShippingInstStmtG.inPortsOf
    rw [hbi]
  -- the closed machine's inputs
  obtain ⟨hcm0, hcm1⟩ :=
    closeMachine_inputs (t := t') (lay := d.shape.layout) hbodyc
  have hAal : ∀ p ∈ t'.inputs.take (t'.inputs.length - d.shape.layout.slots.length),
      Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => namesc p (inWc p (List.mem_of_mem_take hp))
  refine { wal := ?_, pos := hposv, args := ?_, argW := ?_, ins := ?_ }
  · intro p hp
    exact hwCM p (hwsub p hp)
  · have h9 := hleafIn hno
    exact ⟨ids, cache, hlenIds, hbIn.trans h9⟩
  · intro p hp
    have hp' : p ∈ M.inputs.filter (fun p => p.name != "clk" && p.name != "rst") := by
      rw [hbIn] at hp
      exact hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp'
    have hp3 : (p.name != "clk" && p.name != "rst") = true := hp2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp3
    have h := hinWd p hp1 hp3.1 hp3.2
    rw [hweb]
    constructor
    · intro hty
      rw [hty] at h
      exact h
    · intro k hty
      rw [hty] at h
      exact h
  · refine ⟨t'.inputs.take (t'.inputs.length - d.shape.layout.slots.length), hAal, ?_, ?_⟩
    · intro hs
      rw [hbi, hM']
      exact hcm0 hs
    · intro hs
      rw [hbi, hM']
      exact hcm1 hs

set_option maxHeartbeats 4000000 in
/-- `leaf_run_typedIn` on the new boundary (run from a `JQ` world with the cache half). -/
theorem leaf_run_typedInA {Dq : Nat} (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet Dq w) (hc : Dq = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
      PortsIn b ∧ b.body.all seqStmtOk = true ∧
      (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closesM (profLogIO bb) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
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
  have hPZ : PortsIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := PortsIn.of_typedIn hT
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
      exact Tools.ShippingSeqChildIface.mergeChecked_seqOk hseqZ

set_option maxHeartbeats 4000000 in
/-- `core_callConns_ran` over `MachineRanA O` (children `RealChildA O`, `instFields ≠ []`). -/
theorem core_callConns_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        (∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ mc = y.1) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
          (x ∈ b.wires.map (·.name) ∧
            ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
              Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
              ((pn = d.shape.instFields.getD k "" ∧ (∃ p ∈ mc.outputs, p.name = pn) ∧
                  ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
                    Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth) ∨
                (∃ (j : Nat) (q : Port) (a : Nat) (bn : Name × MixedGateBinder),
                  (inPortsOf mc)[j]? = some q ∧ q.name = pn ∧
                  ((d.shape.insts[k]).2.1)[j]? = some a ∧
                  d.shape.binders[nDecl + (d.shape.insts.length +
                    (d.shape.layout.slots.length + a))]? = some bn ∧
                  Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth))) := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
  -- the cleanup and the checked merge keep the non-zero wires and add none
  have hbw : ∀ p ∈ M.wires, p.ty.bitWidth ≠ 0 → p ∈ b.wires := by
    intro p hp hz
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2]
      exact Tools.ShippingOutsExtractedParts.dropZW_wires hp hz
  have hbsub : ∀ p ∈ b.wires, p ∈ M.wires := by
    intro p hp
    rcases hpost with h | h
    · rw [h] at hp
      exact Tools.ShippingInstWidthsParts.dropZW_wires_sub M p hp
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.2] at hp
      exact Tools.ShippingInstWidthsParts.dropZW_wires_sub M p hp
  -- the run
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
  · exact absurd hf0 hfne
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨PI, ls, hin, hPI, hlsL, hndI, hinW, hregs⟩ :=
    Tools.ShippingClosedPorts.closedPorts_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hwnd, hwal, hinWt, P1, P2, hsp, hP2d, hP2len, hP2ty⟩ :=
    Tools.ShippingTransitionPortTys.transitionPortTys_of_run d ok hbody hC hslots hdomB run
  have hls : P2 = ls := (List.append_inj' (hsp.symm.trans hin) (by omega)).2
  obtain ⟨hlenC, hallC⟩ := hreal
  intro mn iname conns hst
  rw [hbody'] at hst
  rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hst rfl with
    h0 | ⟨args, outs, child, mc, hcs, hfind, hne0, hall⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  -- every entry of the group is a call of a real child whose module is `mc`
  have hrealE : ∀ e ∈ outs, ∃ (hk : e.1 < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[e.1]).1 y ∧ mc = y.1 := by
    intro e he
    obtain ⟨hargs0, hch0, -⟩ := hall e he
    have hk0 : e.1 < d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs0).1
      simpa using this
    obtain ⟨y, hy, hor⟩ := hallC e.1 hk0
    rw [hy] at hch0
    have hyn : y.1.name = child.1.name := by
      simpa only [Option.map_some, Option.some.injEq] using hch0
    rcases hor with hmem | hre
    · rw [Tools.ShippingChildInv.nomem_tag hnomem hk0] at hmem
      cases hmem
    · have hyfind :=
        ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y
          (List.mem_of_getElem? hy)).1
      rw [hyn, hfind] at hyfind
      exact ⟨hk0, y, hre, Option.some.inj hyfind⟩
  obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ outs := by
    cases outs with
    | nil => exact absurd rfl hne0
    | cons a rest => exact ⟨a, List.Mem.head _⟩
  obtain ⟨hk0, y0, hre0, hmcy0⟩ := hrealE e0 he0
  have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
  have hfind' : moduleByName D.modules mn = some mc := by
    rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
    exact hfind
  -- a transition port after the declaration's: a wire of `b`, declared at
  -- the width of its binder's type
  have key : ∀ (i : Nat) (x : String),
      (t.inputs.map (·.name))[machNIn d.shape + i]? = some x →
      x ∈ b.wires.map (·.name) ∧ ∃ bn, d.shape.binders[nDecl + i]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
    intro i x hget
    rw [List.getElem?_map] at hget
    cases hq : t.inputs[machNIn d.shape + i]? with
    | none =>
      rw [hq] at hget
      cases hget
    | some q =>
      rw [hq] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      have hqm : q ∈ t.inputs := List.mem_of_getElem? hq
      obtain ⟨hqw, hqz⟩ := hinW q hqm
      have hql : ls[i]? = some q := by
        have h1 : (PI ++ ls)[PI.length + i]? = some q := by
          rw [← hin, hPI]
          exact hq
        rw [List.getElem?_append_right (Nat.le_add_right _ _)] at h1
        have h2 : PI.length + i - PI.length = i := by omega
        rw [h2] at h1
        exact h1
      have hlt : i < (d.shape.binders.drop nDecl).length := by
        rw [← hP2d, hls]
        exact (List.getElem?_eq_some_iff.mp hql).1
      have hbn : (d.shape.binders.drop nDecl)[i]? = some (d.shape.binders.drop nDecl)[i] :=
        List.getElem?_eq_getElem hlt
      have hty : q.ty = kindTy ((d.shape.binders.drop nDecl)[i]).2 :=
        hP2ty i q _ (by rw [hls]; exact hql) hbn
      have hbn' : d.shape.binders[nDecl + i]? = some (d.shape.binders.drop nDecl)[i] := by
        rw [← List.getElem?_drop]
        exact hbn
      -- its declared width in `b`: `q` is the only wire of its name
      have huniq : ∀ r ∈ b.wires, r.name = q.name → r = q := by
        intro r hr hrn
        have hrM : r ∈ M.wires := hbsub r hr
        rw [hMw] at hrM
        rcases Tools.ShippingTransitionPortTys.closeMachine_wires_sup _ _ r hrM with h1 | ⟨z, h1⟩
        · rw [Tools.ShippingTransitionPortTys.closeLets_wires hcl] at h1
          exact Tools.ShippingTransitionPortTys.port_of_name hwnd h1 (hinWt q hqm) hrn
        · have hal : Sparkle.IR.NameHints.Allocated (nextName z) := by
            rw [← h1, hrn]
            exact hwal q (hinWt q hqm)
          exact absurd hal (Tools.ShippingMachineClose.nextName_not_allocated z)
      have hqb : q ∈ b.wires := hbw q (by rw [hMw]; exact hqw) hqz
      have hdw : Sparkle.IR.RegDedup.declWidth b q.name = q.ty.bitWidth :=
        Tools.ShippingInstWidthsParts.declWidth_of_unique (nm := q.name) (ty := q.ty)
          hqb huniq
          (by rw [hty]; exact Tools.ShippingTransitionPortTys.kindTy_shape _)
      exact ⟨List.mem_map.mpr ⟨q, hqb, hget⟩, _, hbn', by rw [← hget, hdw, hty]⟩
  refine ⟨mc, hfind', ⟨e0.1, hk0, y0, hre0, hmcy0⟩, ?_⟩
  intro pn x hpc
  rcases callStmtG_conn hcs hpc with ⟨j, q, a, hq, hqn, haj, hnm⟩ | hclk | ⟨e, he, hget, hef, p, hp, hpn⟩
  · -- an argument connection: the `let`'s transition port
    have eidx : machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length + a =
        machNIn d.shape + (d.shape.insts.length + (d.shape.layout.slots.length + a)) := by
      omega
    have hnm' : (t.inputs.map (·.name))[machNIn d.shape +
        (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some x := by
      rw [← eidx]
      exact hnm
    obtain ⟨hxw, bn, hbn, hdw⟩ := key _ x hnm'
    have h9 : (d.shape.insts.map (·.2.1))[e0.1]? =
        Option.map (·.2.1) (some (d.shape.insts[e0.1])) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hk0]
    have h10 : some args = some ((d.shape.insts[e0.1]).2.1) :=
      (hall e0 he0).1.symm.trans h9
    have hA : args = (d.shape.insts[e0.1]).2.1 := Option.some.inj h10
    rw [hA] at haj
    exact Or.inr ⟨hxw, e0.1, hk0, y0, hre0, hmcy0,
      Or.inr ⟨j, q, a, bn, hq, hqn, haj, hbn, hdw⟩⟩
  · exact Or.inl hclk
  · -- an output connection: the entry's transition port
    obtain ⟨hke, y, hre, hmcy⟩ := hrealE e he
    obtain ⟨-, -, hfld⟩ := hall e he
    obtain ⟨hxw, bn, hbn, hdw⟩ := key e.1 x hget
    exact Or.inr ⟨hxw, e.1, hke, y, hre, hmcy,
      Or.inl ⟨by rw [← hef, hfld], ⟨p, hp, hpn⟩, bn, hbn, hdw⟩⟩

set_option maxHeartbeats 4000000 in
/-- `core_portsMatch_raw_ran` over `MachineRanA O`. -/
theorem core_portsMatch_raw_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    -- OUTPUT side: the result binder's width is the child's field port's
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    -- OUTPUT side: the child's output ports are resolved by its emitted width map
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1)
    -- INPUT side: the data condition, and (NOT derived) the child's argument
    -- ports' emitted widths
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    -- CLOCK / RESET (NOT derived): one bit in a sequential child ...
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y → isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    -- ... and in the parent (NOT derived)
    (hclkB : Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true := by
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingParentTailsA.core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem
      hpost ran hon hoty
  have hconn := core_callConns_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hpost ran
  refine Tools.ShippingTextShipped.portsMatchB_of ?_ ?_
  · intro mn iname conns child cwe hst hc cn hcm x hc2
    obtain ⟨mc, hmc, ⟨k0, hk0, y0, hre0, hmcy0⟩, hall⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    rw [hCm] at hc
    have hch : child = mc := (congrArg Prod.fst (Option.some.inj hc)).symm
    rw [hch]
    have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
      rw [← hc2]
      exact hcm
    rcases hall cn.1 x hcm' with ⟨hseq, hcr⟩ | ⟨hxw, k, hk, y, hre, hmcy, hside⟩
    · -- the clock and the reset
      have hseq' : isSeqChild y0.1 = true := by
        rw [← hmcy0]
        exact hseq
      obtain ⟨hk1, hk2⟩ := hkidClk k0 hk0 y0 hre0 hseq'
      rcases hcr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2, hmcy0, hk1]
        exact hclkB.1
      · rw [e1, e2, hmcy0, hk2]
        exact hclkB.2
    · have h1 : Tools.ShippingDesignSV.weS b x = Sparkle.IR.RegDedup.declWidth b x :=
        (Tools.ShippingWidthTables.declWidth_eq_weS hT.wn hxw).symm
      rcases hside with ⟨hpn, ⟨p, hp, hpe⟩, bn, hbn, hdw⟩ | ⟨j, q, a, bn, hq, hqn, haj, hbn, hdw⟩
      · -- an output connection
        have hP := hkidT k hk y hre
        have hp' : p ∈ y.1.outputs := by
          rw [← hmcy]
          exact hp
        have h3 := hkidW k hk y hre p hp' (hpe.trans hpn)
        rw [hbn] at h3
        have h4 : some ((kindTy bn.2).bitWidth) = some p.ty.bitWidth := h3
        have h5 := Option.some.inj h4
        rw [h1, hdw, h5, hmcy, ← hpe]
        exact (hP.weS_output hp').symm
      · -- an argument connection
        have hq' : (inPortsOf y.1)[j]? = some q := by
          rw [← hmcy]
          exact hq
        obtain ⟨wd, hwd, hws⟩ := hkidIn k hk y hre j q hq'
        have h5 := callArgs_width hargs hk haj hbn hwd
        rw [h1, hdw, h5, hmcy, ← hqn]
        exact hws.symm
  · intro mn iname conns hst
    obtain ⟨mc, hmc, -, -⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp [hCm]

set_option maxHeartbeats 4000000 in
/-- `core_clk_ran` over `MachineRanA O`. -/
theorem core_clk_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
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
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
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


/-- A real leaf child's ports (`LeafPorts`), from its `RealChildA` (its own run). -/
theorem leaf_real_portsA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) : LeafPorts c d y.1 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact leaf_run_portsA O adm d ok hbody hC hdomB hno hSS outTy ⟨quiet, synth, rfl⟩
      (Or.inr (fun c r h => cache c r h)) hr
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-- `hkidIn` of the port matching for a real leaf child, from its `RealChildA`. -/
theorem leaf_real_inWidthsA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
      ∃ wd, (declWidths d)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd :=
  fun _ _ hq =>
    (leaf_real_portsA O d ok hbody hC hdomB hno hSS outTy entry closes h).inWidths hq

/-- `hkidClk` of the port matching for a real leaf child, from its `RealChildA`. -/
theorem leaf_real_clkA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1 :=
  fun hs => (leaf_real_portsA O d ok hbody hC hdomB hno hSS outTy entry closes h).clk hs

/-- A real leaf child's typed-in facts, from its `RealChildA`. -/
theorem leaf_real_typedInA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChildA O c y) :
    ∃ m0 : Sparkle.IR.AST.Module, (y.1 = m0 ∨ y.1 = mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
      PortsIn y.1 ∧ y.1.body.all seqStmtOk = true ∧
      (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false) := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact leaf_run_typedInA O adm d ok hbody hC hdomB hno hSS outTy ⟨quiet, synth, rfl⟩
      (Or.inr (fun c r h => cache c r h)) hr
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx') hon hoty

/-- `PortsIn` of a real leaf child, from its `RealChildA`. -/
theorem leaf_real_portsInA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChildA O c y) : PortsIn y.1 := by
  obtain ⟨m0, -, -, -, hp, -, -⟩ :=
    leaf_real_typedInA O d ok hbody hC hdomB hno hSS outTy entry closes hon hoty h
  exact hp

/-- `leaf_real_kidK_reg` on the new boundary (children's check of a real leaf child with a register). -/
theorem leaf_real_kidK_regA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChildA O c y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  obtain ⟨m0, hpost, hT, hs0, -, hs, hna⟩ :=
    leaf_real_typedInA O d ok hbody hC hdomB hno hSS outTy entry closes hon hoty h
  have hI := seqChild_of_realA O d ok hbody hno outTy entry closes h
  have htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf y.1)
        (Tools.ShippingDesignSV.weS y.1) y.1.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames y.1.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth y.1 x == Tools.ShippingDesignSV.weS y.1 x) =
          true := by
    rcases hpost with e | e
    · rw [e]
      exact hT.seqCheck
    · rcases Sparkle.IR.RefineCheck.mergeChecked_print (hna hsl) with e' | hp
      · have e2 : y.1 = m0 := e.trans e'
        rw [e2]
        exact hT.seqCheck
      · have hp' : Sparkle.IR.PrintGuard.printOk y.1 = true := by
          rw [e]
          exact hp
        exact Tools.ShippingPrintGuard.printOk_sound hp'
  refine ⟨fun C n => kidCheck_leaf_of_text C n hs htext.1 htext.2, ?_⟩
  intro g hg
  rw [hI.design] at hg
  cases hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module on the new boundary, `instFields ≠ []`**: the old
`core_designCheck_run_ran` over `MachineRanA O`, with the connection widths `portsMatchB` and the children's check
`kidsPass (kidCheck …)` DERIVED (from `core_portsMatch_raw_ranA` through `portsMatchB_shipped`, and `core_kidsPass_anyA`)
from the per-child facts `hkidT`, `hkidIn`, `hkidClk`, `hkidK` and the data conditions `hargs` — no check premise. -/
theorem core_designCheck_ranFA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1)
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y → isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
        ∀ g ∈ y.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (n : Nat) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  Tools.ShippingTextShipped.core_designCheck_rest2
    (Tools.ShippingParentRunFactsA.core_runFacts_ranA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
      hkidP hkidW hpost ran)
    (core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran hon hoty)
    n
    (Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (core_hierGate_anyA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran)
      (core_portsMatch_raw_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidW hkidT hargs hkidIn
        hkidClk hpost ran hon hoty
        (core_clk_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost ran)))
    (core_kidsPass_anyA O d ok hbody hC hslots hdomB hins outTy hnomem hkidK hpost ran n)

end Tools.ShippingParentDesignFA
