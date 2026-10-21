import Tools.ShippingParentDesignA
import Tools.ShippingParentTailsA
import Tools.ShippingChecksWidths
import Tools.ShippingChecksOuts
import Tools.ShippingChecksRaw
import Tools.ShippingChecksRun
import Tools.ShippingChecksRunFacts
import Tools.ShippingCallWidths
import Tools.ShippingCallWidthsChildRealA
import Tools.ShippingChecksMaskedLeafA
import Tools.ShippingSeqChildIfaceA
-- UNBUILT (unit SR3e, par/u-sr3e). See REPORT-SR3e.md for the build log.
-- SCOPE (binding): facts about the CHECKS of the shipped module of a machine with calls AND `instFields ≠ []`
-- (a struct-result / multi-output child) on the NEW boundary: `RunFacts` and the statement-kind-gated `outsCheck`.
-- NOT a parent semantic-equivalence head; not runtime fit. `RealChildA` is a history. No `sorry`, no `axiom`, no new law.

/-! # Unit SR3e: `RunFacts` / `outsCheck` of a parent with `instFields ≠ []` over `MachineRanA O`

Mechanical ports (`.cluster/logs/gen_sr3e.py`: verbatim proof text, the head and the run preamble replaced) of the
`MachineRan`/`RealChild`-typed `Tools.ShippingChecksRaw.core_raw_factsM_ranT`, `Tools.ShippingChecksOuts.core_outsExtracted_ran`,
`Tools.ShippingChecksWidths.core_callPortsM_ran` / `core_instOutWidthsOk_ran`, `Tools.ShippingCallWidths.hkidW_of_data`
and the child side `Tools.ShippingChecksRun.leaf_run_outsAssigned`, to `MachineRanA O` / `RealChildA O` (no memory
children: `hnomem` for `TagsAgree`).  Assembled: `core_runFacts_ranA` (the old `core_runFacts` on the new boundary,
`PH`'s `core_hierGate_anyA` and `core_linkedWF_ranA` for the gate / `linkedWF` fields) and `core_outsCheck_all_gate_ranA`
(PH, `Tools/ShippingParentPortsA.lean`) is reused as is for the output check. -/

namespace Tools.ShippingParentRunFactsA
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
open Tools.ShippingChecksWidths Tools.ShippingChecksOuts Tools.ShippingChecksRaw Tools.ShippingChecksRun

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `leaf_run_outsAssigned` on the new boundary (port of `Tools.ShippingChecksRun.leaf_run_outsAssigned`; the run is from a `JQ` world with the cache half). -/
theorem leaf_run_outsAssignedA {D : Nat} (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
  obtain ⟨M, D', w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closesM (profLogIO bb) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
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
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  -- the transition ends in `assign out = w`, and so does the `let`-closed one
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hrawA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    rw [hMeq]
    exact Tools.ShippingChecksDerived3.closeMachine_outsAssigned hpw'
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
  obtain ⟨⟨hzb, -, -, hzo⟩, -, hregs, -, -, -, -, -, -⟩ := hclean hno outTy
  -- the core module has a register (a slot)
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
  exact Tools.ShippingChecksDerived3.entry_outsAssigned hrawA hzb hzo hnA hpost

set_option maxHeartbeats 4000000 in
/-- `core_raw_factsM_ranT` over `MachineRanA O` (children `RealChildA O`, no memory children): reset input, distinct instance names, self-read test. -/
theorem core_raw_facts_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
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
  obtain ⟨-, hAlloc, -, -, -, -, -, -, -, -, -, -, -, hG14, -, hcleanAny, hInputs, -⟩ := wired
  obtain ⟨-, -, hzi, -⟩ := hcleanAny outTy
  obtain ⟨hndM, hsfM⟩ := hG14 hfne
  obtain ⟨outWs, extra, houtWs, -, -, hMin⟩ := hInputs
  have hbody' : b.body = M.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
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
    exact rst_not_allocated (hAlloc _ (List.mem_of_getElem? hk))
  have hrstM : "rst" ∈ M.inputs.map (·.name) := by
    rw [hMin]
    refine List.mem_map.mpr ⟨{ name := "rst", ty := .bit }, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [hne]
      simp
    · simpa using hnotW
  refine ⟨by rw [hbin]; exact hrstM, ?_, ?_⟩
  · rw [hbody', ← instNameOf_eq]
    exact hndM
  · rw [hbody']
    exact noSelfRead_of_feed hsfM

set_option maxHeartbeats 4000000 in
/-- `core_outsExtracted_ran` over `MachineRanA O`. -/
theorem core_outsExtracted_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  -- the full entry's body is the raw module's; no assignment targets an instance output
  have hbody' : b.body = M.body :=
    (Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
  have hasg := Tools.ShippingParentTailsA.core_instOuts_not_assigned_ranA O d ok hbody hC hslots hdomB
    hins outTy hnomem hpost ran
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
  obtain ⟨hlenC, hallC⟩ := hreal
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
      rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hst rfl with
        h0 | ⟨args, outs, child, mc, hcs, hfind, hne0, hall⟩
      · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
      · -- an entry of the group, its child
        obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ outs := by
          cases outs with
          | nil => exact absurd rfl hne0
          | cons a rest => exact ⟨a, List.Mem.head _⟩
        obtain ⟨hargs0, hch0, -⟩ := hall e0 he0
        have hk0 : e0.1 < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hargs0).1
          simpa using this
        obtain ⟨y, hy, hor⟩ := hallC e0.1 hk0
        rw [hy] at hch0
        have hyn : y.1.name = child.1.name := by
          simpa only [Option.map_some, Option.some.injEq] using hch0
        rcases hor with hmem | hre
        · rw [Tools.ShippingChildInv.nomem_tag hnomem hk0] at hmem
          cases hmem
        · -- the instance's module is the child's
          have hyfind :=
            ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y
              (List.mem_of_getElem? hy)).1
          rw [hyn, hfind] at hyfind
          have hmcy : mc = y.1 := Option.some.inj hyfind
          have hap : ∀ p ∈ mc.outputs, (∀ q ∈ inPortsOf mc, q.name ≠ p.name) ∧
              p.name ≠ "clk" ∧ p.name ≠ "rst" := by
            rw [hmcy]
            exact hkidP e0.1 hk0 y hre
          have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
          have hfind' : moduleByName D.modules mn = some mc := by
            rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
            exact hfind
          obtain ⟨p, hp, hpc⟩ := Tools.ShippingOutsExtractedParts.stmtInstOuts_inst hfind' hxs
          obtain ⟨hpin, hclk, hrst⟩ := hap p hp
          obtain ⟨e, he, hget⟩ :=
            Tools.ShippingOutsExtractedParts.callStmtG_outWire hcs hpin hclk hrst hpc
          obtain ⟨hargsE, -⟩ := hall e he
          have hke : e.1 < d.shape.insts.length := by
            have := (List.getElem?_eq_some_iff.mp hargsE).1
            simpa using this
          exact ⟨e.1, hke, hget⟩
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
    obtain ⟨outWsI, hmapI, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
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
/-- `core_callPortsM_ran` over `MachineRanA O` (hnomem instead of `TagsAgree`; children `RealChildA O`). -/
theorem core_callPorts_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
            Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
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
    have hre : Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[e.1]).1 y := by
      rcases hor with hmem | hre
      · rw [Tools.ShippingChildInv.nomem_tag hnomem hk0] at hmem
        cases hmem
      · exact hre
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
  have hap : ∀ p ∈ mc.outputs, (∀ q ∈ inPortsOf mc, q.name ≠ p.name) ∧
      p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    rw [hmcy0]
    exact hkidP e0.1 hk0 y0 hre0
  have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
  have hfind' : moduleByName D.modules mn = some mc := by
    rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
    exact hfind
  refine ⟨mc, hfind', ?_⟩
  intro p hp x hpc
  obtain ⟨hpin, hclk, hrst⟩ := hap p hp
  obtain ⟨e, he, hget, hef⟩ :=
    Tools.ShippingInstWidthsParts.callStmtG_outWireF hcs hpin hclk hrst hpc
  obtain ⟨hke, y, hre, hmcy⟩ := hrealE e he
  obtain ⟨-, -, hfld⟩ := hall e he
  -- the call port: a transition input, of its binder's type
  rw [List.getElem?_map] at hget
  cases hq : t.inputs[machNIn d.shape + e.1]? with
  | none =>
    rw [hq] at hget
    cases hget
  | some q =>
    rw [hq] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    have hqm : q ∈ t.inputs := List.mem_of_getElem? hq
    obtain ⟨hqw, hqz⟩ := hinW q hqm
    have hql : ls[e.1]? = some q := by
      have h1 : (PI ++ ls)[PI.length + e.1]? = some q := by
        rw [← hin, hPI]
        exact hq
      rw [List.getElem?_append_right (Nat.le_add_right _ _)] at h1
      have h2 : PI.length + e.1 - PI.length = e.1 := by omega
      rw [h2] at h1
      exact h1
    have hlt : e.1 < (d.shape.binders.drop nDecl).length := by
      rw [← hP2d, hls]
      exact (List.getElem?_eq_some_iff.mp hql).1
    have hbn : (d.shape.binders.drop nDecl)[e.1]? = some (d.shape.binders.drop nDecl)[e.1] :=
      List.getElem?_eq_getElem hlt
    have hty : q.ty = kindTy ((d.shape.binders.drop nDecl)[e.1]).2 :=
      hP2ty e.1 q _ (by rw [hls]; exact hql) hbn
    have hbn' : d.shape.binders[nDecl + e.1]? = some (d.shape.binders.drop nDecl)[e.1] := by
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
    have hdw : Sparkle.IR.RegDedup.declWidth b q.name = q.ty.bitWidth :=
      Tools.ShippingInstWidthsParts.declWidth_of_unique (nm := q.name) (ty := q.ty)
        (hbw q (by rw [hMw]; exact hqw) hqz) huniq
        (by rw [hty]; exact Tools.ShippingTransitionPortTys.kindTy_shape _)
    exact ⟨e.1, hke, y, hre, hmcy, by rw [← hef, hfld], _, hbn',
      by rw [← hget, hdw, hty]⟩

set_option maxHeartbeats 4000000 in
/-- `core_instOutWidthsOk_ran` over `MachineRanA O`. -/
theorem core_instOutWidthsOk_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true := by
  have hcp := core_callPorts_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hpost ran
  refine Tools.ShippingInstWidthsParts.instOutWidthsOk_of b.body ?_
  intro mn iname conns hst
  obtain ⟨mc, hfind, hports⟩ := hcp mn iname conns hst
  refine ⟨mc, Sparkle.IR.RegDedup.declWidth mc,
    congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hfind, ?_⟩
  intro p hp x hl
  obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
  have hpc : (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [e]
    exact List.mem_append_right _ (List.Mem.head _)
  obtain ⟨k, hk, y, hre, hmcy, hpn, bn, hbn, hdw⟩ := hports p hp x hpc
  have hw := hkidW k hk y hre p (by rw [← hmcy]; exact hp) hpn
  rw [hbn] at hw
  have hwe : (kindTy bn.2).bitWidth = p.ty.bitWidth := by
    simpa only [Option.map_some, Option.some.injEq] using hw
  rw [hdw, hwe]

set_option maxHeartbeats 4000000 in
/-- `hkidW_of_data` for `RealChildA O` children. -/
theorem hkidW_of_dataA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  intro k hk y hy p hp hpn
  unfold Tools.ShippingCallWidths.callWidthsOk at hcw
  have h1 : ((kidOuts k).all fun o =>
      o.name != d.shape.instFields.getD k "" ||
        decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp hcw k (List.mem_range.mpr hk)
  rw [(hkidT k hk y hy).outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  have h2 : (o.name != d.shape.instFields.getD k "" ||
      decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
        some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp h1 o ho
  have hpn' : o.name = d.shape.instFields.getD k "" := by
    rw [← e] at hpn
    exact hpn
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd hpn' (bne_iff_ne.mp h2)
  · have h3 := of_decide_eq_true h2
    rw [← e]
    exact h3


/-- A real leaf child assigns every output, from its `RealChildA` (its own run). -/
theorem leaf_real_outsAssignedA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact leaf_run_outsAssignedA O adm d ok hbody hno hsl hSS outTy ⟨quiet, synth, rfl⟩
      (Or.inr (fun c r h => cache c r h)) hr
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-- `hkidA` of a real leaf child with a register, from its `RealChildA`. -/
theorem leaf_real_kidAA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true := by
  refine ⟨leaf_real_outsAssignedA O d ok hbody hno hsl hSS outTy entry closes h, ?_⟩
  have hI := seqChild_of_realA O d ok hbody hno outTy entry closes h
  intro g hg
  rw [hI.design] at hg
  cases hg

/-- `hkidR` of a real leaf child without calls, from its `RealChildA`. -/
theorem leaf_real_kidRA {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn := by
  have hI := seqChild_of_realA O d ok hbody hno outTy entry closes h
  intro g hg mn i conns hm
  rw [hI.design] at hg
  have hgy : g = y.1 := List.mem_singleton.mp hg
  rw [hgy] at hm
  have hs := List.all_eq_true.mp hI.seqOk _ hm
  exact Tools.ShippingChecksDerived.ff_absurd hs

set_option maxHeartbeats 4000000 in
/-- **`core_runFacts` on the new boundary**: the run's facts of the full entry's module of a machine with calls, a
register and `instFields ≠ []`, from `MachineRanA O` (no memory children). -/
theorem core_runFacts_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
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
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨hrst, hndB, hself⟩ :=
    core_raw_facts_ranA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hpost ran
  exact
    { gate := core_hierGate_anyA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
      wfB := core_linkedWF_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
      ndB := hndB
      self := hself
      outs := core_outsExtracted_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hpost ran
      rst := hrst
      wid := core_instOutWidthsOk_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hkidW
        hpost ran }

end Tools.ShippingParentRunFactsA
