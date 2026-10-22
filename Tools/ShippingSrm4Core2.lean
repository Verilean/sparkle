import Tools.ShippingParentRunFactsA
import Tools.ShippingKidsSelfA
import Tools.ShippingParentDesignA
import Tools.ShippingSrm4Core1
-- BUILT (unit SRM4): c4 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (binding, residue R2): SCRIPTED copies (`scripts/srm4/port_srm4.py`, specs `scripts/srm4/spec*.json`) of `core_hierGate_anyA`, `core_kids_self_ranA`, `core_raw_facts_ranA`, `core_outsExtracted_ranA`, `core_callPorts_ranA`, `core_instOutWidthsOk_ranA`, `core_runFacts_ranA`, from the A-form originals in `Tools/ShippingParentDesignA.lean`, `Tools/ShippingKidsSelfA.lean`, `Tools/ShippingParentRunFactsA.lean`, with the memory entries of the callee allowed.  The script's changes, all of them:
-- the theorem's name gets the suffix `M`; the binder `hnomem` is removed and `hfne : d.shape.instFields ≠ []` is added after `hins` where the original had none; a call of a copied theorem calls the copy; `RealChildA O (d.shape.insts[k]).1 y` (the kid of
-- call entry `k`) becomes `KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y` (the origin's built module, or a `RealChildA` when the origin builds none); the three lines refuting the memory case of a child (`rw [nomem_tag hnomem …] at hmem; cases hmem`) become
-- `kidTA_ofO` (from `MemChildren` of the closing, taken from the closing's own statement); `set_option maxHeartbeats … in` lines are DROPPED (the copies run at the default budget).  Nothing is routed through the old-form `RealChild` / `MachineRan` / `MachineClosesAt` or `kidsChild_of_realM`.
-- The per-kid facts stay hypotheses over `KidTA`.  `RealChildA` is a history of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingSrm4Core2
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
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped Tools.ShippingHierGateAny
open Tools.ShippingOneOutFacts (RunFactsH designCheckH_rest)
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)
open Tools.ShippingParentRanA Tools.ShippingParentTailsA
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingParentDesignA
open Tools.ShippingPortsMatchRaw (callStmtG_conn)
open Tools.ShippingChildBndCore Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingSeqChildIfaceA Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped Tools.ShippingParentRanA
open Tools.ShippingParentTailsA Tools.ShippingParentDesignA
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingChecksWidths Tools.ShippingChecksOuts Tools.ShippingChecksRaw Tools.ShippingChecksRun
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA Tools.ShippingSrm4Core1
open Tools.ShippingInstTagged (originAt)

/-- **The statement-kind gate of the hierarchical check, for either
closing**: the full entry's module of a machine with calls has an instance
statement, and every statement is an instance, an assignment or a
register. -/
theorem core_hierGate_anyAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  have hbody' : b.body = M.body :=
    (core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  have hk0 : 0 < (d.shape.insts.map (·.2.1)).length := by
    rw [List.length_map]
    exact List.length_pos_iff.mpr hins
  refine Tools.ShippingInstWidthsParts.hierGate_of ?_ ?_
  · -- the instance statement of the first call, in either closing
    rw [hbody']
    rcases hcc with ⟨-, hI⟩ | ⟨-, hG, -⟩
    · -- the one-output closing
      obtain ⟨args, child, mc, -, -, -, st, hst, hcs⟩ :=
        Tools.ShippingMachineInst.closeInsts_calls hI 0 hk0
      obtain ⟨outW, argWs, outP, iname, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      rw [he] at hst
      exact ⟨mc.name, iname, _, hst⟩
    · -- the group closing (the proof of `core_hierGate`)
      obtain ⟨st, hst, args, outs, child, mc, hcs, -⟩ :=
        Tools.ShippingMachineInstG.closeInstsG_calls hG 0 hk0
      obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
  · intro st hst
    rw [hbody'] at hst
    rcases List.mem_append.mp (hperm.symm.subset hst) with h0 | h0
    · exact Or.inr (List.all_eq_true.mp hseq0 _ h0)
    · exact Or.inl (List.all_eq_true.mp hLinst _ h0)

/-- `core_kids_self` over `MachineRanA O`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is `MachineRanA O` (the machine synthesis this core run performed returned
`(M, D)`, decomposed on the new boundary); the instance from a core run is via unit PH's
`Tools.ShippingParentRanA.machineRanA_main` (premises `O`, `hA`, `T`, start world, `MachineClosesAtA`). -/
theorem core_kids_self_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 := by
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, -, L, -, -, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨-, -, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the closing's own check: every child, and every module of a child's
  -- design, is found by its name in the merged design as itself
  have hself : ∀ y ∈ children, moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 := by
    rcases hcc with ⟨-, hI⟩ | ⟨-, hG, -⟩
    · intro y hy
      exact ⟨(Tools.ShippingChildServe.closeInsts_names hI).2 y hy,
        (Tools.ShippingChildServe.closeInsts_acyclic hI).2.2.2 y hy⟩
    · exact (Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  have hMC : MemChildren d.shape children := by
    rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩
    · exact absurd hf0 hfne
    · exact h
  -- the design: the join of the children
  obtain ⟨-, hdVis⟩ := designWith_modules (children := children) hd0
  intro g hg
  have hg' : g ∈ (designWith children d₀).modules := by
    rw [← hDeq]
    exact hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg')
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  have hk' : k < d.shape.insts.length := by
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨y', hy', hor'⟩ := hall k hk'
  rw [hk] at hy'
  cases hy'
  have hre := kidTA_ofO hk' hMC hk hor'
  · exact ⟨k, hk', y, hre, hor, hself y hy⟩

/-- `core_raw_factsM_ranT` over `MachineRanA O` (children `RealChildA O`, no memory children): reset input, distinct instance names, self-read test. -/
theorem core_raw_facts_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
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

/-- `core_outsExtracted_ran` over `MachineRanA O`. -/
theorem core_outsExtracted_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  -- the full entry's body is the raw module's; no assignment targets an instance output
  have hbody' : b.body = M.body :=
    (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
  have hasg := Tools.ShippingSrm4Core1.core_instOuts_not_assigned_ranAM O d ok hbody hC hslots hdomB
    hins hfne outTy hpost ran
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
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, hMC⟩
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
        have hre := kidTA_ofO hk0 hMC hy hor
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

/-- `core_callPortsM_ran` over `MachineRanA O` (hnomem instead of `TagsAgree`; children `RealChildA O`). -/
theorem core_callPorts_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
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
            Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
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
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, hMC⟩
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
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape e.1) (d.shape.insts[e.1]).1 y ∧ mc = y.1 := by
    intro e he
    obtain ⟨hargs0, hch0, -⟩ := hall e he
    have hk0 : e.1 < d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs0).1
      simpa using this
    obtain ⟨y, hy, hor⟩ := hallC e.1 hk0
    rw [hy] at hch0
    have hyn : y.1.name = child.1.name := by
      simpa only [Option.map_some, Option.some.injEq] using hch0
    have hre : Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape e.1) (d.shape.insts[e.1]).1 y := by
      have hre := kidTA_ofO hk0 hMC hy hor
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

/-- `core_instOutWidthsOk_ran` over `MachineRanA O`. -/
theorem core_instOutWidthsOk_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true := by
  have hcp := core_callPorts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hkidP hpost ran
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

/-- **`core_runFacts` on the new boundary**: the run's facts of the full entry's module of a machine with calls, a
register and `instFields ≠ []`, from `MachineRanA O` (no memory children). -/
theorem core_runFacts_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
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
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨hrst, hndB, hself⟩ :=
    core_raw_facts_ranAM O d ok hbody hC hslots hdomB hins hsl hfne outTy hpost ran
  exact
    { gate := core_hierGate_anyAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
      wfB := core_linkedWF_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
      ndB := hndB
      self := hself
      outs := core_outsExtracted_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hkidP hpost ran
      rst := hrst
      wid := core_instOutWidthsOk_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hkidP hkidW
        hpost ran }

end Tools.ShippingSrm4Core2
