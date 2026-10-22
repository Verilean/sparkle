import Tools.ShippingParentTailsA
import Tools.ShippingSrm3Iface
-- BUILT (unit SRM4): c4 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (binding, residue R2): SCRIPTED copies (`scripts/srm4/port_srm4.py`, specs `scripts/srm4/spec*.json`) of `core_linkedWF_ranA`, `core_instOuts_not_assigned_ranA`, `core_closed_typedIn_ranA` (and `kidTA_ofO`, the A-form of `kidT_ofO`), from the A-form originals in `Tools/ShippingParentTailsA.lean`, with the memory entries of the callee allowed.  The script's changes, all of them:
-- the theorem's name gets the suffix `M`; the binder `hnomem` is removed and `hfne : d.shape.instFields ≠ []` is added after `hins` where the original had none; a call of a copied theorem calls the copy; `RealChildA O (d.shape.insts[k]).1 y` (the kid of
-- call entry `k`) becomes `KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y` (the origin's built module, or a `RealChildA` when the origin builds none); the three lines refuting the memory case of a child (`rw [nomem_tag hnomem …] at hmem; cases hmem`) become
-- `kidTA_ofO` (from `MemChildren` of the closing, taken from the closing's own statement); `set_option maxHeartbeats … in` lines are DROPPED (the copies run at the default budget).  Nothing is routed through the old-form `RealChild` / `MachineRan` / `MachineClosesAt` or `kidsChild_of_realM`.
-- The per-kid facts stay hypotheses over `KidTA`.  `RealChildA` is a history of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingSrm4Core1
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
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)
open Tools.ShippingParentRanA
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingParentTailsA


/-- **A child of the general closing's run is the tag-based kid of its entry** (A-form of `kidT_ofO`; no name condition). -/
theorem kidTA_ofO {O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref} {shape : MachineShape} {children : List Res} {k : Nat}
    (hk : k < shape.insts.length) (hMC : MemChildren shape children) {y : Res}
    (hy : children[k]? = some y)
    (hor : (shape.instOrigins.getD k .ord).child? = some y ∨
      Tools.ShippingChildCacheA.RealChildA O (shape.insts[k]).1 y) :
    KidTA O (Tools.ShippingInstTagged.originAt shape k) (shape.insts[k]).1 y := by
  rcases hor with h | h
  · exact Or.inl h
  · cases hm : (shape.instOrigins.getD k .ord).child? with
    | none => exact Or.inr ⟨hm, h⟩
    | some md =>
      have h1 : children[k]? = some md := hMC k hk md hm
      rw [hy] at h1
      rw [Option.some.inj h1]
      exact Or.inl hm

/-- `core_linkedWF_ranAM O` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_linkedWF_ranAM O` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_linkedWF_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    Tools.ShippingHierOpen.linkedWF (childMap D.modules) b.body = true := by
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
  obtain ⟨-, -, -, -, -, -, hlink, -⟩ := wired
  have hbody' : b.body = M.body :=
    (core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
  rw [hbody', ← Tools.ShippingMachineLinked.linkedOk_eq]
  exact hlink

/-- `core_instOuts_not_assigned_ranAM O` over `MachineRan` (round par/g-1): the statement and the proof of
`core_instOuts_not_assigned_ranAM O` (`Tools/ShippingLinkedFresh.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_instOuts_not_assigned_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    ∀ x, x ∈ bodyInstOuts (childMap D.modules) b.body →
      x ∉ Sparkle.IR.Reorder.writesOf b.body :=
  instOuts_not_written b.body
    (core_linkedWF_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran)

/-- `core_closed_typedIn_ranAM O` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_closed_typedIn_ranAM O` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_closed_typedIn_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    -- the two data conditions on the output ports
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingTextTyped.TypedIn b := by
  -- the body and the output ports of the full entry's module are the raw module's
  have hkf := core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
  have hbb : b.body = M.body := hkf.2.1
  have hbo : b.outputs = M.outputs := hkf.2.2.1
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
  -- the raw module's wiring: its outputs, its inputs, its cleanup
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hnamesA, -, -, -, -, -, houtsM, -, -, -, -, -, -, -, hcleanAny, hinM, -⟩ := wired
  obtain ⟨-, hzw, -, -⟩ := hcleanAny outTy
  obtain ⟨outWs, extra, -, -, hextra, hMin⟩ := hinM
  have hMinputs : ∀ p ∈ M.inputs,
      Sparkle.IR.NameHints.Allocated p.name ∨ p.name = "clk" ∨ p.name = "rst" := by
    intro p hp
    rw [hMin] at hp
    have hp' := (List.mem_filter.mp hp).1
    rcases List.mem_append.mp hp' with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (hnamesA p.name (List.mem_map.mpr ⟨p, List.mem_of_mem_take h, rfl⟩))
      · split at h
        · cases h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
    · rcases hextra with he | ⟨he, -⟩
      · rw [he] at h
        cases h
      · rw [he] at h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  -- the `let`-closed transition and the closed machine
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨-, -, hwCM, -, hoCM, hkCM, haCM, hrCM⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  -- the wire table of the full entry's module is the closed machine's
  have hweb : Tools.ShippingEntrySoundness.weOf b =
      Tools.ShippingEntrySoundness.weOf (closeMachine d.shape.layout t') :=
    ((Tools.ShippingRegisterSoundness.weOf_congr_wires hbw).trans hzw).trans
      (Tools.ShippingRegisterSoundness.weOf_congr_wires hMw)
  have hwsub : ∀ p ∈ b.wires, p ∈ (closeMachine d.shape.layout t').wires := by
    intro p hp
    rw [hbw] at hp
    have := dropZW_wires_sub hp
    rw [hMw] at this
    exact this
  have hbouts : b.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := hbo.trans houtsM
  -- its assignments and registers are the closed machine's
  have hsub : ∀ st ∈ b.body, st ∈ (closeMachine d.shape.layout t').body ∨
      Sparkle.IR.Machine.isInst st = true := by
    intro st hst
    rw [hbb] at hst
    rcases List.mem_append.mp (hperm.symm.subset hst) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (List.all_eq_true.mp hLinst _ h0)
  -- an output port: its name is none of the closed module's own names
  have outFacts : ∀ q ∈ b.outputs, ∃ o ∈ d.shape.layout.outs,
      q = ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port) := by
    intro q hq
    rw [hbouts] at hq
    obtain ⟨o, ho, he⟩ := List.mem_map.mp hq
    exact ⟨o, ho, he.symm⟩
  refine
    { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_, kinds := ?_, asg := ?_,
      reg := ?_ }
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
    rw [hbi] at hp
    rcases hMinputs p hp with ha | hc | hr
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
    rw [hbouts, List.map_map]
    exact outsNodup
  · -- scalar output ports
    intro q hq
    obtain ⟨o, ho, hqo⟩ := outFacts q hq
    rw [hqo]
    exact Tools.ShippingTextTyped.scalarTy_spec (hoty o ho)
  · -- the statement kinds
    intro st hst
    rcases hsub st hst with h0 | h0
    · rcases hkCM st h0 with ⟨l, r, he⟩ | ⟨o, c', rk, i, iv, he⟩
      · subst he
        rfl
      · subst he
        rfl
    · cases st with
      | inst mn iname conns => rfl
      | _ => exact Tools.ShippingChecksDerived.ff_absurd h0
  · -- the assignments
    intro l r hm
    rcases hsub _ hm with h0 | h0
    · obtain ⟨n, ht, hl⟩ := haCM l r h0
      refine ⟨n, ?_, ?_⟩
      · rw [hweb]
        exact ht
      · rcases hl with hl | ⟨q, hq, h1, h2⟩
        · left
          rw [hweb]
          exact hl
        · right
          have e : b.outputs = (closeMachine d.shape.layout t').outputs :=
            hbouts.trans hoCM.symm
          refine ⟨q, ?_, h1, h2⟩
          rw [e]
          exact hq
    · exact Tools.ShippingChecksDerived.ff_absurd h0
  · -- the registers
    intro o c' rk i iv hm
    rcases hsub _ hm with h0 | h0
    · have ht := hrCM o c' rk i iv h0
      rw [hweb]
      exact ht
    · exact Tools.ShippingChecksDerived.ff_absurd h0

end Tools.ShippingSrm4Core1
