import Tools.ShippingParentRanA
import Tools.ShippingParentTailsA
import Tools.ShippingOneOutFacts
import Tools.ShippingHierGateAny
import Tools.ShippingParentDesignA
import Tools.ShippingParentTailsO
-- UNBUILT when written (P-MEM-4 implementation, par/gen2-spec on cd026658). Not built, not elaborated.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # P-MEM-4: `hnomem`-free copies of the DesignA run facts used by the one-output chain

COPIED from `Tools/ShippingParentDesignA.lean` at SHA 48775f38 (scripts/gen2/S4_PMEM4_FREEZE.md §2, approved):
`core_hierGate_anyO` (DesignA:50-94), `core_kidsComb_raw₁O` (:177-199), `core_instNames₁O` (:204-227),
`core_noSelfRead₁O` (:233-262), `core_outsExtracted₁O` (:269-395), `core_rst_anyO` (:402-489), `core_runFactsHO`
(:494-516). `core_closeInstsA` (no memory premise) is used unchanged.

Change rule: the `hnomem` binder is deleted (every other binder in the same order, same conclusion text);
`(core_kids_facts_ranA … hnomem …).2.1` becomes `Tools.ShippingParentTailsO.core_bodyEq_ranO …`; callees are the `O`
copies. Proofs otherwise verbatim. Copies do not follow later changes of their originals. UNBUILT when written. -/

variable {tenv : Lean.Environment}

namespace Tools.ShippingParentDesignO
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
open Tools.ShippingParentTailsO
open Tools.ShippingParentDesignA (core_closeInstsA)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- Copy of `Tools.ShippingParentDesignA.core_hierGate_anyA` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted; `.2.1` of `core_kids_facts_ranA` → `core_bodyEq_ranO`. -/
theorem core_hierGate_anyO (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  have hbody' : b.body = M.body :=
    core_bodyEq_ranO O d ok hbody hC hslots hdomB hins outTy hpost ran
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

set_option maxHeartbeats 4000000 in
/-- Copy of `Tools.ShippingParentDesignA.core_kidsComb_raw₁A` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted; `.2.1` of `core_kids_facts_ranA` → `core_bodyEq_ranO`. -/
theorem core_kidsComb_raw₁O (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingMachineDepthH.kidsComb D.modules b.body = true := by
  have hbody' : b.body = M.body :=
    core_bodyEq_ranO O d ok hbody hC hslots hdomB hins outTy hpost ran
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInstsA O d hins hf ran
  rw [hbody']
  exact Tools.ShippingMachineDepthHR.kidsComb_of_B
    (Tools.ShippingChildServe.closeInsts_kidsComb hI)

set_option maxHeartbeats 4000000 in
/-- Copy of `Tools.ShippingParentDesignA.core_instNames₁A` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted; `.2.1` of `core_kids_facts_ranA` → `core_bodyEq_ranO`. -/
theorem core_instNames₁O (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    (Tools.ShippingHierState.instNames b.body).Nodup := by
  have hbody' : b.body = M.body :=
    core_bodyEq_ranO O d ok hbody hC hslots hdomB hins outTy hpost ran
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInstsA O d hins hf ran
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  rw [hbody']
  exact Tools.ShippingOneOutClose.closeInsts_instNames hI
    (Tools.ShippingOneOutClose.instNames_nil_of_seqOk hseq0)

set_option maxHeartbeats 4000000 in
/-- Copy of `Tools.ShippingParentDesignA.core_noSelfRead₁A` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted; `.2.1` of `core_kids_facts_ranA` → `core_bodyEq_ranO`. -/
theorem core_noSelfRead₁O (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  have hbody' : b.body = M.body :=
    core_bodyEq_ranO O d ok hbody hC hslots hdomB hins outTy hpost ran
  obtain ⟨_, logProf, t, t', d₀, children, run, hcl, hI, hreal⟩ :=
    core_closeInstsA O d hins hf ran
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
/-- Copy of `Tools.ShippingParentDesignA.core_outsExtracted₁A` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted; `.2.1` → `core_bodyEq_ranO`, `core_instOuts_not_assigned_ranA` → `…_ranO`. -/
theorem core_outsExtracted₁O (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  -- the full entry's body is the raw module's; no assignment targets an instance output
  have hbody' : b.body = M.body :=
    core_bodyEq_ranO O d ok hbody hC hslots hdomB hins outTy hpost ran
  have hasg := core_instOuts_not_assigned_ranO O d ok hbody hC hslots hdomB
    hins outTy hpost ran
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
    core_closeInstsA O d hins hf ran
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
/-- Copy of `Tools.ShippingParentDesignA.core_rst_anyA` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted (it was unused). -/
theorem core_rst_anyO (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    "rst" ∈ b.inputs.map (·.name) := by
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
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

set_option maxHeartbeats 4000000 in
/-- Copy of `Tools.ShippingParentDesignA.core_runFactsHA` (P-MEM-4; scripts/gen2/S4_PMEM4_FREEZE.md §2): `hnomem` deleted; the six components are the `O` copies. -/
theorem core_runFactsHO (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hsl : d.shape.layout.slots ≠ []) :
    RunFactsH D.modules b :=
  { gate := core_hierGate_anyO O d ok hbody hC hslots hdomB hins outTy hpost ran
    ndB := core_instNames₁O O d ok hbody hC hslots hdomB hins hf outTy hpost ran
    self := core_noSelfRead₁O O d ok hbody hC hslots hdomB hins hf outTy hpost ran
    outs := core_outsExtracted₁O O d ok hbody hC hslots hdomB hins hf outTy hpost ran
    rst := core_rst_anyO O d ok hbody hC hslots hdomB hins hsl outTy hpost ran
    comb := core_kidsComb_raw₁O O d ok hbody hC hslots hdomB hins hf outTy hpost ran }

end Tools.ShippingParentDesignO
