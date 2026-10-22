import Tools.ShippingSeqChildDeepIfacePA
import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSeqChildDeepMaskedA
import Tools.ShippingCallsMemPinned
import Tools.ShippingMemClosesKids
-- BUILT (unit SRM3): b4 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM3.md.
-- SCOPE (binding): the interface `ChildIfaceP` (`Tools.ShippingMemCloses.ChildIfaceP`) of the served result of a `RealChildA O c y` of a machine WITH calls, where some call
-- entries are MEMORY entries (the origin builds the module, `InstOrigin.child? = some md`) and the others are `RealChildA` callees — WITHOUT `hnomem`.
-- It is the memory-aware A-form of `core_kids_facts_ranA` / `core_outsIn_ranA` / `core_calls_portsG_ranA` / `core_inPorts_ranA` / `deepChild_ifaceP`: the statements and proofs are
-- COPIES of those with `hnomem` removed and the design clause of `core_kids_facts_ranAM` stating `KidTA` (the origin's built module OR a `RealChildA`) for the kid a design module comes
-- from.  Nothing here is routed through the old-form `RealChild` / `MachineRan` / `MachineClosesAt` or through `kidsChild_of_realM`.
-- The memory kids are handled by the built `memIface` / `mem_design` / `mem_noInst` (the memory module is a fixed built module, no reflection).
-- PREMISES kept (named): `hgk` / `hsep` for the `RealChildA` kids (as in `deepChild_ifaceP`), `hmem` (the memory module's name is in `names` and is not the parent's), `entry`, `closes`.
-- `RealChildA` is a history of past synthesis results, not freshness, not runtime fit.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.

namespace Tools.ShippingSrm3Iface
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
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingSeqChildDeepConsumerA Tools.ShippingSeqChildDeepFactsA
open Tools.ShippingSeqChildDeepKidFactsA Tools.ShippingSeqChildDeepIfacePA
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)
open Tools.ShippingDesignWithG (designWith_modules)
open Tools.ShippingPortWidthsPure Tools.ShippingCallsMemA Tools.ShippingMemCloses
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A kid built by an origin is the memory module of a memory origin. -/
theorem origin_mem_of_child {o : InstOrigin} {y : Res} (h : o.child? = some y) :
    ∃ cb aw dw, o = InstOrigin.mem cb aw dw ∧ y = memModule cb aw dw := by
  cases o with
  | ord => simp [InstOrigin.child?] at h
  | field i => simp [InstOrigin.child?] at h
  | mem cb aw dw => exact ⟨cb, aw, dw, rfl, (Option.some.inj h).symm⟩

/-- `core_kids_facts_ranA` WITHOUT `hnomem` (needs `hfne`): the design clause states `KidTA` (the origin's built module or a `RealChildA`) for the kid a design module comes from; `MemChildren` of the closing
identifies the kid of an origin that builds a module with that module. -/
theorem core_kids_facts_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ b.body = M.body ∧ b.outputs = M.outputs ∧
    (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
    (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      ∀ g2 ∈ y.1 :: y.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
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
  obtain ⟨-, -, -, -, hcall1, hinst1, -, houtsM, -, -, -, hGinst, hGcall, -, -, hcleanAny, -⟩ :=
    wired
  obtain ⟨hzb, -, hzi, hzo⟩ := hcleanAny outTy
  -- an instance statement of the module names a module of its design
  have hinstD : ∀ mn i conns, Stmt.inst mn i conns ∈ M.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ mc ∈ D.modules ∧ mc.name = mn := by
    intro mn i conns hm
    by_cases hf : d.shape.instFields = []
    · obtain ⟨k, args, mc, -, hfind, -⟩ := hinst1 hf mn i conns hm
      have hfind' := hfind
      unfold moduleByName at hfind'
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind', by simpa using List.find?_some hfind'⟩
    · obtain ⟨args, outs, mc, hcs, hfind, -⟩ := hGinst hf _ hm rfl
      obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      cases he
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind, rfl⟩
  have hhas : Tools.ShippingMachineShipsHier.hasInst M := by
    have hk0 : 0 < d.shape.insts.length := List.length_pos_iff.mpr hins
    by_cases hf : d.shape.instFields = []
    · obtain ⟨args, mc, st, -, hst, -, hcs⟩ := hcall1 hf 0 hk0
      obtain ⟨_, _, _, iname, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
    · obtain ⟨st, hst, args, outs, mc, hcs, -⟩ := hGcall hf 0 hk0
      obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
  have hbeq : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M := by
    rcases hpost with h | h
    · exact h
    · rw [h]
      refine Tools.ShippingMachineDepthRun.mergeChecked_of_hasInst ?_
      obtain ⟨mn, i, conns, hm⟩ := hhas
      exact ⟨mn, i, conns, by rw [hzb]; exact hm⟩
  have hbody' : b.body = M.body := by rw [hbeq, hzb]
  have hbout : b.outputs = M.outputs := by rw [hbeq, hzo]
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  have hMC : MemChildren d.shape children := by
    rcases hcc with ⟨hfe, -⟩ | ⟨-, -, h⟩
    · exact absurd hfe hfne
    · exact h
  -- the design: the join of the children
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hnames := Tools.ShippingChecksDepth.visited_name (children := children) hd0
  -- the closed machine assigns its outputs, and so does the module
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hMA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    refine Tools.ShippingChecksDerived2.outsAssigned_of_assigned fun p hp => ?_
    have hp2 : p ∈ (closeMachine d.shape.layout t').outputs := by
      rw [closeMachine_outputs hpw']
      rw [houtsM] at hp
      exact hp
    obtain ⟨r, hr⟩ := Tools.ShippingChecksDerived3.closeMachine_outs_assigned hpw' p hp2
    exact ⟨r, hperm.subset (List.mem_append_left _ hr)⟩
  refine ⟨hMname.trans hname0, hbody', hbout,
    fun mn i conns hm => (hinstD mn i conns hm).imp fun _ h => h.1, ?_,
    Tools.ShippingChecksDerived3.outsAssigned_congr hbody' hbout hMA⟩
  intro g hg
  rw [hDeq] at hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  have hk' : k < d.shape.insts.length := by
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨y', hy', hor'⟩ := hall k hk'
  rw [hk] at hy'
  cases hy'
  have hkid : KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y := by
    cases hc : (originAt d.shape k).child? with
    | some z =>
      have e := hMC k hk' z hc
      rw [hk] at e
      cases e
      exact Or.inl hc
    | none =>
      rcases hor' with hmem | hre
      · exact absurd (hmem.symm.trans hc) (fun h => by cases h)
      · exact Or.inr ⟨hc, hre⟩
  refine ⟨k, hk', y, hkid, hor, fun g2 hg2 => ?_⟩
  · rw [hDeq]
    refine hnames g2 (mem_visited.mpr ⟨y, hy, ?_⟩)
    rcases List.mem_cons.mp hg2 with h | h
    · exact Or.inl h
    · exact Or.inr h



/-- **`outsIn` of the served module over `MachineRanA O`**: an output port is no argument port and not `clk`/`rst`. -/
theorem core_outsIn_ranAM (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ p ∈ b.outputs, (∀ q ∈ inPortsOf b, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
  have hkf := core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy
    hpost ran
  have hbo : b.outputs = M.outputs := hkf.2.2.1
  have hbi : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
  obtain ⟨tenv, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
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
  obtain ⟨-, -, -, houtIn, -, -⟩ :=
    Tools.ShippingMachineDepthChild.calls_ports wired hlenIds hsl (fun o ho => (outsOk o ho).2)
      kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, -, -, -, -, -, houtsM, -, -, -, -, -, -, -, hcleanAny, -, -⟩ := wired
  have hbouts : b.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := hbo.trans houtsM
  intro p hp
  have hpo : p.name ∈ M.outputs.map (·.name) := by
    rw [← hbo]
    exact List.mem_map_of_mem hp
  have hnotIn := houtIn p.name hpo
  have hp' := hp
  rw [hbouts] at hp'
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp'
  refine ⟨fun q hq eq => hnotIn ?_, ?_, ?_⟩
  · unfold inPortsOf at hq
    rw [hbi] at hq
    rw [← eq]
    exact List.mem_map_of_mem (List.mem_filter.mp hq).1
  · rw [← e]
    exact (outName_ne_clk (outsOk o ho).2).1
  · rw [← e]
    exact (outName_ne_clk (outsOk o ho).2).2



theorem core_calls_portsG_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots ≠ [])
    -- the argument split (the data conditions of `kidsChild_iface`)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    CallsPorts c d kD b ∧ (∀ p ∈ b.outputs, p.name ≠ "clk" ∧ p.name ≠ "rst") := by
  -- the body, the output ports, the inputs and the wires of the full
  -- entry's module are the raw module's
  have hkf := core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy
    hpost ran
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
  obtain ⟨tenv, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  -- the general closing
  have hG : closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀) = some (M, D) := by
    rcases hcc with ⟨hfe, -⟩ | ⟨-, hG, -⟩
    · exact absurd hfe hfne
    · exact hG
  obtain ⟨hMw, -, -, L, hLinst, hperm, -, -, -, -, -, -, -⟩ := hcc.some
  -- the masked outputs of the closed machine
  have hMask := Tools.ShippingClosedMasked.closedBody_masked_of_run d ok hbody hC hslots hdomB
    run hcl
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
  -- the raw module's wiring: its outputs, its argument ports, its cleanup
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, hargP, -⟩ :=
    Tools.ShippingMachineDepthChild.calls_ports wired hlenIds hsl (fun o ho => (outsOk o ho).2)
      kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, -, -, -, -, -, houtsM, -, -, -, -, -, -, -, hcleanAny, -, -⟩ := wired
  obtain ⟨-, hzw, -, -⟩ := hcleanAny outTy
  -- the `let`-closed transition and the closed machine
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hfrCM, -, -, -, -, -, -, -⟩ :=
    Tools.ShippingCloseMachineTyped.closeMachine_typed (lay := d.shape.layout) hbodyc typedc
      namedc namesc inWc inNdc wNdc slotsc
      (fun f hf => by rw [hcoreW]; exact hfit f hf)
      (fun o ho => by rw [hcoreW]; exact houtfit o ho) outsOk outTy
  -- the wire table of the full entry's module is the closed machine's
  have hweb : Tools.ShippingEntrySoundness.weOf b =
      Tools.ShippingEntrySoundness.weOf (closeMachine d.shape.layout t') :=
    ((Tools.ShippingRegisterSoundness.weOf_congr_wires hbw).trans hzw).trans
      (Tools.ShippingRegisterSoundness.weOf_congr_wires hMw)
  have hbouts : b.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := hbo.trans houtsM
  -- the closing keeps a subset of the inputs of the closed machine with the
  -- clock and the reset `withClockFor` may append
  obtain ⟨outWs, -, hMin⟩ := Tools.ShippingMachineInstG.closeInstsG_inputs hG
  obtain ⟨hcm0, hcm1⟩ :=
    closeMachine_inputs (t := t') (lay := d.shape.layout) hbodyc
  have hinP : inPortsOf b = machPorts c ids cache (d.bsIn.take kD) := by
    unfold inPortsOf
    rw [hbi]
    exact hargP
  refine ⟨({ outs := hbouts, masked := ?_, args := ⟨ids, cache, hlenIds, hinP⟩, argW := ?_, pos := hposv } : CallsPorts c d kD b), ?_⟩
  · -- the masked outputs
    intro p hp
    rw [hbouts] at hp
    obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
    rw [← e, hbb]
    exact Tools.ShippingChildMapCongr.outMaskedB_perm_insts hLinst hperm
      (hMask _ o ho (outTy o ho))
  · -- an argument port's width in the wire table
    intro p hp
    have hp' : p ∈ M.inputs.filter (fun p => p.name != "clk" && p.name != "rst") := by
      unfold inPortsOf at hp
      rw [hbi] at hp
      exact hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp'
    have hp3 : (p.name != "clk" && p.name != "rst") = true := hp2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp3
    rw [hMin] at hp1
    have hpw : p ∈ (withClockFor children (closeMachine d.shape.layout t')).inputs :=
      (List.mem_filter.mp hp1).1
    have hpc : p ∈ (closeMachine d.shape.layout t').inputs := by
      rcases Tools.ShippingMachineInstG.withClockFor_inputs children
        (closeMachine d.shape.layout t') with e | ⟨e, -⟩
      · rw [e] at hpw
        exact hpw
      · rw [e] at hpw
        rcases List.mem_append.mp hpw with h | h
        · exact h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with h | h
          · exact absurd (congrArg Sparkle.IR.AST.Port.name h) hp3.1
          · exact absurd (congrArg Sparkle.IR.AST.Port.name h) hp3.2
    have hpt : p ∈ t'.inputs := by
      cases hs : d.shape.layout.slots.isEmpty with
      | true =>
        rw [hcm0 hs] at hpc
        exact List.mem_of_mem_take hpc
      | false =>
        rw [hcm1 hs] at hpc
        rcases List.mem_append.mp hpc with h | h
        · exact List.mem_of_mem_take h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with rfl | rfl
          · exact absurd rfl hp3.1
          · exact absurd rfl hp3.2
    have hw0 := weOf_of_port wNdc (inWc p hpt)
    constructor
    · intro hty
      rw [hty] at hw0
      have hw1 : Tools.ShippingEntrySoundness.weOf t' p.name = 1 := hw0
      have hpos1 : 0 < Tools.ShippingEntrySoundness.weOf t' p.name := by
        rw [hw1]
        exact Nat.one_pos
      rw [hweb, hfrCM _ hpos1]
      exact hw1
    · intro k hk hty
      rw [hty] at hw0
      have hw1 : Tools.ShippingEntrySoundness.weOf t' p.name = k := hw0
      have hposk : 0 < Tools.ShippingEntrySoundness.weOf t' p.name := by
        rw [hw1]
        exact hk
      rw [hweb, hfrCM _ hposk]
      exact hw1
  · intro p hp
    rw [hbouts] at hp
    obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
    rw [← e]
    exact outName_ne_clk (outsOk o ho).2


/-- **The argument ports of the served module over `MachineRanA O`**: their number and distinct names. -/
theorem core_inPorts_ranAM (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    (inPortsOf b).length = machNIn d.shape ∧ ((inPortsOf b).map (·.name)).Nodup := by
  have hkf := core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy
    hpost ran
  have hbo : b.outputs = M.outputs := hkf.2.2.1
  have hbi : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact Tools.ShippingOutsExtractedParts.dropZW_inputs M
  obtain ⟨tenv, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
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
  obtain ⟨hnd, -, -, -, hargP, -⟩ :=
    Tools.ShippingMachineDepthChild.calls_ports wired hlenIds hsl (fun o ho => (outsOk o ho).2)
      kD hkD hIlen hSL hSlen hLlen hNIn
  have hip : inPortsOf b = Tools.ShippingMachineCompose.argPorts M := by
    unfold inPortsOf Tools.ShippingMachineCompose.argPorts
    rw [hbi]
  refine ⟨?_, ?_⟩
  · rw [hip, hargP, Tools.ShippingMachineCompose.machPorts_length _ (by
      rw [hlenIds, d.binders_split]; simp only [List.length_append, List.length_take]; omega), hNIn]
  · rw [hip]
    unfold Tools.ShippingMachineCompose.argPorts
    exact hnd.sublist ((List.filter_sublist).map _)



/-- **`ChildIfaceP` of a `RealChildA O c y` of a machine WITH calls**, with the served design `y.2` KEPT (the grandchildren's
modules, names in `names`).  Premises: those of `deepChild_ifaceA'`, the argument-port data of `core_inPorts_ranAM`, `hgk`
(the grandchildren's modules and their instances name `names` only) and `hsep` (name separation). -/
theorem deepChild_ifaceP_M (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (names : List String)
    (hgk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ names ∧
        ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length) (cb : Bool) (aw dw : Nat),
      originAt d.shape k = InstOrigin.mem cb aw dw →
      (memModule cb aw dw).1.name ∈ names ∧ (memModule cb aw dw).1.name ≠ Sparkle.IR.ModuleName.ofDecl c)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingMemCloses.ChildIfaceP (Sparkle.IR.ModuleName.ofDecl c) (machNIn d.shape)
      (d.shape.layout.outs.map (·.name)) names y.1 y.2 := by
  have hgkK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ names ∧
        ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names := by
    intro k hk y' hy' g hg
    rcases hy' with hc | ⟨-, hre⟩
    · obtain ⟨cb, aw, dw, ho, hyy⟩ := origin_mem_of_child hc
      subst hyy
      have hgm : g = (memModule cb aw dw).1 := by
        rcases List.mem_cons.mp hg with e | e
        · exact e
        · exact Tools.ShippingMemKid.mem_design e
      subst hgm
      exact ⟨(hmem k hk cb aw dw ho).1, fun mn i conns hm => absurd hm (Tools.ShippingMemKid.mem_noInst cb aw dw mn i conns)⟩
    · exact hgk k hk y' hre g hg
  have hsepK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c) := by
    intro k hk y' hy' g hg
    rcases hy' with hc | ⟨-, hre⟩
    · obtain ⟨cb, aw, dw, ho, hyy⟩ := origin_mem_of_child hc
      subst hyy
      have hgm : g = (memModule cb aw dw).1 := by
        rcases List.mem_cons.mp hg with e | e
        · exact e
        · exact Tools.ShippingMemKid.mem_design e
      subst hgm
      exact (hmem k hk cb aw dw ho).2
    · exact hsep k hk y' hre g hg
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
    have hw : JQ O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have hc : CacheInvA O (cv w) := fun c r h => cache c r h
    have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
      (closes mctx' cctx' adm) hw (Or.inr hc)
    obtain ⟨hMn, hb, ho, hinst, hreal, -⟩ :=
      core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
    have hdes : y.2.modules = D.modules := by
      refine hdesL ?_
      intro x hx e
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal x hx
      refine hsepK k hk y' hre x ?_ (e.trans hMn)
      rcases hor with heq | hin
      · rw [heq]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hin
    -- the closed machine, its instances, the harness design
    have ran0 := ran
    obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
    rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
    · exact absurd hno hins
    obtain ⟨-, -, -, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
    obtain ⟨hseq0, -, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
    have hall : ∀ s ∈ y.1.body, Sparkle.IR.OptCheck.seqStmtOk s = true ∨ Sparkle.IR.Machine.isInst s = true := by
      intro s hs
      rw [hb] at hs
      rcases List.mem_append.mp (hperm.mem_iff.mpr hs) with h1 | h1
      · exact Or.inl (List.all_eq_true.mp hseq0 s h1)
      · exact Or.inr (List.all_eq_true.mp hLinst s h1)
    have hname : y.1.name = Sparkle.IR.ModuleName.ofDecl c := by
      rcases hpost with e | e
      · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
      · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
    have hcp := (core_calls_portsG_ranAM O d ok hbody hC hslots hdomB hins hfne outTy
      hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran).1
    have houtNames : y.1.outputs.map (·.name) = d.shape.layout.outs.map (·.name) := by
      rw [hcp.outs, List.map_map]; rfl
    have ok' := ok
    simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
    obtain ⟨-, -, -, -, -, -, -, outsNodup, -⟩ := ok'
    have hports := core_inPorts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl kD hkD hIlen hSL hSlen hLlen hNIn
      hpost ran
    have hdesMem : ∀ g ∈ D.modules, g.name ∈ names ∧
        ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names := by
      intro g hg
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal g hg
      refine hgkK k hk y' hre g ?_
      rcases hor with heq | hin
      · rw [heq]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hin
    refine ⟨hname, hports.1, hports.2, houtNames,
      core_outsIn_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran,
      by rw [houtNames]; exact outsNodup,
      (fun cb aw dw hm => by rw [memParams_none_of_kinds hall] at hm; cases hm),
      by rw [hdes, hDeq]; exact (designWith_modules hd0).1,
      (fun g hg => by rw [hdes] at hg; exact (hdesMem g hg).1),
      fun g hg he => ?_, fun g hg mn i conns hm => ?_⟩
    · rw [hdes] at hg
      exfalso
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal g hg
      refine hsepK k hk y' hre g ?_ (he.trans hname)
      rcases hor with heq | hin
      · rw [heq]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hin
    · rcases List.mem_cons.mp hg with e | hin
      · rw [e, hb] at hm
        obtain ⟨mc, hmc⟩ := hinst mn i conns hm
        have hmc' := hmc
        unfold moduleByName at hmc'
        have hmem := List.mem_of_find?_eq_some hmc'
        have hnm : mc.name = mn := by simpa using List.find?_some hmc'
        rw [← hnm]
        exact (hdesMem mc hmem).1
      · rw [hdes] at hin
        exact (hdesMem g hin).2 mn i conns hm


end Tools.ShippingSrm3Iface

#print axioms Tools.ShippingSrm3Iface.core_kids_facts_ranAM
#print axioms Tools.ShippingSrm3Iface.core_outsIn_ranAM
#print axioms Tools.ShippingSrm3Iface.core_calls_portsG_ranAM
#print axioms Tools.ShippingSrm3Iface.core_inPorts_ranAM
#print axioms Tools.ShippingSrm3Iface.deepChild_ifaceP_M
