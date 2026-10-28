import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingDesignWithG
import Tools.ShippingMemClosesKids
-- BUILT (unit SR3r): r7 exit 0; #print axioms: propext, Classical.choice, Quot.sound for both theorems.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR3r, step 2: `ChildIfaceP` (the general closing's child interface) of a NON-LEAF child

`Tools.ShippingSeqChildIfaceA.seqChild_of_realA` is leaf-only (`design.modules = []`).  `deepChild_ifaceP` (PROVED) gives, for a
`RealChildA O c y` of a machine WITH calls, `Tools.ShippingMemCloses.ChildIfaceP (ofDecl c) (machNIn d.shape) outs names y.1 y.2`
KEEPING the served design `y.2` (the grandchildren's modules) — it does NOT assume that design empty, and it does NOT conclude
in general that it is non-empty (integrator wording, par/int-r34, per review) and `names` the grandchildren's module names (caller data).
* NAME SEPARATION is `hsep` (no module of a grandchild is named `ofDecl c`), the caller's premise as in `deepChild_ifaceA'`.
* `hgk`: every module of a grandchild's served pair has its name in `names`, and the instances of its body name `names` only
  (caller data; for a leaf grandchild it follows from `seqChild_of_realA`).
* `core_inPorts_ranA` (PROVED): the number of argument ports and their distinct names, a COPY of the prefix of `core_outsIn_ranA`.
* `memParams? y.1 = none`: the closed machine's body is assignments and registers (`closedBody_kinds_of_run`) plus instance
  statements (`CloseCalls`), so no `.memory` statement; the served design's distinct names from `designWith_modules`
  (the harness design has no module).
`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqChildDeepIfacePA
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
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingSeqChildDeepConsumerA Tools.ShippingSeqChildDeepFactsA
open Tools.ShippingSeqChildDeepKidFactsA
open Tools.ShippingDesignWithG (designWith_modules)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The argument ports of the served module over `MachineRanA O`**: their number and distinct names. -/
theorem core_inPorts_ranA (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
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
  have hkf := Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy
    hnomem hpost ran
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

theorem memParams_none_of_kinds {m : Sparkle.IR.AST.Module}
    (h : ∀ s ∈ m.body, Sparkle.IR.OptCheck.seqStmtOk s = true ∨ Sparkle.IR.Machine.isInst s = true) :
    Sparkle.Compiler.MachMemory.memParams? m = none := by
  unfold Sparkle.Compiler.MachMemory.memParams?
  split
  · rename_i heq
    rw [heq] at h
    rcases h _ List.mem_cons_self with h1 | h1 <;> simp [Sparkle.IR.OptCheck.seqStmtOk, Sparkle.IR.Machine.isInst] at h1
  · rfl

set_option maxHeartbeats 4000000 in
/-- **`ChildIfaceP` of a `RealChildA O c y` of a machine WITH calls**, with the served design `y.2` KEPT (the grandchildren's
modules, names in `names`).  Premises: those of `deepChild_ifaceA'`, the argument-port data of `core_inPorts_ranA`, `hgk`
(the grandchildren's modules and their instances name `names` only) and `hsep` (name separation). -/
theorem deepChild_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
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
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingMemCloses.ChildIfaceP (Sparkle.IR.ModuleName.ofDecl c) (machNIn d.shape)
      (d.shape.layout.outs.map (·.name)) names y.1 y.2 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
    have hw : JQ O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have hc : CacheInvA O (cv w) := fun c r h => cache c r h
    have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
      (closes mctx' cctx' adm) hw (Or.inr hc)
    obtain ⟨hMn, hb, ho, hinst, hreal, -⟩ :=
      core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
    have hdes : y.2.modules = D.modules := by
      refine hdesL ?_
      intro x hx e
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal x hx
      refine hsep k hk y' hre x ?_ (e.trans hMn)
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
    have hcp := (Tools.ShippingSeqChildDeepMaskedA.core_calls_portsG_ranA O d ok hbody hC hslots hdomB hins hfne outTy
      hnomem hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran).1
    have houtNames : y.1.outputs.map (·.name) = d.shape.layout.outs.map (·.name) := by
      rw [hcp.outs, List.map_map]; rfl
    have ok' := ok
    simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
    obtain ⟨-, -, -, -, -, -, -, outsNodup, -⟩ := ok'
    have hports := core_inPorts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl kD hkD hIlen hSL hSlen hLlen hNIn
      hpost ran
    have hdesMem : ∀ g ∈ D.modules, g.name ∈ names ∧
        ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names := by
      intro g hg
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal g hg
      refine hgk k hk y' hre g ?_
      rcases hor with heq | hin
      · rw [heq]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hin
    refine ⟨hname, hports.1, hports.2, houtNames,
      core_outsIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran,
      by rw [houtNames]; exact outsNodup,
      (fun cb aw dw hm => by rw [memParams_none_of_kinds hall] at hm; cases hm),
      by rw [hdes, hDeq]; exact (designWith_modules hd0).1,
      (fun g hg => by rw [hdes] at hg; exact (hdesMem g hg).1),
      fun g hg he => ?_, fun g hg mn i conns hm => ?_⟩
    · rw [hdes] at hg
      exfalso
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal g hg
      refine hsep k hk y' hre g ?_ (he.trans hname)
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

end Tools.ShippingSeqChildDeepIfacePA

#print axioms Tools.ShippingSeqChildDeepIfacePA.core_inPorts_ranA
#print axioms Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP
