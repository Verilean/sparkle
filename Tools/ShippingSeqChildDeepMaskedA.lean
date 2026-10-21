import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingCallsPortsG
import Tools.ShippingClosedTyped
-- UNBUILT (unit SR3o): see the run names in REPORT-SR3o.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Witness `O : RefLawsAOps MkRefd mref cref`, `T : RefLawsATele O.quiet mref cref` (ADDED boundary).

/-! # Step 1 (unit SR3o): `outsMaskedN y.1` for the NON-leaf child `mid` itself over `RealChildA`

Old route: `GenKid.masked` = `outsMaskedN_of_callsG` applied to `GenKid.ports` (`core_calls_portsG`), `GenKid.typedIn`
(`core_closed_typedIn`), `GenKid.outsIn` (the `clk`/`rst` part, from `kidsChild_of_real`) and `core_conn_refsG`; all stated
over the OLD `ChildBnd`/`MachineClosesAt` boundary.  Here:

* `core_calls_portsG_ranA` (PROVED): `core_calls_portsG`'s proof, COPIED (if that changes, this copy does not follow), with the
  run taken from `MachineRanA O` instead of `machine_run_of_core`; ALSO concludes that no output port of `b` is named
  `clk`/`rst` (the part of `ChildIfaceD.outsIn` that `outsMaskedN_of_callsG` consumes), from the layout's outputs.
* `core_conn_refsG_ranA` (PROVED): `core_conn_refsG` from `core_callConns_ranA` (KidsSelfA).
* `deepChild_outsMaskedA` (PROVED): `outsMaskedN y.1 = true` for `RealChildA O c y` of a machine WITH calls and instance
  fields, from `deepChild_ifaceA'`'s run and the three theorems above.  Extra premises over `deepChild_kidsMaskedA`: the
  argument-split data (`kD`, `hsl`, ...) of `core_calls_portsG`, and the two output-port data conditions `hon`/`hoty`
  of `core_closed_typedIn_ranA`.  No grandchild premise (`hkidM`) is needed.

`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqChildDeepMaskedA
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
open Tools.ShippingPortWidthsPure
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingParentRanA Tools.ShippingKidsSelfA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentTailsA
open Tools.ShippingSeqChildDeepConsumerA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem core_calls_portsG_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
  have hkf := Tools.ShippingParentTailsA.core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy
    hnomem hpost ran
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

set_option maxHeartbeats 4000000 in
/-- **`core_conn_refsG` over `MachineRanA O`.** -/
theorem core_conn_refsG_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x →
        x = "clk" ∨ x = "rst" ∨ x ∈ b.wires.map (·.name) := by
  have hconn := Tools.ShippingKidsSelfA.core_callConns_ranA O d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hpost ran
  intro mn iname conns hst cn hcm x hc2
  obtain ⟨mc, -, -, hall⟩ := hconn mn iname conns hst
  have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [← hc2]
    exact hcm
  rcases hall cn.1 x hcm' with ⟨-, h⟩ | ⟨hxw, -⟩
  · rcases h with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr hxw)

set_option maxHeartbeats 4000000 in
/-- **`outsMaskedN` of the served module of a NON-leaf child** (the `masked` field of `KidFacts`/`GenKid`), over
`RealChildA`.  Minimal consumer: `outsMaskedN_of_callsG`. -/
theorem deepChild_outsMaskedA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, -⟩ :=
    deepChild_ifaceA' O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
    (closes mctx' cctx' adm) hw (Or.inr hc)
  obtain ⟨hP, hO⟩ := core_calls_portsG_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hsl
    kD hkD hIlen hSL hSlen hLlen hNIn hpost ran
  exact Tools.ShippingCallsPortsG.outsMaskedN_of_callsG hP
    (Tools.ShippingParentTailsA.core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy
      hnomem hpost ran hon hoty)
    hO
    (core_conn_refsG_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hpost ran)

end Tools.ShippingSeqChildDeepMaskedA

#print axioms Tools.ShippingSeqChildDeepMaskedA.core_calls_portsG_ranA
#print axioms Tools.ShippingSeqChildDeepMaskedA.core_conn_refsG_ranA
#print axioms Tools.ShippingSeqChildDeepMaskedA.deepChild_outsMaskedA
