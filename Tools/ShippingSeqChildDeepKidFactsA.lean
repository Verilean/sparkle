import Tools.ShippingSeqChildDeepKidCheckA
import Tools.ShippingSeqChildDeepMaskedA
-- BUILT (unit SR3q): q1 exit 0; #print axioms: propext, Classical.choice, Quot.sound for all four theorems (q3 ChildVertAuditTest exit 0).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.  Witness `O : RefLawsAOps MkRefd mref cref`, `T : RefLawsATele O.quiet mref cref` (ADDED boundary).

/-! # Unit SR3q: `KidFacts` over `RealChildA` for a NON-leaf child

* `KidFactsA` (DEFINITION, a `Prop` structure): `Tools.ShippingKidFacts.KidFacts` with `RealChild mref cref c y` replaced by
  `RealChildA O c y`; same nine fields, same statements.  The old structure is unchanged.
* `core_outsIn_ranA` (PROVED): the `outsIn` field's content (an output port of the served module is no argument port, not
  `clk`/`rst`) from `MachineRanA O`: the prefix of `core_calls_portsG_ranA`'s proof, COPIED (SR3o's copy discarded `houtIn` of
  `calls_ports`; if either changes, the copies do not follow).
* `deepChild_kidCheckA_loc` (PROVED, step 2): `deepChild_kidCheckA` with the grandchildren's `check` asked at the TWO depths it
  is used at (`n` and `n + 1`) instead of at every depth `m`.  `deepChild_kidCheckA_of_all` re-derives the old `∀ m` premise shape
  as a special case (so the old statement is unchanged and is a consequence of the local one).  The required depths are restricted to the ones
  actually used (`n`, `n + 1`); the local form is DERIVED from the all-depth form (`deepChild_kidCheckA_of_all`); no claim
  of strict strength either way (integrator wording fix, par/int-r33, per review).
* `deepChild_kidFactsA` (PROVED): `KidFactsA O c d.shape.layout.outs (argWidths d kD) (n + 1)` for `RealChildA O c y` of a
  machine WITH calls, from `KidFactsA` of its call entries' callees at depths `n` and `n + 1` (as `GenKid.kidsLo/kidsHi`), the two
  call-width tables, and the data of `core_calls_portsG_ranA`.  Fields: `outsIn` `core_outsIn_ranA`; `outTys`/`inW` `CallsPorts`;
  `portsIn` `core_closed_typedIn_ranA`; `clk` `core_clk_ranA`; `masked` `deepChild_outsMaskedA`; `kidA`/`kidR` `core_kids_facts_ranA`
  with the grandchildren's `kidA`/`kidR`; `check` `deepChild_kidCheckA_loc`.

`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqChildDeepKidFactsA
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`KidFacts` over `RealChildA`**: what a parent's check-free depth chain takes of one callee `c` (the fields and statements
of `Tools.ShippingKidFacts.KidFacts`, with `RealChildA O c y` for `RealChild mref cref c y`).  `RealChildA` is a history of past
synthesis results. -/
structure KidFactsA (O : RefLawsAOps MkRefd mref cref) (c : Name) (outs : List OutField)
    (ins : List Nat) (n : Nat) : Prop where
  outsIn : ∀ (y : Res), RealChildA O c y →
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst"
  outTys : ∀ (y : Res), RealChildA O c y →
    Tools.ShippingChildIfaceTy.ChildOutTys outs y.1
  kidA : ∀ (y : Res), RealChildA O c y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (y : Res), RealChildA O c y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn
  masked : ∀ (y : Res), RealChildA O c y →
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true
  portsIn : ∀ (y : Res), RealChildA O c y → Tools.ShippingLeafTyped.PortsIn y.1
  inW : ∀ (y : Res), RealChildA O c y →
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
      ∃ wd, ins[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd
  clk : ∀ (y : Res), RealChildA O c y → isSeqChild y.1 = true →
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1
  check : ∀ (y : Res), RealChildA O c y →
    ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y.1.name = some y.1 →
      (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true

set_option maxHeartbeats 4000000 in
/-- **`outsIn` of the served module over `MachineRanA O`**: an output port is no argument port and not `clk`/`rst`. -/
theorem core_outsIn_ranA (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    ∀ p ∈ b.outputs, (∀ q ∈ inPortsOf b, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
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


set_option maxHeartbeats 4000000 in
/-- **Step 2: `deepChild_kidCheckA` with the grandchildren's `check` at the two depths it uses** (`hLo` at `n`, `hHi` at
`n + 1`) instead of at every depth `m`.  Same conclusion as `deepChild_kidCheckA`. -/
theorem deepChild_kidCheckA_loc (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1)
    {kidIns : Nat → List Nat} (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ (j : Nat) (q : Port), (inPortsOf y'.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y'.1 q.name = wd)
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → isSeqChild y'.1 = true →
      Tools.ShippingDesignSV.weS y'.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y'.1 "rst" = 1)
    (n : Nat)
    (hLo : (∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y'.1 = true ∧
        ∀ g ∈ y'.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true))
    (hHi : (∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) y'.1 = true ∧
        ∀ g ∈ y'.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) g = true))
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) (ms : List Sparkle.IR.AST.Module)
    (_hy1 : moduleByName ms y.1.name = some y.1)
    (hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) g = true := by
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    deepChild_ranA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  have hmsD : ∀ g ∈ D.modules, moduleByName ms g.name = some g := fun g hg =>
    hy2 g (by rw [hdes]; exact hg)
  refine ⟨?_, ?_⟩
  · exact (Tools.ShippingGenKid.kidCheck_succ (childMap ms) n y.1).trans
      (Tools.ShippingSeqChildDeepKidCheckA.kids_designCheck_inA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
        hkidP hkidW hkidT hargs hkidIn hkidClk n hLo hpost ran hon hoty ms hmsD)
  · intro g hg
    rw [hdes] at hg
    obtain ⟨k, hk, y', hre, hor, hs1, hs2⟩ := core_kids_self_ranA O d ok hbody hC hslots hdomB hins hnomem ran g hg
    have hz1 : moduleByName ms y'.1.name = some y'.1 :=
      hmsD y'.1 (Tools.ShippingHierPremisesBase.moduleByName_mem hs1).1
    have hz2 : ∀ g2 ∈ y'.2.modules, moduleByName ms g2.name = some g2 := fun g2 hg2 =>
      hmsD g2 (Tools.ShippingHierPremisesBase.moduleByName_mem (hs2 g2 hg2)).1
    have hchk := hHi k hk y' hre ms hz1 hz2
    rcases hor with heq | hin
    · rw [heq]
      exact hchk.1
    · exact hchk.2 g hin

set_option maxHeartbeats 4000000 in
/-- The old `∀ m` premise of `deepChild_kidCheckA` gives the local form's two premises (its instances at `n` and `n + 1`), so the
old statement is a special case of `deepChild_kidCheckA_loc`; the converse does not hold (the local form says nothing about the
other depths). -/
theorem deepChild_kidCheckA_of_all (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1)
    {kidIns : Nat → List Nat} (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ (j : Nat) (q : Port), (inPortsOf y'.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y'.1 q.name = wd)
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → isSeqChild y'.1 = true →
      Tools.ShippingDesignSV.weS y'.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y'.1 "rst" = 1)
    (n : Nat)
    (hkidC : ∀ (m : Nat) (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) m y'.1 = true ∧
        ∀ g ∈ y'.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) m g = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) (ms : List Sparkle.IR.AST.Module)
    (hy1 : moduleByName ms y.1.name = some y.1)
    (hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) g = true :=
  deepChild_kidCheckA_loc O T d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hkidP hkidW hkidT hargs hkidIn hkidClk n (hkidC n) (hkidC (n + 1)) hon hoty hsep entry closes h ms hy1 hy2

set_option maxHeartbeats 4000000 in
/-- **`KidFactsA` of a non-leaf child `c` (a machine WITH calls, general closing, a register) at depth `n + 1`**, from
`KidFactsA` of its call entries' callees at depths `n` (`hlo`) and `n + 1` (`hhi`) and the two call-width tables
(`hcw`, `hargs`).  PROVED relative to `O`, `T`, `MachineDefines`/`MachineClosesAtA` of `c` in `AdmCtx` contexts.  The
grandchildren's facts are the caller's (`hlo`, `hhi`). -/
theorem deepChild_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hlo : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsA O (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hhi : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsA O (d.shape.insts[k]).1 (kidOuts k) (kidIns k) (n + 1))
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    : KidFactsA O c d.shape.layout.outs (argWidths d kD) (n + 1) := by
  have hrun : ∀ y : Res, RealChildA O c y →
      ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (M : Sparkle.IR.AST.Module) (D : Design),
        (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
          y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
        y.2.modules = D.modules ∧ MachineRanA O mctx' cctx' c d.shape M D := fun y h =>
    deepChild_ranA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  have hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst" := fun k hk y' hre => (hlo k hk).outsIn y' hre
  have hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1 :=
    fun k hk y' hre => (hlo k hk).portsIn y' hre
  have hkidIn := fun (k : Nat) (hk : k < d.shape.insts.length) (y' : Res) (hre : RealChildA O (d.shape.insts[k]).1 y') =>
    (hlo k hk).inW y' hre
  have hkidClk := fun (k : Nat) (hk : k < d.shape.insts.length) (y' : Res) (hre : RealChildA O (d.shape.insts[k]).1 y') =>
    (hlo k hk).clk y' hre
  have hkidW := Tools.ShippingParentRunFactsA.hkidW_of_dataA O hcw
    (fun k hk y' hre => (hlo k hk).outTys y' hre)
  exact
  { outsIn := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact core_outsIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl kD hkD hIlen hSL hSlen hLlen hNIn
        hpost ran
    outTys := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact ⟨(Tools.ShippingSeqChildDeepMaskedA.core_calls_portsG_ranA O d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran).1.outs⟩
    kidA := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      obtain ⟨-, -, -, -, hreal, hassign⟩ :=
        core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
      refine ⟨hassign, fun g hg => ?_⟩
      rw [hdes] at hg
      obtain ⟨k, hk, y', hre, hor, -⟩ := hreal g hg
      have hA := (hlo k hk).kidA y' hre
      rcases hor with heq | hin
      · rw [heq]
        exact hA.1
      · exact hA.2 g hin
    kidR := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      obtain ⟨-, hb, -, hinst, hreal, -⟩ :=
        core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
      intro g hg mn i conns hm
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [hb] at hm
        obtain ⟨mc, hmc⟩ := hinst mn i conns hm
        obtain ⟨hmem, hname⟩ := Tools.ShippingHierPremisesBase.moduleByName_mem hmc
        exact ⟨mc, by rw [hdes]; exact hmem, hname⟩
      · rw [hdes] at hg
        obtain ⟨k, hk, y', hre, hor, hall⟩ := hreal g hg
        have hg' : g ∈ y'.1 :: y'.2.modules := by
          rcases hor with heq | hin
          · rw [heq]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ hin
        obtain ⟨g2, hg2, hn2⟩ := (hlo k hk).kidR y' hre g hg' mn i conns hm
        obtain ⟨g3, hg3, hn3⟩ := hall g2 (List.mem_cons_of_mem _ hg2)
        exact ⟨g3, by rw [hdes]; exact hg3, hn3.trans hn2⟩
    masked := fun y h =>
      Tools.ShippingSeqChildDeepMaskedA.deepChild_outsMaskedA O T d ok hbody hC hslots hdomB hins hfne outTy hnomem
        hsl kD hkD hIlen hSL hSlen hLlen hNIn hon hoty hsep entry closes h
    portsIn := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact Tools.ShippingLeafTyped.PortsIn.of_typedIn
        (core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran hon hoty)
    inW := fun y h j q hq => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact (Tools.ShippingSeqChildDeepMaskedA.core_calls_portsG_ranA O d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran).1.inWidths
        (core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran hon hoty).wn hq
    clk := fun y h _ => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact Tools.ShippingParentDesignFA.core_clk_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost ran
    check := fun y h ms hy1 hy2 =>
      deepChild_kidCheckA_loc O T d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hkidP hkidW hkidT hargs hkidIn hkidClk n
        (fun k hk y' hre => (hlo k hk).check y' hre) (fun k hk y' hre => (hhi k hk).check y' hre)
        hon hoty hsep entry closes h ms hy1 hy2 }

end Tools.ShippingSeqChildDeepKidFactsA

#print axioms Tools.ShippingSeqChildDeepKidFactsA.core_outsIn_ranA
#print axioms Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidCheckA_loc
#print axioms Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidCheckA_of_all
#print axioms Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA
