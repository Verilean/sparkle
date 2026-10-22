import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSrm4Core5
import Tools.ShippingMemKidFacts
-- BUILT (unit SRM4): c10 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (binding, residue R2): `KidFactsNC` / `KidFactsTNC` (the facts of a callee's kids WITHOUT the `check` field: `KidFactsA` minus its design-check conjunct, which is UNSATISFIABLE for a design with a memory module at a positive kid depth, see
-- `Tools/ShippingSrm4Check.lean`; `KidFactsTNC` takes the kid of a call ENTRY, `flat` (`FlatOk`) in place of `masked`), the memory module's facts (`memKidTNC_facts`, no depth) and `deepChild_kidFactsNC`: `deepChild_kidFactsA`
-- of `Tools/ShippingSeqChildDeepKidFactsA.lean` with `hnomem` removed, the `hhi` / `check` parts dropped, and the callees of the call entries taken at `KidFactsTNC` (a scripted copy, see the header of `Tools/ShippingSrm4Core1.lean`, followed by the hand edits named here; `hkidW_of_dataAM` is a pure scripted copy).
-- PROVED relative to `O`, `T`, `MachineDefines` / `MachineClosesAtA` of the callee in `AdmCtx` contexts.  OPEN: the `check` field (a height-indexed check).  `RealChildA` is a history of past synthesis results, not freshness or runtime fit.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm4Core6
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
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingSeqChildDeepConsumerA Tools.ShippingSeqChildDeepFactsA
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA Tools.ShippingSrm4Core1 Tools.ShippingSrm4Core2 Tools.ShippingSrm4Core3 Tools.ShippingSrm4Core4 Tools.ShippingSrm4Core5
open Tools.ShippingInstTagged (originAt)


/-- **`KidFacts` over `RealChildA` WITHOUT the `check` field** (`KidFactsA` minus its design-check conjunct, see the header: that field is unsatisfiable for a design with a memory module at a positive kid depth). -/
structure KidFactsNC (O : RefLawsAOps MkRefd mref cref) (c : Name) (outs : List OutField) (ins : List Nat) : Prop where
  outsIn : ∀ (y : Res), RealChildA O c y →
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst"
  outTys : ∀ (y : Res), RealChildA O c y → Tools.ShippingChildIfaceTy.ChildOutTys outs y.1
  kidA : ∀ (y : Res), RealChildA O c y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧ ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (y : Res), RealChildA O c y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → ∃ g2 ∈ y.2.modules, g2.name = mn
  masked : ∀ (y : Res), RealChildA O c y → Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true
  portsIn : ∀ (y : Res), RealChildA O c y → Tools.ShippingLeafTyped.PortsIn y.1
  inW : ∀ (y : Res), RealChildA O c y →
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q → ∃ wd, ins[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd
  clk : ∀ (y : Res), RealChildA O c y → isSeqChild y.1 = true →
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1

/-- **The same facts for the kid of a call ENTRY** (the origin's built module, or `RealChildA` when the origin builds none), with `flat` (`FlatOk`: masked and memory-free, or the built memory module) in place of `masked`. -/
structure KidFactsTNC (O : RefLawsAOps MkRefd mref cref) (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (c : Name) (outs : List OutField) (ins : List Nat) : Prop where
  outsIn : ∀ (y : Res), KidTA O o c y →
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst"
  outTys : ∀ (y : Res), KidTA O o c y → Tools.ShippingChildIfaceTy.ChildOutTys outs y.1
  kidA : ∀ (y : Res), KidTA O o c y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧ ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (y : Res), KidTA O o c y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → ∃ g2 ∈ y.2.modules, g2.name = mn
  flat : ∀ (y : Res), KidTA O o c y → Tools.ShippingMemKid.FlatOk y.1
  portsIn : ∀ (y : Res), KidTA O o c y → Tools.ShippingLeafTyped.PortsIn y.1
  inW : ∀ (y : Res), KidTA O o c y →
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q → ∃ wd, ins[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd
  clk : ∀ (y : Res), KidTA O o c y → isSeqChild y.1 = true →
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1

theorem KidTA.real' {O : RefLawsAOps MkRefd mref cref} {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} {c : Name} {y : Res} (h : KidTA O o c y) (ho : o.child? = none) :
    RealChildA O c y := by
  rcases h with h | ⟨-, h⟩
  · rw [ho] at h; cases h
  · exact h

theorem KidTA.mem' {O : RefLawsAOps MkRefd mref cref} {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} {c : Name} {y md : Res} (h : KidTA O o c y) (ho : o.child? = some md) :
    y = md := by
  rcases h with h | ⟨hn, -⟩
  · rw [ho] at h; exact (Option.some.inj h).symm
  · rw [ho] at hn; cases hn

/-- a callee whose origin builds no module: its `KidFactsNC` are the entry's -/
theorem KidFactsNC.toT {O : RefLawsAOps MkRefd mref cref} {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} {c : Name} {outs : List OutField} {ins : List Nat}
    (h : KidFactsNC O c outs ins) (ho : o.child? = none) : KidFactsTNC O o c outs ins :=
  { outsIn := fun y hy => h.outsIn y (KidTA.real' hy ho)
    outTys := fun y hy => h.outTys y (KidTA.real' hy ho)
    kidA := fun y hy => h.kidA y (KidTA.real' hy ho)
    kidR := fun y hy => h.kidR y (KidTA.real' hy ho)
    flat := fun y hy => Tools.ShippingMemKid.flatOk_of_masked (h.masked y (KidTA.real' hy ho))
    portsIn := fun y hy => h.portsIn y (KidTA.real' hy ho)
    inW := fun y hy => h.inW y (KidTA.real' hy ho)
    clk := fun y hy => h.clk y (KidTA.real' hy ho) }

/-- a memory entry: the built memory module's side of the interface, for every read kind and widths (NO depth: there is no `check`) -/
theorem memKidTNC_facts {O : RefLawsAOps MkRefd mref cref} {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} {c : Name} {cb : Bool} {aw dw : Nat}
    (ho : o.child? = some (Sparkle.Compiler.MachMemory.memModule cb aw dw)) :
    KidFactsTNC O o c (Tools.ShippingMemKid.memOuts dw) (Tools.ShippingMemKid.memIns aw dw) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy; obtain rfl := KidTA.mem' hy ho; exact Tools.ShippingMemKid.mem_outsIn cb aw dw
  · intro y hy; obtain rfl := KidTA.mem' hy ho; exact Tools.ShippingMemKid.mem_outTys cb aw dw
  · intro y hy; obtain rfl := KidTA.mem' hy ho
    refine ⟨Tools.ShippingMemKid.mem_outsAssigned cb aw dw, fun g hg => ?_⟩
    rw [Tools.ShippingMemKid.mem_design hg]; exact Tools.ShippingMemKid.mem_outsAssigned cb aw dw
  · intro y hy; obtain rfl := KidTA.mem' hy ho; exact Tools.ShippingMemKid.mem_kidR cb aw dw
  · intro y hy; obtain rfl := KidTA.mem' hy ho; exact Or.inr ⟨cb, aw, dw, rfl⟩
  · intro y hy; obtain rfl := KidTA.mem' hy ho; exact Tools.ShippingMemKid.mem_portsIn cb aw dw
  · intro y hy; obtain rfl := KidTA.mem' hy ho; exact Tools.ShippingMemKid.mem_inW cb aw dw
  · intro y hy _; obtain rfl := KidTA.mem' hy ho
    exact ⟨(Tools.ShippingMemKid.mem_weS cb aw dw).2.2.2.2.1, (Tools.ShippingMemKid.mem_weS cb aw dw).2.2.2.2.2⟩

/-- `hkidW_of_data` for `RealChildA O` children. -/
theorem hkidW_of_dataAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
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

/-- **`KidFactsNC` of a non-leaf child `c` (a machine WITH calls, general closing, a register) whose call entries may be MEMORY entries** (A-form of `deepChild_kidFactsA` with `hnomem` removed and
WITHOUT the `check` field, see the header): from `KidFactsTNC` of its call entries' callees (`hlo`: the origin's built module or a `RealChildA`) and the two call-width tables (`hcw`, `hargs`).  PROVED relative to
`O`, `T`, `MachineDefines`/`MachineClosesAtA` of `c` in `AdmCtx` contexts.  The grandchildren's facts are the caller's (`hlo`). -/
theorem deepChild_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
    (hlo : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsTNC O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    : KidFactsNC O c d.shape.layout.outs (argWidths d kD) := by
  have hrun : ∀ y : Res, RealChildA O c y →
      ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (M : Sparkle.IR.AST.Module) (D : Design),
        (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
          y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
        y.2.modules = D.modules ∧ MachineRanA O mctx' cctx' c d.shape M D := fun y h =>
    deepChild_ranAM O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes h
  have hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst" := fun k hk y' hre => (hlo k hk).outsIn y' hre
  have hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1 :=
    fun k hk y' hre => (hlo k hk).portsIn y' hre
  have hkidIn := fun (k : Nat) (hk : k < d.shape.insts.length) (y' : Res) (hre : Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y') =>
    (hlo k hk).inW y' hre
  have hkidClk := fun (k : Nat) (hk : k < d.shape.insts.length) (y' : Res) (hre : Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y') =>
    (hlo k hk).clk y' hre
  have hkidW := Tools.ShippingSrm4Core6.hkidW_of_dataAM O hcw
    (fun k hk y' hre => (hlo k hk).outTys y' hre)
  exact
  { outsIn := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact core_outsIn_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl kD hkD hIlen hSL hSlen hLlen hNIn
        hpost ran
    outTys := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact ⟨(Tools.ShippingSrm3Iface.core_calls_portsG_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran).1.outs⟩
    kidA := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      obtain ⟨-, -, -, -, hreal, hassign⟩ :=
        core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
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
        core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
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
      Tools.ShippingSrm4Core5.deepChild_outsMaskedAM O T d ok hbody hC hslots hdomB hins hfne outTy
        hsl kD hkD hIlen hSL hSlen hLlen hNIn hon hoty hsep entry closes h
    portsIn := fun y h => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact Tools.ShippingLeafTyped.PortsIn.of_typedIn
        (core_closed_typedIn_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran hon hoty)
    inW := fun y h j q hq => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact (Tools.ShippingSrm3Iface.core_calls_portsG_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl kD hkD hIlen hSL hSlen hLlen hNIn hpost ran).1.inWidths
        (core_closed_typedIn_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran hon hoty).wn hq
    clk := fun y h _ => by
      obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ := hrun y h
      exact Tools.ShippingSrm4Core4.core_clk_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl hpost ran }
end Tools.ShippingSrm4Core6
