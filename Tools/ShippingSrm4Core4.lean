import Tools.ShippingParentDesignFA
import Tools.ShippingSrm4Core2
-- BUILT (unit SRM4): c5 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (binding, residue R2): SCRIPTED copies (`scripts/srm4/port_srm4.py`, specs `scripts/srm4/spec*.json`) of `core_callConns_ranA`, `core_portsMatch_raw_ranA`, `core_clk_ranA`, from the A-form originals in `Tools/ShippingParentDesignFA.lean`, with the memory entries of the callee allowed.  The script's changes, all of them:
-- the theorem's name gets the suffix `M`; the binder `hnomem` is removed and `hfne : d.shape.instFields ≠ []` is added after `hins` where the original had none; a call of a copied theorem calls the copy; `RealChildA O (d.shape.insts[k]).1 y` (the kid of
-- call entry `k`) becomes `KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y` (the origin's built module, or a `RealChildA` when the origin builds none); the three lines refuting the memory case of a child (`rw [nomem_tag hnomem …] at hmem; cases hmem`) become
-- `kidTA_ofO` (from `MemChildren` of the closing, taken from the closing's own statement); `set_option maxHeartbeats … in` lines are DROPPED (the copies run at the default budget).  Nothing is routed through the old-form `RealChild` / `MachineRan` / `MachineClosesAt` or `kidsChild_of_realM`.
-- The per-kid facts stay hypotheses over `KidTA`.  `RealChildA` is a history of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingSrm4Core4
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
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA Tools.ShippingSrm4Core1 Tools.ShippingSrm4Core2
open Tools.ShippingInstTagged (originAt)

/-- `core_callConns_ran` over `MachineRanA O` (children `RealChildA O`, `instFields ≠ []`). -/
theorem core_callConns_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        (∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y ∧ mc = y.1) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
          (x ∈ b.wires.map (·.name) ∧
            ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
              Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
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
    have hre := kidTA_ofO hk0 hMC hy hor
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

/-- `core_portsMatch_raw_ran` over `MachineRanA O`. -/
theorem core_portsMatch_raw_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    -- OUTPUT side: the result binder's width is the child's field port's
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    -- OUTPUT side: the child's output ports are resolved by its emitted width map
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1)
    -- INPUT side: the data condition, and (NOT derived) the child's argument
    -- ports' emitted widths
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    -- CLOCK / RESET (NOT derived): one bit in a sequential child ...
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y → isSeqChild y.1 = true →
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
    Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O d ok hbody hC hslots hdomB hins hfne outTy
      hpost ran hon hoty
  have hconn := core_callConns_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
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

/-- `core_clk_ran` over `MachineRanA O`. -/
theorem core_clk_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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

end Tools.ShippingSrm4Core4
