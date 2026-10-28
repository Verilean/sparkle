import Tools.ShippingSeqChildDeepMaskedA
import Tools.ShippingKidsSelfA
import Tools.ShippingSrm4Core2
-- BUILT (unit SRM4): c5 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (binding, residue R2): SCRIPTED copies (`scripts/srm4/port_srm4.py`, specs `scripts/srm4/spec*.json`) of `core_callConns_ranA` (general closing) and `core_conn_refsG_ranA`, from the A-form originals in `Tools/ShippingKidsSelfA.lean` and `Tools/ShippingSeqChildDeepMaskedA.lean`, with the memory entries of the callee allowed.  The script's changes, all of them:
-- the theorem's name gets the suffix `M`; the binder `hnomem` is removed and `hfne : d.shape.instFields ≠ []` is added after `hins` where the original had none; a call of a copied theorem calls the copy; `RealChildA O (d.shape.insts[k]).1 y` (the kid of
-- call entry `k`) becomes `KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y` (the origin's built module, or a `RealChildA` when the origin builds none); the three lines refuting the memory case of a child (`rw [nomem_tag hnomem …] at hmem; cases hmem`) become
-- `kidTA_ofO` (from `MemChildren` of the closing, taken from the closing's own statement); `set_option maxHeartbeats … in` lines are DROPPED (the copies run at the default budget).  Nothing is routed through the old-form `RealChild` / `MachineRan` / `MachineClosesAt` or `kidsChild_of_realM`.
-- The per-kid facts stay hypotheses over `KidTA`.  `RealChildA` is a history of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingSrm4Core3
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
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingParentDesignA
open Tools.ShippingPortsMatchRaw (callStmtG_conn)
open Tools.ShippingChildBndCore Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
open Tools.ShippingPortWidthsPure
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingParentRanA Tools.ShippingKidsSelfA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentTailsA
open Tools.ShippingSeqChildDeepConsumerA
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA Tools.ShippingSrm4Core1 Tools.ShippingSrm4Core2
open Tools.ShippingInstTagged (originAt)

/-- `core_callConns` (general closing) over `MachineRanA O`: copy of `Tools.ShippingPortsMatchRaw.core_callConns_ran`
with the children `RealChildA O`. -/
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
    (core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
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

/-- **`core_conn_refsG` over `MachineRanA O`.** -/
theorem core_conn_refsG_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
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
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x →
        x = "clk" ∨ x = "rst" ∨ x ∈ b.wires.map (·.name) := by
  have hconn := Tools.ShippingSrm4Core3.core_callConns_ranAM O d ok hbody hC hslots hdomB hins hfne
    outTy hpost ran
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

end Tools.ShippingSrm4Core3
