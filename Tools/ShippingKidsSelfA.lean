import Tools.ShippingKidsSelf
import Tools.ShippingParentRanA
import Tools.ShippingParentTailsA
import Tools.ShippingParentDesignA
-- BUILT (unit SR3, par/u-sr3): ks2 exit 0 (ks1 exit 1: missing opens). See REPORT-SR3.md.
-- SCOPE (binding): facts about the checks of the shipped module of a machine with calls on the NEW boundary
-- (`RealChildA O`, `MachineRanA O`); NOT a semantic head and NOT the endpoint `machine_design_svH_full`.
-- Not runtime fit. No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR3: the `core_kids_self` family on `RealChildA` / `MachineRanA` (consumer 3)

Ports of `Tools.ShippingKidsSelf.{core_kids_self_ran, core_kidsPass_deep_ran, core_kidsMaskedN_top_ran}` and of
`Tools.ShippingPortsMatchRaw.core_callConns_ran` (general closing) from `Tools.ShippingMachineRan.MachineRan`
(old `InvW`, `RealChild mref cref`) to `Tools.ShippingParentRanA.MachineRanA O` (children `ChildrenRealA O`,
per-child fact `RealChildA O`, a HISTORY of past synthesis results, not freshness or semantic correctness).
Proofs verbatim except the head (the machine synthesis result is read out of `MachineRanA`) and the callees,
replaced by their PH `_ranA` forms (`core_kids_facts_ranA`, `core_hierGate_anyA`).  `core_kidsPass_deep_ranA` does
not need `hfne` (the gate comes from `core_hierGate_anyA`).

* `core_kids_self_ranA`, `core_kidsPass_deep_ranA`, `core_kidsMaskedN_top_ranA`: from `MachineRanA`.
* `core_kids_selfA`, `core_kidsPass_deepA`, `core_kidsMaskedN_topA`: from a returning core run, by
  `machineRanA_main`.  PREMISES: `O`, `hA`, `T : RefLawsATele` (only through `BodyStepC`/`htr`), the start world
  `JQ O.quiet D₀ w` (+ `CacheInvA` if `D₀ ≠ 0`), `MachineDefines`, and `MachineClosesAtA` (UNRESOLVED PREMISE: the
  machine synthesis does not fall back; no instance is discharged here, the file has none).  `hkidK`/`hkidM` stay
  premises of the per-child checks, as in the old statements. -/

namespace Tools.ShippingKidsSelfA
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
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_callConns` (general closing) over `MachineRanA O`: copy of `Tools.ShippingPortsMatchRaw.core_callConns_ran`
with the children `RealChildA O`. -/
theorem core_callConns_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
      ∃ mc, moduleByName D.modules mn = some mc ∧
        (∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ mc = y.1) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
          (x ∈ b.wires.map (·.name) ∧
            ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
              Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
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
    (core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran).2.1
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
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
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
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[e.1]).1 y ∧ mc = y.1 := by
    intro e he
    obtain ⟨hargs0, hch0, -⟩ := hall e he
    have hk0 : e.1 < d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs0).1
      simpa using this
    obtain ⟨y, hy, hor⟩ := hallC e.1 hk0
    rw [hy] at hch0
    have hyn : y.1.name = child.1.name := by
      simpa only [Option.map_some, Option.some.injEq] using hch0
    rcases hor with hmem | hre
    · rw [Tools.ShippingChildInv.nomem_tag hnomem hk0] at hmem
      cases hmem
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

set_option maxHeartbeats 4000000 in
/-- `core_kids_self` over `MachineRanA O`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_kids_self` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_kids_self_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
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
  rcases hor' with hmem | hre
  · rw [Tools.ShippingChildInv.nomem_tag hnomem hk'] at hmem
    cases hmem
  · exact ⟨k, hk', y, hre, hor, hself y hy⟩

set_option maxHeartbeats 4000000 in
/-- `core_kidsPass_deep` over `MachineRanA O`:
the proof of the built theorem, COPIED from `Tools.ShippingKidsSelf` with `ran` over `MachineRanA O` and every callee of the chain by its `_ranA` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the `…A` theorem below is its instance at `MachineRanA` from a returning core run
(`Tools.ShippingParentRanA.machineRanA_main`). -/
theorem core_kidsPass_deep_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (n : Nat)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ ms : List Sparkle.IR.AST.Module,
        moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
        Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
          ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true := by
  obtain ⟨-, hbody', -, hresM, -, -⟩ :=
    core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  have hselfD := core_kids_self_ranA O d ok hbody hC hslots hdomB hins hnomem ran
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    core_hierGate_anyA O d ok hbody hC hslots hdomB hins outTy hnomem
      hpost ran
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    have hm : Stmt.inst mn iname conns ∈ b.body :=
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp hst
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    have hmem : mc ∈ D.modules := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidK k hk y hre D.modules hs1 hs2).1
    · exact (hkidK k hk y hre D.modules hs1 hs2).2 mc hin
  | _ => rfl

set_option maxHeartbeats 4000000 in
/-- `core_kidsMaskedN_top` over `MachineRanA O`:
the proof of the built theorem, COPIED from `Tools.ShippingKidsSelf` with `ran` over `MachineRanA O` and every callee of the chain by its `_ranA` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the `…A` theorem below is its instance at `MachineRanA` from a returning core run
(`Tools.ShippingParentRanA.machineRanA_main`). -/
theorem core_kidsMaskedN_top_ranA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidM : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  have hconn := core_callConns_ranA O d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hpost ran
  refine Tools.ShippingChecksMasked.kidsMaskedN_of fun mn iname conns hm => ?_
  obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, -⟩ := hconn mn iname conns hm
  refine ⟨mc, hmc, ?_⟩
  rw [hmcy]
  exact hkidM k hk y hre

open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildDepthC
open Tools.ShippingChildFresh

set_option maxHeartbeats 4000000 in
/-- **`core_kids_self` on the new boundary**: for a returning core run of a machine with calls, every module of the
run's design is a `RealChildA` child's module or a module of its design, and the design resolves them to themselves.
PREMISES: `O`, `hA`, `T`, start world, `MachineDefines`, `MachineClosesAtA` (UNRESOLVED). A history, not runtime fit. -/
theorem core_kids_selfA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (T : RefLawsATele O.quiet mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 :=
  core_kids_self_ranA O d ok hbody hC hslots hdomB hins hnomem
    (machineRanA_main O hA T hcore entry closes hw hc)

set_option maxHeartbeats 4000000 in
/-- **`core_kidsPass_deep` on the new boundary** (no `hfne`; either closing). Same premises as `core_kids_selfA`
plus the per-child check `hkidK`. -/
theorem core_kidsPass_deepA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (T : RefLawsATele O.quiet mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (n : Nat)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      ∀ ms : List Sparkle.IR.AST.Module,
        moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
        Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
          ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    {b : Sparkle.IR.AST.Module}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
 :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true :=
  core_kidsPass_deep_ranA O d ok hbody hC hslots hdomB hins outTy hnomem n hkidK hpost
    (machineRanA_main O hA T hcore entry closes hw hc)

set_option maxHeartbeats 4000000 in
/-- **`core_kidsMaskedN_top` on the new boundary** (general closing, `hfne`). Same premises as `core_kids_selfA`
plus the per-child masked outputs `hkidM`. -/
theorem core_kidsMaskedN_topA (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (T : RefLawsATele O.quiet mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidM : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    {b : Sparkle.IR.AST.Module}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
 :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  core_kidsMaskedN_top_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidM hpost
    (machineRanA_main O hA T hcore entry closes hw hc)

end Tools.ShippingKidsSelfA

#print axioms Tools.ShippingKidsSelfA.core_kids_selfA
#print axioms Tools.ShippingKidsSelfA.core_kidsPass_deepA
#print axioms Tools.ShippingKidsSelfA.core_kidsMaskedN_topA
