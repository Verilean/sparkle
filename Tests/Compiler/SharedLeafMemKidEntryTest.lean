import Tests.Compiler.SharedLeafMemKidRunTest
import Tools.ShippingNmEntry
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit SRM2): the run names and exits are recorded in REPORT-SRM2.md.
-- SCOPE (SRM2, step 2): the memory-aware parent layer of `Tools/ShippingNmGroup.lean` / `Tools/ShippingNmEntry.lean` HAND-APPLIED to the two examples of `Tests/Compiler/SharedLeafMemKidTest.lean`:
--   variant A  `topshareM` = [wrapM, wrapM, wrapM3, wrapM3], both callees call the SAME leaf `leafM` WITH a memory child;
--   variant B  `topshareQ` = [wrapP, wrapP, wrapQ, wrapQ], `wrapP` calls the plain leaf `leafP`, `wrapQ` calls `leafP` AND a memory child.
-- What is applied: `nm_closes0` (`MachineClosesAtStart0` of the parent DERIVED), `nm_machineRun` (`MachineRunJQC` at depth 1), `nm_entry_run` (the parent's own run with `(M, Dg)`, the returned value linked and no
-- parent module in `Dg`), and the miss-then-hit SHARED-LEAF DESIGN CLAUSE `nm_closing` for the pair of callees (the leaf's cache entry is a module of BOTH callee designs).  Data facts of the parent are `decide`d.
-- PREMISES (named per handler): `O`, `T`, `hA`, `MachineDefines` of the parent / callees / leaf, `MachineClosesAtA` of each callee that has callee calls, the interface `ChildIfaceP` of the RealChildA results of each
-- callee WITH a memory child (`ifaceW1` / `ifaceW3` / `ifaceQ`: OPEN, residue R1; for the plain callee `wrapP` it is DERIVED by `leafCallee_ifaceP` and its `MachineClosesAtA` by `leafCallee_closesA`).
-- NOT applied: the interface / `KidFactsA` / `seq_child_runN` / composed trace (the endpoint) of the memory-bearing callees.  The examples do not make the class complete.  `RealChildA` / `JQC` are histories of past
-- synthesis results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.SharedLeafMemKidEntryTest
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest
open Tools.ShippingMemLeafRun Tools.ShippingMemLeafCache Tools.ShippingNmGroup Tools.ShippingNmEntry
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Tools.ShippingSharedLeafHit Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingSharedLeafNL
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingMemCloses Tools.ShippingTopShareRun Tools.ShippingTopShareNoParent


variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## variant A: the parent `topshareM` over `wrapM`, `wrapM3` (shared leaf WITH a memory child) -/

/-- the module names inside a callee's design: the leaf and its memory module -/
def namesM : List String := [Sparkle.IR.ModuleName.ofDecl ``leafM, (memModule false 4 8).1.name]

noncomputable abbrev csM : List NCal :=
  [⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩,
   ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩]

theorem wrapM_agree : Tools.ShippingInstTagged.TagsAgree wrapM.machineData.shape := by first | decide | decide +kernel
theorem wrapM3_agree : Tools.ShippingInstTagged.TagsAgree wrapM3.machineData.shape := by first | decide | decide +kernel
theorem leafM_nomem : memChild? ``leafM = none := by first | rfl | decide
theorem leafM_cG : ``wrapM ∉ leafM.machineData.shape.insts.map (·.1) := wrapM_notin

theorem wrapM_calleeNM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape) :
    CalleeNM O mctx cctx ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ :=
  ⟨wrapM.machine_ok, wrapM.machine_body, ⟨4, wrapM_calls, wrapM_domB⟩, wrapM_slots,
    fun h0 => absurd (congrArg List.length h0) (by decide), fun h0 => absurd (congrArg List.length h0) (by decide),
    fun D' hD' x hx => Or.inr ⟨(wrapM_tags x hx).1, (wrapM_tags x hx).2 ▸ leafM_step O T hA entryL D' hD'⟩,
    fun k hk => Tools.ShippingInstTagged.agree_at wrapM_agree hk, wrapM_cne, wrapM_notin, entry, closes⟩

theorem wrapM3_calleeNM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape) :
    CalleeNM O mctx cctx ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ :=
  ⟨wrapM3.machine_ok, wrapM3.machine_body, ⟨4, wrapM3_calls, wrapM3_domB⟩, wrapM3_slots,
    fun h0 => absurd (congrArg List.length h0) (by decide), fun h0 => absurd (congrArg List.length h0) (by decide),
    fun D' hD' x hx => Or.inr ⟨(wrapM3_tags x hx).1, (wrapM3_tags x hx).2 ▸ leafM_step O T hA entryL D' hD'⟩,
    fun k hk => Tools.ShippingInstTagged.agree_at wrapM3_agree hk, wrapM3_cne, wrapM3_notin, entry, closes⟩

theorem topshareM_parentData : NmParentData topshareM.machineData csM ``topshareM 4 := by
  refine ⟨topshareM.machine_ok, topshareM.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem csM_nc : ∀ e ∈ csM, ∀ e' ∈ csM, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs := by
  first | decide | decide +kernel
theorem csM_cd : ∀ e ∈ csM, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ ``topshareM) ∧ ``topshareM ∉ e.Gs := by
  first | decide | decide +kernel

theorem csM_callees (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape) :
    NmCallees O mctx cctx ``topshareM csM :=
  ⟨fun e he => by
    simp only [csM, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact wrapM_calleeNM O T hA entryL entry₁ closes₁
    · exact wrapM3_calleeNM O T hA entryL entry₂ closes₂, csM_nc, csM_cd⟩

theorem csM_iface (O : RefLawsAOps MkRefd mref cref)
    (ifaceW1 : ∀ y : Res, RealChildA O ``wrapM y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape)
        (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2)
    (ifaceW3 : ∀ y : Res, RealChildA O ``wrapM3 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape)
        (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) :
    CalleeIface O csM := by
  intro e he y hy
  simp only [csM, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ifaceW1 y hy
  · exact ifaceW3 y hy

/-- **`MachineClosesAtStart0` of `topshareM` DERIVED** (hand-applied `nm_closes0`). -/
theorem topshareM_closes0 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape)
    (ifaceW1 : ∀ y : Res, RealChildA O ``wrapM y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape)
        (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2)
    (ifaceW3 : ∀ y : Res, RealChildA O ``wrapM3 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape)
        (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape :=
  nm_closes0 O hA topshareM_parentData (csM_callees O T hA entryL entry₁ entry₂ closes₁ closes₂) (csM_iface O ifaceW1 ifaceW3)

/-- **`MachineRunJQC` of `topshareM` at depth 1** (hand-applied `nm_machineRun`). -/
theorem topshareM_machineRun (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape)
    (ifaceW1 : ∀ y : Res, RealChildA O ``wrapM y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape)
        (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2)
    (ifaceW3 : ∀ y : Res, RealChildA O ``wrapM3 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape)
        (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design :=
  nm_machineRun O hA topshareM_parentData (csM_callees O T hA entryL entry₁ entry₂ closes₁ closes₂) (csM_iface O ifaceW1 ifaceW3)
    entryP hw hcore

/-- **The parent's own run of `topshareM`** (hand-applied `nm_entry_run`). -/
theorem topshareM_entry_run (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape)
    (ifaceW1 : ∀ y : Res, RealChildA O ``wrapM y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape)
        (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2)
    (ifaceW3 : ∀ y : Res, RealChildA O ``wrapM3 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape)
        (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = csM.length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < csM.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (csM[j]).c = some y) ∧
      (∀ i (hi : i < csM.length) j (hj : j < csM.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < csM.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (csM[j]).d.shape.insts.length),
          (∃ md, ((csM[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((csM[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((csM[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((csM[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? ((csM[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < csM.length) j (hj : j < csM.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (csM[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (csM[j]).d.shape.insts.length),
          ((csM[i]).d.shape.insts[k₁]).1 = ((csM[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? (((csM[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((csM[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) :=
  nm_entry_run O hA topshareM_parentData (csM_callees O T hA entryL entry₁ entry₂ closes₁ closes₂) (csM_iface O ifaceW1 ifaceW3)
    entryP hw h

/-- **The shared-leaf DESIGN CLAUSE for the pair `wrapM`, `wrapM3`** (hand-applied `nm_closing`): the leaf's cache entry `e` is a module of BOTH callee designs, `CacheCoh` of the end cache. -/
theorem topshareM_shared_leaf (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape)
    {D : Nat} (hD : D ≠ 0) {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w) (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w))
    (h1 : (cv w).get? ``wrapM = none) (h2 : (cv w).get? ``wrapM3 = none)
    (hr : RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules := by
  have hC := csM_callees O T hA entryL entry₁ entry₂ closes₁ closes₂
  obtain ⟨Y, hlen, -, -, hcl', hk', hmd', hcoh, hget, -, -, hshared, -⟩ :=
    nm_closing O hA hD csM hC.K topshareM_parentData.nodup hC.nc topshareM_parentData.names topshareM_parentData.child
      hw hcl hk hmd (by
        intro e he
        simp only [csM, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact h1
        · exact h2) hr
  obtain ⟨y, hy, hg⟩ := hget 0 (by decide)
  obtain ⟨y', hy', hg'⟩ := hget 1 (by decide)
  have hn : ((csM[0]'(by decide)).d.shape.insts[0]'(by first | decide | decide +kernel)).1 = ``leafM := by first | decide | decide +kernel
  have hn' : ((csM[1]'(by decide)).d.shape.insts[0]'(by first | decide | decide +kernel)).1 = ``leafM := by first | decide | decide +kernel
  obtain ⟨z, hz1, hz2, hz⟩ := hshared 0 (by decide) 1 (by decide) y y' hy hy' 0 (by first | decide | decide +kernel) 0
    (by first | decide | decide +kernel) (hn.trans hn'.symm)
  refine ⟨Y, y, y', hy, hy', hg, hg', hcl', hk', hmd', hcoh, ?_⟩
  rcases hz with ⟨e, he, rfl⟩ | ⟨md, -, hm, -⟩
  · rw [hn] at he
    exact ⟨e, he, hz1, hz2⟩
  · rw [hn, leafM_nomem] at hm
    cases hm

/-! ## variant B: the parent `topshareQ` over `wrapP` (plain callee) and `wrapQ` (callee WITH a memory child) -/

def namesP : List String := [Sparkle.IR.ModuleName.ofDecl ``leafP]
def namesQ : List String := [Sparkle.IR.ModuleName.ofDecl ``leafP, (memModule false 4 8).1.name]

noncomputable abbrev csQ : List NCal :=
  [⟨``wrapP, wrapP.machineData, [], namesP⟩, ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩]

theorem wrapP_agree : Tools.ShippingInstTagged.TagsAgree wrapP.machineData.shape := by first | decide | decide +kernel
theorem wrapQ_agree' : Tools.ShippingInstTagged.TagsAgree wrapQ.machineData.shape := wrapQ_agree

/-- the data of the plain callee `wrapP` over the plain leaf `leafP` (decided; the Kary template) -/
theorem wrapP_calleeData : Tools.ShippingQuadLeafGeneric.LeafCalleeData wrapP.machineData leafP.machineData ``wrapP ``leafP 3 := by
  refine ⟨wrapP.machine_ok, wrapP.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem wrapP_calleeNM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) :
    CalleeNM O mctx cctx ⟨``wrapP, wrapP.machineData, [], namesP⟩ :=
  ⟨wrapP.machine_ok, wrapP.machine_body, ⟨3, wrapP_calls, wrapP_domB⟩, wrapP_slots,
    fun h0 => absurd (congrArg List.length h0) (by decide), fun h0 => absurd (congrArg List.length h0) (by decide),
    fun D' hD' x hx => Or.inr ⟨(wrapP_tags x hx).1, (wrapP_tags x hx).2 ▸ leafKid_step_nm O hA (leafP_leafOK hR0 hcl) D' hD'⟩,
    fun k hk => Tools.ShippingInstTagged.agree_at wrapP_agree hk, wrapP_cne, List.not_mem_nil, entry,
    Tools.ShippingQuadLeafGeneric.leafCallee_closesA O T hA leafP_data wrapP_calleeData hR0 hcl⟩

theorem wrapQ_calleeNM (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape) :
    CalleeNM O mctx cctx ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩ :=
  ⟨wrapQ.machine_ok, wrapQ.machine_body, ⟨5, wrapQ_calls, wrapQ_domB⟩, wrapQ_slots,
    fun h0 => absurd (congrArg List.length h0) (by decide), fun h0 => absurd (congrArg List.length h0) (by decide),
    fun D' hD' x hx => (wrapQ_hcalls x hx).elim Or.inl
      (fun h => Or.inr ⟨h.1, h.2 ▸ leafKid_step_nm O hA (leafP_leafOK hR0 hcl) D' hD'⟩),
    fun k hk => Tools.ShippingInstTagged.agree_at wrapQ_agree hk, wrapQ_cne, List.not_mem_nil, entry, closes⟩

theorem topshareQ_parentData : NmParentData topshareQ.machineData csQ ``topshareQ 4 := by
  refine ⟨topshareQ.machine_ok, topshareQ.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem csQ_nc : ∀ e ∈ csQ, ∀ e' ∈ csQ, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs := by
  first | decide | decide +kernel
theorem csQ_cd : ∀ e ∈ csQ, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ ``topshareQ) ∧ ``topshareQ ∉ e.Gs := by
  first | decide | decide +kernel

theorem csQ_callees (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape) :
    NmCallees O mctx cctx ``topshareQ csQ :=
  ⟨fun e he => by
    simp only [csQ, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact wrapP_calleeNM O T hA hR0 hcl entry₁
    · exact wrapQ_calleeNM O hA hR0 hcl entry₂ closes₂, csQ_nc, csQ_cd⟩

theorem csQ_iface (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (ifaceQ : ∀ y : Res, RealChildA O ``wrapQ y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape)
        (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) :
    CalleeIface O csQ := by
  intro e he y hy
  simp only [csQ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact Tools.ShippingQuadLeafGeneric.leafCallee_ifaceP O T hA leafP_data wrapP_calleeData entry₁ hR0 hcl hy
  · exact ifaceQ y hy

/-- **`MachineClosesAtStart0` of `topshareQ` DERIVED** (hand-applied `nm_closes0`; the plain callee's `MachineClosesAtA` and interface are DERIVED, the memory-bearing callee's are premises). -/
theorem topshareQ_closes0 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape)
    (ifaceQ : ∀ y : Res, RealChildA O ``wrapQ y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape)
        (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape :=
  nm_closes0 O hA topshareQ_parentData (csQ_callees O T hA hR0 hcl entry₁ entry₂ closes₂) (csQ_iface O T hA hR0 hcl entry₁ ifaceQ)

/-- **`MachineRunJQC` of `topshareQ` at depth 1** (hand-applied `nm_machineRun`). -/
theorem topshareQ_machineRun (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape)
    (ifaceQ : ∀ y : Res, RealChildA O ``wrapQ y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape)
        (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design} (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design :=
  nm_machineRun O hA topshareQ_parentData (csQ_callees O T hA hR0 hcl entry₁ entry₂ closes₂) (csQ_iface O T hA hR0 hcl entry₁ ifaceQ)
    entryP hw hcore

/-- **The parent's own run of `topshareQ`** (hand-applied `nm_entry_run`). -/
theorem topshareQ_entry_run (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape)
    (ifaceQ : ∀ y : Res, RealChildA O ``wrapQ y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape)
        (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational ``topshareQ) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = csQ.length ∧
      closeLets topshareQ.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareQ.machineData.shape) topshareQ.machineData.shape.insts.length
        topshareQ.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareQ.machineData.shape.insts.map (·.2.1))
        topshareQ.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareQ.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < csQ.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (csQ[j]).c = some y) ∧
      (∀ i (hi : i < csQ.length) j (hj : j < csQ.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < csQ.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (csQ[j]).d.shape.insts.length),
          (∃ md, ((csQ[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((csQ[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((csQ[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((csQ[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? ((csQ[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < csQ.length) j (hj : j < csQ.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (csQ[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (csQ[j]).d.shape.insts.length),
          ((csQ[i]).d.shape.insts[k₁]).1 = ((csQ[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? (((csQ[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((csQ[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) :=
  nm_entry_run O hA topshareQ_parentData (csQ_callees O T hA hR0 hcl entry₁ entry₂ closes₂) (csQ_iface O T hA hR0 hcl entry₁ ifaceQ)
    entryP hw h

/-- **The shared-leaf DESIGN CLAUSE for the pair `wrapP`, `wrapQ`** (hand-applied `nm_closing`): the plain leaf `leafP`'s cache entry is a module of BOTH callee designs (the callee `wrapQ` also holds a memory child). -/
theorem topshareQ_shared_leaf (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl0 : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape)
    {D : Nat} (hD : D ≠ 0) {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w) (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w))
    (h1 : (cv w).get? ``wrapP = none) (h2 : (cv w).get? ``wrapQ = none)
    (hr : RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules := by
  have hC := csQ_callees O T hA hR0 hcl0 entry₁ entry₂ closes₂
  obtain ⟨Y, hlen, -, -, hcl', hk', hmd', hcoh, hget, -, -, hshared, -⟩ :=
    nm_closing O hA hD csQ hC.K topshareQ_parentData.nodup hC.nc topshareQ_parentData.names topshareQ_parentData.child
      hw hcl hk hmd (by
        intro e he
        simp only [csQ, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact h1
        · exact h2) hr
  obtain ⟨y, hy, hg⟩ := hget 0 (by decide)
  obtain ⟨y', hy', hg'⟩ := hget 1 (by decide)
  have hn : ((csQ[0]'(by decide)).d.shape.insts[0]'(by first | decide | decide +kernel)).1 = ``leafP := by first | decide | decide +kernel
  have hn' : ((csQ[1]'(by decide)).d.shape.insts[0]'(by first | decide | decide +kernel)).1 = ``leafP := by first | decide | decide +kernel
  obtain ⟨z, hz1, hz2, hz⟩ := hshared 0 (by decide) 1 (by decide) y y' hy hy' 0 (by first | decide | decide +kernel) 0
    (by first | decide | decide +kernel) (hn.trans hn'.symm)
  refine ⟨Y, y, y', hy, hy', hg, hg', hcl', hk', hmd', hcoh, ?_⟩
  rcases hz with ⟨e, he, rfl⟩ | ⟨md, -, hm, -⟩
  · rw [hn] at he
    exact ⟨e, he, hz1, hz2⟩
  · rw [hn, leafP_nomem] at hm
    cases hm

end Tests.Compiler.SharedLeafMemKidEntryTest

#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_closes0
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_machineRun
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_entry_run
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_shared_leaf
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_closes0
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_machineRun
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_entry_run
#print axioms Tests.Compiler.SharedLeafMemKidEntryTest.topshareQ_shared_leaf

end
