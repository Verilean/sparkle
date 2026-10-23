import Tests.Compiler.Srm7RankTest
import Tools.ShippingSrm12Corr
-- BUILT (unit SRM12): dev runs a5 (Corr + CorrTest) exit 0, a8 (audit) exit 0; the final-SHA rebuild is in REPORT-SRM12.md.
-- SCOPE: the edge correspondence (`Tools/ShippingSrm12Corr.lean`) for `topshareM` (graph `gM`, SRM7) and `topshareQ` (graph `gQ`): every module of the run (`b`, its optimised form, every module of `D.modules`) satisfies `ModCorr`,
-- i.e. its instance statements and the graph's call entries (memory-origin and ordinary entries kept apart) correspond in both directions; and the per-instance-statement rank facts (`rkOf g F mn = some r'`, `r' < r`) that follow from SRM7's computed ranks.
-- The generic part is `ran_designCorr`/`memCallee_childCorr`/`childCorr_noInst`; the per-design part is the instantiation below (callee tables: `wrapM_kids`, `wrapM_memCallee`, `leafKid_ifaceP`, ...).
-- PREMISES of every theorem here are those of SRM5's `topshareM_hcheck`/`topshareQ_hcheck` MINUS the rank table: `O`, `T`, `hA`, the `MachineDefines` of the machines (and `hcl` for the plain leaf), `hcore`, `hpost`, `hw`.
-- NOT claimed: an arbitrary graph, arbitrary designs, that other designs are covered, the endpoint.  `RealChildA` is a history of past synthesis results.  No `sorry`, no `axiom`, no `native_decide`.
set_option autoImplicit false
namespace Tests.Compiler.Srm12CorrTest
open Lean Meta
open Tools.ShippingSrm7Rank Tools.ShippingSrm12Corr Sparkle.Compiler.MachInstOrigin
open Sparkle.Compiler.MachMemory (memChildName memModule)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm7RankTest
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingMemCloses Tools.ShippingMachineAuto
open Tools.ShippingInstTagged (originAt)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## graph entries are the machine data's `instTagged` -/

theorem gM_top_callees : callees gM ``topshareM = some topshareM.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gM]
theorem gM_wrap_callees : callees gM ``wrapM = some wrapM.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gM]
theorem gM_wrap3_callees : callees gM ``wrapM3 = some wrapM3.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gM]
theorem gM_leaf_callees : callees gM ``leafM = some leafM.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gM]
theorem gQ_top_callees : callees gQ ``topshareQ = some topshareQ.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gQ]
theorem gQ_wrapP_callees : callees gQ ``wrapP = some wrapP.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gQ]
theorem gQ_wrapQ_callees : callees gQ ``wrapQ = some wrapQ.machineData.shape.instTagged := by
  first | rfl | decide | simp [callees, gQ]
theorem gQ_leaf_callees : callees gQ ``leafP = some [] := by
  first | rfl | decide | simp [callees, gQ]

/-! ## `topshareM`: callees `leafM`, `wrapM`, `wrapM3` -/

theorem leafM_childCorr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) : ChildCorr gM O ``leafM :=
  memCallee_childCorr O T gM leafM_memCallee (fun _ _ _ k hk y hn _ => (leafM_none_false hk hn).elim)
    (fun k hk hn => (leafM_none_false hk hn).elim) entryL gM_leaf_callees (fun k hk hn => (leafM_none_false hk hn).elim)

theorem wrapM_childCorr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape) : ChildCorr gM O ``wrapM :=
  memCallee_childCorr O T gM wrapM_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun k hk _ => by rw [wrapM_kids k hk]; rfl) entry gM_wrap_callees
    (fun k hk _ => by rw [wrapM_kids k hk]; exact leafM_childCorr O T entryL)

theorem wrapM3_childCorr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) : ChildCorr gM O ``wrapM3 :=
  memCallee_childCorr O T gM wrapM3_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapM3_kids k hk] at hre
      exact leafM_ifaceP (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun k hk _ => by rw [wrapM3_kids k hk]; rfl) entry gM_wrap3_callees
    (fun k hk _ => by rw [wrapM3_kids k hk]; exact leafM_childCorr O T entryL)

/-- **The correspondence for `topshareM`**: the post-processed parent `b`, its optimised form, and every module of the run's design `D` satisfy `ModCorr gM` -/
theorem topshareM_corr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ModCorr gM b ∧ ModCorr gM (checkedOptimize b) ∧ DesignCorr gM D.modules :=
  ran_designCorr O gM topshareM.machineData topshareM_parentData.ok topshareM_parentData.body (nDecl := 4)
    topshareM_parentData.callsOk topshareM_parentData.slots topshareM_parentData.domB topshareM_insts_ne topshareM_fne topshareM_outTy
    hpost (topshareM_ranA O T hA entryL entry₁ entry₂ entry hcore hw) gM_top_callees
    (fun k hk y _ hre => by
      by_cases hk2 : k < 2
      · rw [topshareM_name k hk, if_pos hk2] at hre ⊢
        exact (wrapM_ifaceP O T entryL entry₁ hre).name
      · rw [topshareM_name k hk, if_neg hk2] at hre ⊢
        exact (wrapM3_ifaceP O T entryL entry₂ hre).name)
    (fun k hk _ => by
      by_cases hk2 : k < 2
      · rw [topshareM_name k hk, if_pos hk2]; exact wrapM_childCorr O T entryL entry₁
      · rw [topshareM_name k hk, if_neg hk2]; exact wrapM3_childCorr O T entryL entry₂)

/-! ## `topshareQ`: callees `leafP` (plain), `wrapP`, `wrapQ` -/

theorem leafP_childCorr (O : RefLawsAOps MkRefd mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) :
    ChildCorr gQ O ``leafP :=
  childCorr_noInst O gQ gQ_leaf_callees (fun y hre => ⟨_, _, leafKid_ifaceP O leafP_data hR0 hcl hre⟩)

theorem wrapP_childCorr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape) : ChildCorr gQ O ``wrapP :=
  memCallee_childCorr O T gQ wrapP_memCallee
    (fun m' c' _ k hk y _ hre => by
      rw [wrapP_kids k hk] at hre
      exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre)
    (fun k hk _ => by rw [wrapP_kids k hk]; rfl) entry gQ_wrapP_callees
    (fun k hk _ => by rw [wrapP_kids k hk]; exact leafP_childCorr O hR0 hcl)

theorem wrapQ_childCorr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) : ChildCorr gQ O ``wrapQ :=
  memCallee_childCorr O T gQ wrapQ_memCallee
    (fun m' c' _ k hk y hn hre => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm] at hre
      simp only [wqName, wqNk, wqOuts, wqNames, if_pos hk2]
      exact leafKid_ifaceP (mctx := m') (cctx := c') O leafP_data (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl hre)
    (fun k hk hn => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm]
      simp only [wqName, if_pos hk2])
    entry gQ_wrapQ_callees
    (fun k hk hn => by
      obtain ⟨hk2, hnm⟩ := wrapQ_ord k hk hn
      rw [hnm]
      exact leafP_childCorr O hR0 hcl)

/-- **The correspondence for `topshareQ`** -/
theorem topshareQ_corr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ModCorr gQ b ∧ ModCorr gQ (checkedOptimize b) ∧ DesignCorr gQ D.modules :=
  ran_designCorr O gQ topshareQ.machineData topshareQ_parentData.ok topshareQ_parentData.body (nDecl := 4)
    topshareQ_parentData.callsOk topshareQ_parentData.slots topshareQ_parentData.domB topshareQ_insts_ne topshareQ_fne topshareQ_outTy
    hpost (topshareQ_ranA O T hA hR0 hcl entry₁ entry₂ entry hcore hw) gQ_top_callees
    (fun k hk y _ hre => by
      by_cases hk2 : k < 2
      · rw [topshareQ_name k hk, if_pos hk2] at hre ⊢
        exact (wrapP_ifaceP O T hR0 hcl entry₁ hre).name
      · rw [topshareQ_name k hk, if_neg hk2] at hre ⊢
        exact (wrapQ_ifaceP O T hR0 hcl entry₂ hre).name)
    (fun k hk _ => by
      by_cases hk2 : k < 2
      · rw [topshareQ_name k hk, if_pos hk2]; exact wrapP_childCorr O T hR0 hcl entry₁
      · rw [topshareQ_name k hk, if_neg hk2]; exact wrapQ_childCorr O T hR0 hcl entry₂)

/-! ## Rank facts per instance statement (from SRM7's computed ranks) -/

theorem gM_names : ∀ c ks, callees gM c = some ks →
    c = ``topshareM ∨ c = ``wrapM ∨ c = ``wrapM3 ∨ c = ``leafM := by
  intro c ks h
  have := callees_mem_names gM h
  simpa [gM] using this

theorem gQ_names : ∀ c ks, callees gQ c = some ks →
    c = ``topshareQ ∨ c = ``wrapP ∨ c = ``wrapQ ∨ c = ``leafP := by
  intro c ks h
  have := callees_mem_names gQ h
  simpa [gQ] using this

/-- every module of the correspondence with a declaration name has a computed rank in `gM` -/
theorem gM_rank_of_modCorr {m : Sparkle.IR.AST.Module} (hm : ModCorr gM m) {c : Name}
    (hc : Sparkle.IR.ModuleName.decode m.name = some (Sparkle.IR.ModuleName.Key.decl c)) :
    ∃ r, rkOf gM 4 m.name = some r := by
  obtain ⟨ks, hks, -, -⟩ := hm.2.2 c hc
  have hr : rkOf gM 4 m.name = declRank gM 4 c := by simp only [rkOf, hc]
  rw [hr]
  rcases gM_names c ks hks with rfl | rfl | rfl | rfl
  · exact ⟨_, gM_top⟩
  · exact ⟨_, gM_wrap⟩
  · exact ⟨_, gM_wrap3⟩
  · exact ⟨_, gM_leaf⟩

theorem gQ_rank_of_modCorr {m : Sparkle.IR.AST.Module} (hm : ModCorr gQ m) {c : Name}
    (hc : Sparkle.IR.ModuleName.decode m.name = some (Sparkle.IR.ModuleName.Key.decl c)) :
    ∃ r, rkOf gQ 3 m.name = some r := by
  obtain ⟨ks, hks, -, -⟩ := hm.2.2 c hc
  have hr : rkOf gQ 3 m.name = declRank gQ 3 c := by simp only [rkOf, hc]
  rw [hr]
  rcases gQ_names c ks hks with rfl | rfl | rfl | rfl
  · exact ⟨_, gQ_top⟩
  · exact ⟨_, gQ_wrapP⟩
  · exact ⟨_, gQ_wrapQ⟩
  · exact ⟨_, gQ_leaf⟩

/-- **E4 for `topshareM`**: for every instance statement of every module of the run (`b`, `checkedOptimize b`, `D.modules`) the caller has a computed rank `r`, the target a computed rank `r' < r` -/
theorem inst_rank_of_modCorr_M {ms : List Sparkle.IR.AST.Module} (hms : DesignCorr gM ms) :
    ∀ m ∈ ms, ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body →
      ∃ r r', rkOf gM 4 m.name = some r ∧ rkOf gM 4 mn = some r' ∧ r' < r := by
  intro m hm mn iname conns hin
  have hmc := hms m hm
  rcases hmc.1 with ⟨c, hc⟩ | ⟨cb, aw, dw, hc⟩
  · obtain ⟨r, hr⟩ := gM_rank_of_modCorr hmc hc
    obtain ⟨r', h1, h2⟩ := inst_rank gM 4 hmc hr hin
    exact ⟨r, r', hr, h1, h2⟩
  · exact absurd hin (hmc.2.1 cb aw dw hc mn iname conns)

theorem inst_rank_of_modCorr_Q {ms : List Sparkle.IR.AST.Module} (hms : DesignCorr gQ ms) :
    ∀ m ∈ ms, ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body →
      ∃ r r', rkOf gQ 3 m.name = some r ∧ rkOf gQ 3 mn = some r' ∧ r' < r := by
  intro m hm mn iname conns hin
  have hmc := hms m hm
  rcases hmc.1 with ⟨c, hc⟩ | ⟨cb, aw, dw, hc⟩
  · obtain ⟨r, hr⟩ := gQ_rank_of_modCorr hmc hc
    obtain ⟨r', h1, h2⟩ := inst_rank gQ 3 hmc hr hin
    exact ⟨r, r', hr, h1, h2⟩
  · exact absurd hin (hmc.2.1 cb aw dw hc mn iname conns)

/-- **E4 for `topshareM`, end to end**: the rank facts SRM5/SRM8 need for EVERY instance statement of the run's modules (the optimised parent and `D.modules`), from the correspondence and SRM7's computed ranks -/
theorem topshareM_inst_ranks (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ∀ m ∈ checkedOptimize b :: D.modules, ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body →
      ∃ r r', rkOf gM 4 m.name = some r ∧ rkOf gM 4 mn = some r' ∧ r' < r := by
  obtain ⟨-, hopt, hD⟩ := topshareM_corr O T hA entryL entry₁ entry₂ entry hcore hpost hw
  refine inst_rank_of_modCorr_M (ms := checkedOptimize b :: D.modules) ?_
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hopt
  · exact hD m hm

/-- **E4 for `topshareQ`, end to end** -/
theorem topshareQ_inst_ranks (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    ∀ m ∈ checkedOptimize b :: D.modules, ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body →
      ∃ r r', rkOf gQ 3 m.name = some r ∧ rkOf gQ 3 mn = some r' ∧ r' < r := by
  obtain ⟨-, hopt, hD⟩ := topshareQ_corr O T hA hR0 hcl entry₁ entry₂ entry hcore hpost hw
  refine inst_rank_of_modCorr_Q (ms := checkedOptimize b :: D.modules) ?_
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hopt
  · exact hD m hm

end Tests.Compiler.Srm12CorrTest

#print axioms Tests.Compiler.Srm12CorrTest.topshareM_corr
#print axioms Tests.Compiler.Srm12CorrTest.topshareQ_corr
#print axioms Tests.Compiler.Srm12CorrTest.topshareM_inst_ranks
#print axioms Tests.Compiler.Srm12CorrTest.topshareQ_inst_ranks
