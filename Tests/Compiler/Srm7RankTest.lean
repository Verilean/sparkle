import Tests.Compiler.Srm5ParentTest
import Tests.Compiler.Srm5ParentQTest
import Tests.Compiler.NonzeroInitParentTest
import Tests.Compiler.NoPortsMemSeqGenNewTest
import Tools.ShippingSrm7Rank
-- BUILT (unit SRM7): dev run s7b4 exit 0 (default heartbeats, no heartbeat option); the final-SHA rebuild is in REPORT-SRM7.md.
-- SCOPE: the computed rank table (`Tools/ShippingSrm7Rank.lean`) applied to the call graphs READ FROM `X.machineData.shape.instTagged` of the generated declarations.
-- (R3) `topshareM`/`topshareQ`: the computed table equals SRM5's `rkM`/`rkQ` on every module name the SRM5 premises query (`rkOf_gM_eq_rkM`, `rkOf_gQ_eq_rkQ`), and `topshareM_hcheck_computed`/`topshareQ_hcheck_computed` are
-- SRM5's `topshareM_hcheck`/`topshareQ_hcheck` with the rank-table premises (`rk`, `hrkmem`, `hrT`, `hrW`, `hrW3`, `hrL`) REPLACED by the computation (the graph is read from the machine data; the equalities `rank = n` are decided).
-- Every other premise of those theorems is unchanged (`O`, `T`, `hA`, `MachineDefines`, `hcore`, `hpost`, `hw`, ...).  `hkidH` is NOT a rank fact: it is the machine-level `*_kidHeight` theorem that SRM5 already proves inside these two theorems.
-- FURTHER EXAMPLES (rank only, no `hcheck`): `seqTwoMem` (flat parent with two sequential children and two memories) and `collMixSame5` (a parent whose two call entries are named alike: one memory, one ordinary).
-- FIXTURES (synthetic graphs): cycle, self call, unresolved callee, duplicate names, fuel exhausted: all REFUSED.
-- NOT claimed: a rank table for arbitrary designs; the graph is read from the machine data of the listed declarations only.
namespace Tests.Compiler.Srm7RankTest
open Lean Meta
open Tools.ShippingSrm7Rank Sparkle.Compiler.MachInstOrigin
open Sparkle.Compiler.MachMemory (memChildName memModule)
open Tests.Compiler.SharedLeafMemKidTest

/-! ## `topshareM` (depth 3) -/

noncomputable def gM : CallGraph :=
  [(``topshareM, topshareM.machineData.shape.instTagged), (``wrapM, wrapM.machineData.shape.instTagged),
   (``wrapM3, wrapM3.machineData.shape.instTagged), (``leafM, leafM.machineData.shape.instTagged)]

theorem gM_inClass : InClass gM 4 ``topshareM = true := by decide
theorem gM_top : declRank gM 4 ``topshareM = some 3 := by decide
theorem gM_wrap : declRank gM 4 ``wrapM = some 2 := by decide
theorem gM_wrap3 : declRank gM 4 ``wrapM3 = some 2 := by decide
theorem gM_leaf : declRank gM 4 ``leafM = some 1 := by decide

/-! ## `topshareQ` (depth 2; the plain leaf has rank 0) -/

noncomputable def gQ : CallGraph :=
  [(``topshareQ, topshareQ.machineData.shape.instTagged), (``wrapP, wrapP.machineData.shape.instTagged),
   (``wrapQ, wrapQ.machineData.shape.instTagged), (``leafP, leafP.machineData.shape.instTagged)]

theorem gQ_inClass : InClass gQ 3 ``topshareQ = true := by decide
theorem gQ_top : declRank gQ 3 ``topshareQ = some 2 := by decide
theorem gQ_wrapP : declRank gQ 3 ``wrapP = some 1 := by decide
theorem gQ_wrapQ : declRank gQ 3 ``wrapQ = some 1 := by decide
theorem gQ_leaf : declRank gQ 3 ``leafP = some 0 := by decide

/-! ## (R3) equal to SRM5's hand-written tables on every queried name -/

open Tests.Compiler.SharedLeafMemKidIfaceTest in
theorem rkOf_gM_eq_rkM :
    (∀ cb aw dw, rkOf gM 4 (memModule cb aw dw).1.name = rkM (memModule cb aw dw).1.name) ∧
    rkOf gM 4 (Sparkle.IR.ModuleName.ofDecl ``leafM) = rkM (Sparkle.IR.ModuleName.ofDecl ``leafM) ∧
    rkOf gM 4 (Sparkle.IR.ModuleName.ofDecl ``wrapM) = rkM (Sparkle.IR.ModuleName.ofDecl ``wrapM) ∧
    rkOf gM 4 (Sparkle.IR.ModuleName.ofDecl ``wrapM3) = rkM (Sparkle.IR.ModuleName.ofDecl ``wrapM3) ∧
    rkOf gM 4 (Sparkle.IR.ModuleName.ofDecl ``topshareM) = rkM (Sparkle.IR.ModuleName.ofDecl ``topshareM) :=
  ⟨fun cb aw dw => (rkOf_mem gM 4 cb aw dw).trans (rkM_mem cb aw dw).symm,
   by rw [rkOf_decl, gM_leaf, rkM_leaf], by rw [rkOf_decl, gM_wrap, rkM_wrap],
   by rw [rkOf_decl, gM_wrap3, rkM_wrap3], by rw [rkOf_decl, gM_top, rkM_top]⟩

open Tests.Compiler.SharedLeafMemKidIfaceTest in
theorem rkOf_gQ_eq_rkQ :
    (∀ cb aw dw, rkOf gQ 3 (memModule cb aw dw).1.name = rkQ (memModule cb aw dw).1.name) ∧
    rkOf gQ 3 (Sparkle.IR.ModuleName.ofDecl ``leafP) = rkQ (Sparkle.IR.ModuleName.ofDecl ``leafP) ∧
    rkOf gQ 3 (Sparkle.IR.ModuleName.ofDecl ``wrapP) = rkQ (Sparkle.IR.ModuleName.ofDecl ``wrapP) ∧
    rkOf gQ 3 (Sparkle.IR.ModuleName.ofDecl ``wrapQ) = rkQ (Sparkle.IR.ModuleName.ofDecl ``wrapQ) ∧
    rkOf gQ 3 (Sparkle.IR.ModuleName.ofDecl ``topshareQ) = rkQ (Sparkle.IR.ModuleName.ofDecl ``topshareQ) :=
  ⟨fun cb aw dw => (rkOf_mem gQ 3 cb aw dw).trans (rkQ_mem cb aw dw).symm,
   by rw [rkOf_decl, gQ_leaf, rkQ_leaf], by rw [rkOf_decl, gQ_wrapP, rkQ_wrapP],
   by rw [rkOf_decl, gQ_wrapQ, rkQ_wrapQ], by rw [rkOf_decl, gQ_top, rkQ_top]⟩

/-! ## the rank premises of SRM5 discharged by the computation -/

section
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm5Height
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidIfaceTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

open Tests.Compiler.SharedLeafMemKidEntryTest in
/-- `topshareM_hcheck` with the rank table COMPUTED from the call graph `gM` (read from the machine data): no rank premise remains -/
theorem topshareM_hcheck_computed (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    hcheck (childMap D.modules) (rkOf gM 4) (f + 3) (checkedOptimize b) = true :=
  topshareM_hcheck O T hA f entryL entry₁ entry₂ entry hcore hpost hw (rkOf gM 4) (rkOf_mem gM 4)
    (by rw [rkOf_decl, gM_top]) (by rw [rkOf_decl, gM_wrap]) (by rw [rkOf_decl, gM_wrap3]) (by rw [rkOf_decl, gM_leaf])

/-- `topshareQ_hcheck` with the rank table COMPUTED from the call graph `gQ` -/
theorem topshareQ_hcheck_computed (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) (f : Nat)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    hcheck (childMap D.modules) (rkOf gQ 3) (f + 2) (checkedOptimize b) = true :=
  topshareQ_hcheck O T hA f hR0 hcl entry₁ entry₂ entry hcore hpost hw (rkOf gQ 3) (rkOf_mem gQ 3)
    (by rw [rkOf_decl, gQ_top]) (by rw [rkOf_decl, gQ_wrapP]) (by rw [rkOf_decl, gQ_wrapQ]) (by rw [rkOf_decl, gQ_leaf])
end

/-! ## further generated examples with memory children (rank only) -/


/-- `seqTwoMem` (a flat parent: two sequential children `cnt`, `acc`, two memories), graph read from the machine data of all three declarations -/
noncomputable def gTwo : CallGraph :=
  [(``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem, Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem.machineData.shape.instTagged), (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt, Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape.instTagged),
   (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.instTagged)]

theorem gTwo_inClass : InClass gTwo 3 ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem = true := by decide
theorem gTwo_top : declRank gTwo 3 ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem = some 1 := by decide


/-- `collMixSame5` has two call entries named alike (`SparkleMem.sync.4.8`): one is the memory (origin `.mem`), the other an ORDINARY call (origin `.ord`) of a declaration of that name.
The graph holds only the parent; the ordinary callee is not read, so the rank is REFUSED (the origin, not the name, separates the two entries). -/
noncomputable def gColl : CallGraph := [(``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5, Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machineData.shape.instTagged)]

theorem gColl_refused : declRank gColl 3 ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5 = none := by decide
theorem gColl_notInClass : InClass gColl 3 ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5 = false := by decide

/-! ## refusal fixtures (synthetic graphs) -/

def okG : CallGraph := [(`t, [(`m, .ord), (`l, .ord)]), (`m, [(`l, .ord)]), (`l, [])]
theorem okG_rank : declRank okG 4 `t = some 2 ∧ declRank okG 4 `m = some 1 ∧ declRank okG 4 `l = some 0 := by decide
/-- cycle: `a → b → a`, refused at EVERY fuel tried (and by `rkOf_edge`'s strict decrease at every fuel) -/
def cycG : CallGraph := [(`a, [(`b, .ord)]), (`b, [(`a, .ord)])]
theorem cycG_refused : declRank cycG 8 `a = none ∧ declRank cycG 8 `b = none := by decide
def selfG : CallGraph := [(`a, [(`a, .ord)])]
theorem selfG_refused : declRank selfG 8 `a = none := declRank_self (g := selfG) (c := `a) (ks := [(`a, .ord)]) (by decide) (by decide) 8
/-- an unresolved callee -/
def missG : CallGraph := [(`a, [(`zz, .ord)])]
theorem missG_refused : declRank missG 8 `a = none := by decide
/-- duplicate declaration names -/
def dupG : CallGraph := [(`a, []), (`a, [(`b, .ord)]), (`b, [])]
theorem dupG_wf : WfG dupG = false := by decide
theorem dupG_class : InClass dupG 4 `a = false := by decide
theorem dupG_table (F : Nat) (s : String) : rkChecked dupG F s = none := rkChecked_dup dupG_wf F s
/-- fuel too small: the depth bound `B` is part of the class -/
theorem okG_fuel : InClass okG 2 `t = false ∧ InClass okG 3 `t = true := by decide
/-- a missing callee in a REAL graph: `leafM` not read -/
noncomputable def gMnoLeaf : CallGraph :=
  [(``topshareM, topshareM.machineData.shape.instTagged), (``wrapM, wrapM.machineData.shape.instTagged),
   (``wrapM3, wrapM3.machineData.shape.instTagged)]
theorem gMnoLeaf_refused : declRank gMnoLeaf 4 ``topshareM = none := by decide

end Tests.Compiler.Srm7RankTest
