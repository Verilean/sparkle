import Tests.Compiler.TopShareTraceTest
import Tests.Compiler.TopShareRetInstTest
import Tools.ShippingTopShareRan
import Tools.ShippingSeqParentAt
import Tools.ShippingSeqOldPieces
import Tools.ShippingSeqChildDeepRunA
import Tests.Compiler.SeqDeepGrandEndpointTest
-- BUILT (unit SR11): t3 (scratch `lean`, pieces + endpoint + wired theorem) exit 0; c3 (this file, `lean`, with the in-file audits) exit 0 (c1/c2 were stopped: the first audit used default-transparency isDefEq and did not finish); see REPORT-SR11.md for the final-SHA rebuild.
-- SCOPE (binding, ledger L8aq): the depth-2 pieces of the endpoint `Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc` for the
-- SHARED-leaf design `topshare` (callees `wrap`, `wrap3`, both calling the SAME leaf `acc`): `composed` (`ts_composedA`: `ComposedG` at depth 2
-- from the four calls [wrap, wrap, wrap3, wrap3]), `soundL`, `houtTy` (`decide`), and the four design checks (`ts_runFacts`, `ts_outsCheck`,
-- `ts_kidsMasked`, `ts_designCheck`), and the endpoint INSTANCE `topshare_noShips_noBd_dc` plus `topshare_wired` (ONE witness `M`, `Dg` shared with
-- `topshare_entry_run_inst_ret`).  The generator `#machine_seq_parent_endpoint` still REFUSES `topshare`; this file is NOT a generator change.
-- HOW THE TEXT WAS OBTAINED (honest): the pieces below are the instantiation, for `P = topshare`, `Cs = [wrap, wrap3]`, `Gs = [acc, acc]`, of the
-- template text of `Tools/ShippingSeqParentGenD2M.lean`, obtained by calling its public `assembleM` on parameters read by a copy of its
-- `analyseM` with only the SAME-leaf refusal removed (the dump was done in a scratch file, not committed).  The generated text is pasted here
-- with these edits: (a) `epD2M_disj` and the parent `epD2M_closesA` (whose library lemma needs `hdisjD`, FALSE for a shared leaf) are DELETED;
-- (b) the parent closing is the START-world one: `ts_ranA` uses `machineRanA_start0` with `topshare_closes0` (SR10, DERIVED), `ts_traceXA` uses
-- `topshare_machineRun` (SR10); the start world is `JQC O 0 w` (not `JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA …)`); (c) names `topshare.epD2M…` → `Tests.Compiler.TopShareComposedTest.ts…`
-- (so no `epD2M_*` declaration exists for the refused `topshare`).  The per-callee blocks (`ts0_*` for `wrap -> acc`, `ts1_*` for `wrap3 -> acc`) are unchanged.
-- The old chain `#machine_design_svNR topshare 2` is run below ONLY to read PC-free pieces (`hcalls`, group facts, `Inhabited` instance) through
-- `old_seqparent%` / `oldGroupFact%` / `oldInst%` as for `grand`; the old theorems themselves are asserted NOT in the closure (in-file audit).
-- PREMISES (not derived here): `O : RefLawsAOps`, `T : RefLawsATele`, `AdmCtx`, `MachineDefines` of topshare/wrap/wrap3/acc, start world `JQC O 0 w`;
-- these are carried in `ts_Bnd` / the hypotheses of `topshare_wired`.  `RealChildA`/`ServedRealA`/`JQC` are histories, not semantic correctness in the current environment.
open Tests.Compiler.SeqDeepGenDiffTest Tests.Compiler.SeqDeepGenInstTest
set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SeqDeepGenDiffTest.topshare 2

section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingSeqParentLemmas
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA Tools.ShippingChildDepthC
open Tools.ShippingChildTranslateA Tools.ShippingParentRanA Tools.ShippingChildComposeC Tools.ShippingChildRunAMain
open Tools.ShippingParentSeqComposedA
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- An origin without a memory key builds no child (so a call-field origin, whatever its field index, is `KidTA`'s second disjunct). -/
theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_origin_child_none (o : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (h : Tools.ShippingMemCloses.memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [Tools.ShippingMemCloses.memKey])

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_G_outs_clean :
    ∀ o ∈ Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts0_G_nk : Nat :=
  ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.binders.take (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.binders.length -
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.slots.length - Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_insts_G : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length),
    (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk Tests.Compiler.SeqDeepGenInstTest.wrap.machineData 3 (fun _ => [8]) = true := by
  first | decide | decide +kernel


theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length),
      (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc ∧ Tools.ShippingMemCloses.memKey (originAt Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape k) = none := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape k)
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc) Tests.Compiler.TopShareComposedTest.ts0_G_nk
        (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    unfold Tools.ShippingCallsMemA.KidTA at hy
    rw [Tests.Compiler.TopShareComposedTest.ts0_origin_child_none _ ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (by decide) (by decide) hR0 (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := 3) O T hA Tests.Compiler.SeqDeepGenInstTest.wrap.machineData
    Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc) (fun _ => Tests.Compiler.TopShareComposedTest.ts0_G_nk)
    (fun _ => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc ≠ ``Tests.Compiler.SeqDeepGenInstTest.wrap))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_hsep {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenInstTest.wrap) := by
  have hn : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length),
      (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
    first | decide | decide +kernel
  refine Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids (mctx := mctx) (cctx := cctx) O Tests.Compiler.SeqDeepGenInstTest.wrap.machineData ?_
    (fun k hk => by rw [hn k hk]; decide)
  intro k hk
  rw [hn k hk]
  exact ⟨Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body, by decide, by decide, hR0,
    fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _⟩


set_option maxRecDepth 100000 in
theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_outChars : ∀ o ∈ Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_outScalar : ∀ o ∈ Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel


theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_G_kidFactsA (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) (n : Nat) :
    KidFactsA O ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs [8] n := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape :=
    fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _
  have hon : ∀ o ∈ Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.TopShareComposedTest.ts0_G_outs_clean o ho)
  have hdw : Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData = [8] := by first | decide | decide +kernel
  exact
  { outsIn := fun y hy =>
      (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) hR0 hcl hy).outsIn
    outTys := fun y hy =>
      Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0
        (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
    kidA := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidAA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy
    kidR := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidRA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) hR0 hcl hy
    masked := fun y hy =>
      Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hR0 hcl hy
    portsIn := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_portsInA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy
    inW := fun y hy j q hq => by
      obtain ⟨wd, h1, h2⟩ := Tools.ShippingParentDesignFA.leaf_real_inWidthsA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy j q hq
      rw [hdw] at h1
      exact ⟨wd, h1, h2⟩
    clk := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_clkA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy
    check := fun y hy ms _ _ => by
      have hK := Tools.ShippingParentDesignFA.leaf_real_kidK_regA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy
      exact ⟨hK.1 _ n, fun g hg => hK.2 g hg _ n⟩ }

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    KidFactsA O ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs
      (Tools.ShippingCallsChildPorts.argWidths Tests.Compiler.SeqDeepGenInstTest.wrap.machineData 3) (n + 1) := by
  have hn := Tests.Compiler.TopShareComposedTest.ts0_C_insts_G
  exact Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA O T Tests.Compiler.SeqDeepGenInstTest.wrap.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok
    Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body (nDecl := 3) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    3 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs) (fun _ => [8]) n
    (fun k hk => by rw [hn k hk]; exact Tests.Compiler.TopShareComposedTest.ts0_G_kidFactsA O hR0 n)
    (fun k hk => by rw [hn k hk]; exact Tests.Compiler.TopShareComposedTest.ts0_G_kidFactsA O hR0 (n + 1))
    (by first | decide | decide +kernel) Tests.Compiler.TopShareComposedTest.ts0_C_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.TopShareComposedTest.ts0_C_outChars o ho)) Tests.Compiler.TopShareComposedTest.ts0_C_outScalar
    (Tests.Compiler.TopShareComposedTest.ts0_C_hsep O hR0) entry
    (fun _ _ hA' => Tests.Compiler.TopShareComposedTest.ts0_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_hgk (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] := by
  intro k hk y' hy g hg
  rw [Tests.Compiler.TopShareComposedTest.ts0_C_insts_G k hk] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
    (by decide) (by decide) hR0 (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``Tests.Compiler.SeqDeepGenInstTest.wrap y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenInstTest.wrap) (Tools.ShippingMachineEntry.machNIn Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
      (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] y.1 y.2 :=
  Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP O T Tests.Compiler.SeqDeepGenInstTest.wrap.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body (nDecl := 3)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) 3
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    _ (Tests.Compiler.TopShareComposedTest.ts0_C_hgk O hR0) (Tests.Compiler.TopShareComposedTest.ts0_C_hsep O hR0) entry
    (fun _ _ hA' => Tests.Compiler.TopShareComposedTest.ts0_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

def _root_.Tests.Compiler.TopShareComposedTest.ts0_C_Bnd (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ =>
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape

instance _root_.Tests.Compiler.TopShareComposedTest.ts0_C_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.ss))) Tests.Compiler.SeqDeepGenInstTest.wrap.machine_composedNR1
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA


theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_hcausal : HCausalOf Tests.Compiler.SeqDeepGenInstTest.wrap.machineData (fun i => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB :=
  fun i bools bits S S' t h =>
  Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenInstTest.wrap [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape m design)
      ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData m design (fun i => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)))
      (letObsB Tests.Compiler.SeqDeepGenInstTest.wrap.machineData (fun i => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits
        Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA Tests.Compiler.SeqDeepGenInstTest.wrap.machineData
    (fun i => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody Tests.Compiler.SeqDeepGenInstTest.wrap.machineResult
    Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body Tests.Compiler.SeqDeepGenInstTest.wrap.machine_inits
    Tests.Compiler.SeqDeepGenInstTest.wrap.machine_writes Tests.Compiler.SeqDeepGenInstTest.wrap.machine_result Tests.Compiler.SeqDeepGenInstTest.wrap.machine_source Tests.Compiler.TopShareComposedTest.ts0_C_hcausal
    O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design)
    (machineRunJQC_of_closesA O hA hcore entry (Tests.Compiler.TopShareComposedTest.ts0_C_closesA O T hA hR0) hw hc)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_hcalls (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData design m (dom := fun i => i)
      (letObsB Tests.Compiler.SeqDeepGenInstTest.wrap.machineData (fun i => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB)
      (fun i bools bits => Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)))
      3
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn else [])
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs else [])
      (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then fun vals => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineSource i
        (Tools.ShippingMachineChild.boolsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals) else fun vals => [])
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc)) :=
  (old_seqparent% hcalls Tests.Compiler.SeqDeepGenInstTest.wrap) m design

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenInstTest.wrap [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData 3 m design
      (fun i => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits))) := by
  have h := Tests.Compiler.TopShareComposedTest.ts0_C_traceXA O T hA hR0 hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h (by first | decide | decide +kernel) 3 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn else [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs else [])
    (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then fun vals => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineSource i
        (Tools.ShippingMachineChild.boolsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals) else fun vals => [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc))
    (Tests.Compiler.TopShareComposedTest.ts0_C_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact Tests.Compiler.TopShareComposedTest.ts0_C_insts_G k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape (Tests.Compiler.TopShareComposedTest.ts0_C_Bnd mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
      Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs
      (fun vals => Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (Tests.Compiler.TopShareComposedTest.ts0_C_Bnd mref cref)
    (fun hcore hadm hjqc entry _ hB => Tests.Compiler.TopShareComposedTest.ts0_C_composedA O T hadm hB hjqc.1 (Or.inr hjqc.2) hcore entry)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)) j = bools j)
      Tests.Compiler.SeqDeepGenInstTest.wrap.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hextB)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)) j n' = bits j n')
      Tests.Compiler.SeqDeepGenInstTest.wrap.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hext)
    Sparkle.Core.Domain.defaultDomain h


/-- An origin without a memory key builds no child (so a call-field origin, whatever its field index, is `KidTA`'s second disjunct). -/
theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_origin_child_none (o : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (h : Tools.ShippingMemCloses.memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [Tools.ShippingMemCloses.memKey])

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_G_outs_clean :
    ∀ o ∈ Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts1_G_nk : Nat :=
  ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.binders.take (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.binders.length -
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.slots.length - Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_insts_G : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length),
    (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts[k]).1 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 (fun _ => [8]) = true := by
  first | decide | decide +kernel


theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length),
      (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts[k]).1 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc ∧ Tools.ShippingMemCloses.memKey (originAt Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape k) = none := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape k)
        (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc) Tests.Compiler.TopShareComposedTest.ts1_G_nk
        (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    unfold Tools.ShippingCallsMemA.KidTA at hy
    rw [Tests.Compiler.TopShareComposedTest.ts1_origin_child_none _ ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (by decide) (by decide) hR0 (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := 3) O T hA Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData
    Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_ok Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc) (fun _ => Tests.Compiler.TopShareComposedTest.ts1_G_nk)
    (fun _ => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc ≠ ``Tests.Compiler.SeqDeepGenDiffTest.wrap3))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_hsep {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.wrap3) := by
  have hn : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length),
      (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts[k]).1 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
    first | decide | decide +kernel
  refine Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids (mctx := mctx) (cctx := cctx) O Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData ?_
    (fun k hk => by rw [hn k hk]; decide)
  intro k hk
  rw [hn k hk]
  exact ⟨Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body, by decide, by decide, hR0,
    fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _⟩


set_option maxRecDepth 100000 in
theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_outChars : ∀ o ∈ Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_outScalar : ∀ o ∈ Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel


theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_G_kidFactsA (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) (n : Nat) :
    KidFactsA O ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs [8] n := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape :=
    fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _
  have hon : ∀ o ∈ Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.TopShareComposedTest.ts1_G_outs_clean o ho)
  have hdw : Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData = [8] := by first | decide | decide +kernel
  exact
  { outsIn := fun y hy =>
      (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) hR0 hcl hy).outsIn
    outTys := fun y hy =>
      Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0
        (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
    kidA := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidAA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy
    kidR := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidRA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (by decide) (by decide) hR0 hcl hy
    masked := fun y hy =>
      Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hR0 hcl hy
    portsIn := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_portsInA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy
    inW := fun y hy j q hq => by
      obtain ⟨wd, h1, h2⟩ := Tools.ShippingParentDesignFA.leaf_real_inWidthsA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy j q hq
      rw [hdw] at h1
      exact ⟨wd, h1, h2⟩
    clk := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_clkA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy
    check := fun y hy ms _ _ => by
      have hK := Tools.ShippingParentDesignFA.leaf_real_kidK_regA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
        (nDecl := Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy
      exact ⟨hK.1 _ n, fun g hg => hK.2 g hg _ n⟩ }

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    KidFactsA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs
      (Tools.ShippingCallsChildPorts.argWidths Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3) (n + 1) := by
  have hn := Tests.Compiler.TopShareComposedTest.ts1_C_insts_G
  exact Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA O T Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_ok
    Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_body (nDecl := 3) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    3 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs) (fun _ => [8]) n
    (fun k hk => by rw [hn k hk]; exact Tests.Compiler.TopShareComposedTest.ts1_G_kidFactsA O hR0 n)
    (fun k hk => by rw [hn k hk]; exact Tests.Compiler.TopShareComposedTest.ts1_G_kidFactsA O hR0 (n + 1))
    (by first | decide | decide +kernel) Tests.Compiler.TopShareComposedTest.ts1_C_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.TopShareComposedTest.ts1_C_outChars o ho)) Tests.Compiler.TopShareComposedTest.ts1_C_outScalar
    (Tests.Compiler.TopShareComposedTest.ts1_C_hsep O hR0) entry
    (fun _ _ hA' => Tests.Compiler.TopShareComposedTest.ts1_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_hgk (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] := by
  intro k hk y' hy g hg
  rw [Tests.Compiler.TopShareComposedTest.ts1_C_insts_G k hk] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
    (by decide) (by decide) hR0 (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.wrap3) (Tools.ShippingMachineEntry.machNIn Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
      (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] y.1 y.2 :=
  Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP O T Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_ok Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_body (nDecl := 3)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) 3
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    _ (Tests.Compiler.TopShareComposedTest.ts1_C_hgk O hR0) (Tests.Compiler.TopShareComposedTest.ts1_C_hsep O hR0) entry
    (fun _ _ hA' => Tests.Compiler.TopShareComposedTest.ts1_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

def _root_.Tests.Compiler.TopShareComposedTest.ts1_C_Bnd (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ =>
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape

instance _root_.Tests.Compiler.TopShareComposedTest.ts1_C_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.ss))) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_composedNR1
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA


theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_hcausal : HCausalOf Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData (fun i => i) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB :=
  fun i bools bits S S' t h =>
  Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape m design)
      ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData m design (fun i => i) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)))
      (letObsB Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData (fun i => i) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits
        Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData
    (fun i => i) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineResult
    Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_ok Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_body Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_inits
    Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_writes Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_result Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_source Tests.Compiler.TopShareComposedTest.ts1_C_hcausal
    O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design)
    (machineRunJQC_of_closesA O hA hcore entry (Tests.Compiler.TopShareComposedTest.ts1_C_closesA O T hA hR0) hw hc)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_hcalls (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData design m (dom := fun i => i)
      (letObsB Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData (fun i => i) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB)
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)))
      3
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn else [])
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs else [])
      (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then fun vals => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineSource i
        (Tools.ShippingMachineChild.boolsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals) else fun vals => [])
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc)) :=
  (old_seqparent% hcalls Tests.Compiler.SeqDeepGenDiffTest.wrap3) m design

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 m design
      (fun i => i) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits))) := by
  have h := Tests.Compiler.TopShareComposedTest.ts1_C_traceXA O T hA hR0 hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h (by first | decide | decide +kernel) 3 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn else [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs else [])
    (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then fun vals => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineSource i
        (Tools.ShippingMachineChild.boolsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.bsIn vals) else fun vals => [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc then (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc))
    (Tests.Compiler.TopShareComposedTest.ts1_C_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact Tests.Compiler.TopShareComposedTest.ts1_C_insts_G k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape (Tests.Compiler.TopShareComposedTest.ts1_C_Bnd mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
      Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs
      (fun vals => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (Tests.Compiler.TopShareComposedTest.ts1_C_Bnd mref cref)
    (fun hcore hadm hjqc entry _ hB => Tests.Compiler.TopShareComposedTest.ts1_C_composedA O T hadm hB hjqc.1 (Or.inr hjqc.2) hcore entry)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)) j = bools j)
      Tests.Compiler.SeqDeepGenDiffTest.wrap3.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hextB)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)) j n' = bits j n')
      Tests.Compiler.SeqDeepGenDiffTest.wrap3.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hext)
    Sparkle.Core.Domain.defaultDomain h

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_calleeAt (k : Nat) : Name :=
  ((Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts[k]?).map (·.1)).getD Name.anonymous

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_calleeAt_eq (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.length) :
    Tests.Compiler.TopShareComposedTest.ts_calleeAt k = (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts[k]).1 := by
  simp [Tests.Compiler.TopShareComposedTest.ts_calleeAt, List.getElem?_eq_getElem hk]

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_outsOf (n : Name) : List Sparkle.IR.Machine.OutField :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs else []

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_outsOf_0 : Tests.Compiler.TopShareComposedTest.ts_outsOf ``Tests.Compiler.SeqDeepGenInstTest.wrap = Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs := by
  unfold Tests.Compiler.TopShareComposedTest.ts_outsOf
  rw [if_pos rfl]

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_outsOf_1 : Tests.Compiler.TopShareComposedTest.ts_outsOf ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape.layout.outs := by
  unfold Tests.Compiler.TopShareComposedTest.ts_outsOf
  rw [if_neg (show ¬ ((``Tests.Compiler.SeqDeepGenDiffTest.wrap3 : Name) = ``Tests.Compiler.SeqDeepGenInstTest.wrap) by decide), if_pos rfl]

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_widthsOf (n : Name) : List Nat :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then Tools.ShippingCallsChildPorts.argWidths Tests.Compiler.SeqDeepGenInstTest.wrap.machineData 3 else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then Tools.ShippingCallsChildPorts.argWidths Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 else []

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_widthsOf_0 : Tests.Compiler.TopShareComposedTest.ts_widthsOf ``Tests.Compiler.SeqDeepGenInstTest.wrap = Tools.ShippingCallsChildPorts.argWidths Tests.Compiler.SeqDeepGenInstTest.wrap.machineData 3 := by
  unfold Tests.Compiler.TopShareComposedTest.ts_widthsOf
  rw [if_pos rfl]

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_widthsOf_1 : Tests.Compiler.TopShareComposedTest.ts_widthsOf ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = Tools.ShippingCallsChildPorts.argWidths Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 := by
  unfold Tests.Compiler.TopShareComposedTest.ts_widthsOf
  rw [if_neg (show ¬ ((``Tests.Compiler.SeqDeepGenDiffTest.wrap3 : Name) = ``Tests.Compiler.SeqDeepGenInstTest.wrap) by decide), if_pos rfl]

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_nInOf (n : Name) : Nat :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then Tools.ShippingMachineEntry.machNIn Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then Tools.ShippingMachineEntry.machNIn Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape else 0

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_nInOf_0 : Tests.Compiler.TopShareComposedTest.ts_nInOf ``Tests.Compiler.SeqDeepGenInstTest.wrap = Tools.ShippingMachineEntry.machNIn Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape := by
  unfold Tests.Compiler.TopShareComposedTest.ts_nInOf
  rw [if_pos rfl]

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_nInOf_1 : Tests.Compiler.TopShareComposedTest.ts_nInOf ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = Tools.ShippingMachineEntry.machNIn Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape := by
  unfold Tests.Compiler.TopShareComposedTest.ts_nInOf
  rw [if_neg (show ¬ ((``Tests.Compiler.SeqDeepGenDiffTest.wrap3 : Name) = ``Tests.Compiler.SeqDeepGenInstTest.wrap) by decide), if_pos rfl]

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_leafOf (n : Name) : Name :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc else Name.anonymous

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_leafOf_0 : Tests.Compiler.TopShareComposedTest.ts_leafOf ``Tests.Compiler.SeqDeepGenInstTest.wrap = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
  unfold Tests.Compiler.TopShareComposedTest.ts_leafOf
  rw [if_pos rfl]

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_leafOf_1 : Tests.Compiler.TopShareComposedTest.ts_leafOf ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by
  unfold Tests.Compiler.TopShareComposedTest.ts_leafOf
  rw [if_neg (show ¬ ((``Tests.Compiler.SeqDeepGenDiffTest.wrap3 : Name) = ``Tests.Compiler.SeqDeepGenInstTest.wrap) by decide), if_pos rfl]

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_bsF (n : Name) :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn else []

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_srcF (_i : Unit) (n : Name) : (Nat → List Nat) → List (Nat → Nat) :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then fun vals => Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn) vals) (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn) vals) else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then fun vals => Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn) vals) (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn) vals) else fun _ => []

noncomputable def _root_.Tests.Compiler.TopShareComposedTest.ts_PC (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) (n : Name) (mc : Sparkle.IR.AST.Module) : Prop :=
  if n = ``Tests.Compiler.SeqDeepGenInstTest.wrap then Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape (Tests.Compiler.TopShareComposedTest.ts0_C_Bnd mref cref) mc design else if n = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 then Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape (Tests.Compiler.TopShareComposedTest.ts1_C_Bnd mref cref) mc design else True


theorem _root_.Tests.Compiler.TopShareComposedTest.ts_callees : Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.map (·.1) = [``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3] := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_mem : ∀ c ∈ Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.map (·.1), c = ``Tests.Compiler.SeqDeepGenInstTest.wrap ∨ c = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 := by
  first | decide | decide +kernel

/-- An origin without a memory key builds no child (so a call-field origin, whatever its field index, is `KidTA`'s second disjunct). -/
theorem _root_.Tests.Compiler.TopShareComposedTest.ts_origin_child_none (o : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (h : Tools.ShippingMemCloses.memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [Tools.ShippingMemCloses.memKey])

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_insts_C : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.length),
    ((Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts[k]).1 = ``Tests.Compiler.SeqDeepGenInstTest.wrap ∨ (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts[k]).1 = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3) ∧ Tools.ShippingMemCloses.memKey (originAt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape k) = none := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_ne : ∀ k : Nat, k < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.length →
    Tests.Compiler.TopShareComposedTest.ts_calleeAt k ≠ ``Tests.Compiler.SeqDeepGenDiffTest.topshare ∧ Tests.Compiler.TopShareComposedTest.ts_leafOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k) ≠ ``Tests.Compiler.SeqDeepGenDiffTest.topshare := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData 3 (fun k => Tests.Compiler.TopShareComposedTest.ts_widthsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) = true := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_callWidths :
    Tools.ShippingCallWidths.callWidthsOk Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData 3 (fun k => Tests.Compiler.TopShareComposedTest.ts_outsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.Tests.Compiler.TopShareComposedTest.ts_outChars : ∀ o ∈ Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.Tests.Compiler.TopShareComposedTest.ts_outScalar : ∀ o ∈ Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    :
    ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.length),
      Tools.ShippingSeqChildDeepKidFactsA.KidFactsA O (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts[k]).1
        (Tests.Compiler.TopShareComposedTest.ts_outsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (Tests.Compiler.TopShareComposedTest.ts_widthsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (n + 1) := by
  intro k hk
  rw [Tests.Compiler.TopShareComposedTest.ts_calleeAt_eq k hk]
  rcases (Tests.Compiler.TopShareComposedTest.ts_insts_C k hk).1 with hn | hn
  · rw [hn, Tests.Compiler.TopShareComposedTest.ts_outsOf_0, Tests.Compiler.TopShareComposedTest.ts_widthsOf_0]
    exact Tests.Compiler.TopShareComposedTest.ts0_C_kidFactsA O T n hM0 hR0
  · rw [hn, Tests.Compiler.TopShareComposedTest.ts_outsOf_1, Tests.Compiler.TopShareComposedTest.ts_widthsOf_1]
    exact Tests.Compiler.TopShareComposedTest.ts1_C_kidFactsA O T n hM1 hR1


theorem _root_.Tests.Compiler.TopShareComposedTest.ts_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape)
    (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (Tests.Compiler.TopShareTraceTest.topshare_closes0 O T hA hM0 hM1 hR0) hw

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape)
    (hw : JQC O 0 w) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingSeqParentKidFactsA.kidsA_runFacts O Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_ok Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_body
    (nDecl := 3) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k => Tests.Compiler.TopShareComposedTest.ts_outsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (fun k => Tests.Compiler.TopShareComposedTest.ts_widthsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (n + 1)
    (Tests.Compiler.TopShareComposedTest.ts_hkid O T n hM0 hR0 hM1 hR1) Tests.Compiler.TopShareComposedTest.ts_callWidths hpost (Tests.Compiler.TopShareComposedTest.ts_ranA O T hA hM0 hR0 hM1 hR1 hcore entry hw)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape)
    (hw : JQC O 0 w) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (n + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_outsCheck O Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_ok Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_body
    (nDecl := 3) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k => Tests.Compiler.TopShareComposedTest.ts_outsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (fun k => Tests.Compiler.TopShareComposedTest.ts_widthsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (n + 1)
    (Tests.Compiler.TopShareComposedTest.ts_hkid O T n hM0 hR0 hM1 hR1) hpost (Tests.Compiler.TopShareComposedTest.ts_ranA O T hA hM0 hR0 hM1 hR1 hcore entry hw)
    (Tests.Compiler.TopShareComposedTest.ts_runFacts O T n hA hM0 hR0 hM1 hR1 hcore hpost entry hw).gate

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape)
    (hw : JQC O 0 w) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_maskedN O Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_ok Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_body
    (nDecl := 3) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k => Tests.Compiler.TopShareComposedTest.ts_outsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (fun k => Tests.Compiler.TopShareComposedTest.ts_widthsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (n + 1)
    (Tests.Compiler.TopShareComposedTest.ts_hkid O T n hM0 hR0 hM1 hR1) hpost (Tests.Compiler.TopShareComposedTest.ts_ranA O T hA hM0 hR0 hM1 hR1 hcore entry hw)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_designCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape)
    (hw : JQC O 0 w) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) (n + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_designCheck O Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_ok Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_body
    (nDecl := 3) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k => Tests.Compiler.TopShareComposedTest.ts_outsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (fun k => Tests.Compiler.TopShareComposedTest.ts_widthsOf (Tests.Compiler.TopShareComposedTest.ts_calleeAt k)) (n + 1)
    (Tests.Compiler.TopShareComposedTest.ts_hkid O T n hM0 hR0 hM1 hR1) Tests.Compiler.TopShareComposedTest.ts_callWidths Tests.Compiler.TopShareComposedTest.ts_callArgs hpost (Tests.Compiler.TopShareComposedTest.ts_ranA O T hA hM0 hR0 hM1 hR1 hcore entry hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.TopShareComposedTest.ts_outChars o ho)) Tests.Compiler.TopShareComposedTest.ts_outScalar

instance _root_.Tests.Compiler.TopShareComposedTest.ts_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.ss))) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_hcausal : HCausalOf Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB := fun i bools bits S S' t h =>
  Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape m design)
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
      (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits
        Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData
    (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineResult
    Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineSource Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_ok Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_body Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_inits
    Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_writes Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_result Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_source Tests.Compiler.TopShareComposedTest.ts_hcausal
    O (bodyStepC_of_tele O T) hA (n := 0 + 1) (htr_of_tele O hA T 0) (m := m) (design := design)
    (Tests.Compiler.TopShareTraceTest.topshare_machineRun O T hA entry hM0 hM1 hR0 hw hcore)

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_soundLA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape) :
    Tools.ShippingMachineAuto.MachineTraceLB ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      Tests.Compiler.SeqDeepGenDiffTest.topshare.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
      (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits
        Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    Tests.Compiler.TopShareComposedTest.ts_traceXA O T hA hM0 hR0 hM1 hR1 hw hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_houtTy : ∀ o ∈ Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem _root_.Tests.Compiler.TopShareComposedTest.ts_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hM1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape)
    (hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData 3 m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineSource
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
      (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits))) := by
  have h := Tests.Compiler.TopShareComposedTest.ts_traceXA O T hA hM0 hR0 hM1 hR1 hw hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h (by first | decide | decide +kernel) 3 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    Tests.Compiler.TopShareComposedTest.ts_bsF Tests.Compiler.TopShareComposedTest.ts_outsOf Tests.Compiler.TopShareComposedTest.ts_srcF (Tests.Compiler.TopShareComposedTest.ts_PC O design)
    (fun i bools bits k c hk => by
      have hk2 : [``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenInstTest.wrap, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3][k]? = some c := by
        rw [← Tests.Compiler.TopShareComposedTest.ts_callees]; exact hk
      have hlt : k < 4 := by
        have := (List.getElem?_eq_some_iff.mp hk2).1; simpa using this
      -- the group facts of the generated proof that do not mention the child predicate: one bundle per distinct (callee, argument list)

      have L0 : ∀ (q : Nat) (hq : q < ([0, 1] : List Nat).length), ([0, 1] : List Nat)[q] < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.ls.length ∧
          ∃ g, (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits)[([0, 1] : List Nat)[q]]? = some g :=
        oldGroupFact% (∀ (q : Nat) (hq : q < ([0, 1] : List Nat).length), ([0, 1] : List Nat)[q] < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.ls.length ∧
          ∃ g, (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits)[([0, 1] : List Nat)[q]]? = some g) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfL0
      have R0 : ∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat) τ)
          ((List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn).filter fun b => b.2 != .domain) :=
        oldGroupFact% (∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat) τ)
          ((List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn).filter fun b => b.2 != .domain)) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfR0
      have Hb0 : Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
      have Hv0 : Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0


      have L1 : ∀ (q : Nat) (hq : q < ([1, 0] : List Nat).length), ([1, 0] : List Nat)[q] < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.ls.length ∧
          ∃ g, (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits)[([1, 0] : List Nat)[q]]? = some g :=
        oldGroupFact% (∀ (q : Nat) (hq : q < ([1, 0] : List Nat).length), ([1, 0] : List Nat)[q] < Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.ls.length ∧
          ∃ g, (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits)[([1, 0] : List Nat)[q]]? = some g) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfL1
      have R1 : ∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat) τ)
          ((List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn).filter fun b => b.2 != .domain) :=
        oldGroupFact% (∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat) τ)
          ((List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn).filter fun b => b.2 != .domain)) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfR1
      have Hb1 : Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb1
      have Hv1 : Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv1

      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      rcases k with _ | _ | _ | _ | k
      · have hck : c = ``Tests.Compiler.SeqDeepGenInstTest.wrap := by simpa using hk2.symm
        subst hck
        first
          | (refine ⟨rfl, [0, 1], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L0, R0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
          | (refine ⟨rfl, [0, 1], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L0, R0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
      · have hck : c = ``Tests.Compiler.SeqDeepGenInstTest.wrap := by simpa using hk2.symm
        subst hck
        first
          | (refine ⟨rfl, [0, 1], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L0, R0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
          | (refine ⟨rfl, [0, 1], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L0, R0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
      · have hck : c = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 := by simpa using hk2.symm
        subst hck
        first
          | (refine ⟨rfl, [1, 0], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L1, R1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
          | (refine ⟨rfl, [1, 0], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L1, R1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
      · have hck : c = ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 := by simpa using hk2.symm
        subst hck
        first
          | (refine ⟨rfl, [1, 0], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L1, R1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
          | (refine ⟨rfl, [1, 0], rfl, (fun mc hmc => ⟨Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc, by rw [(Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L1, R1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
      · omega)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      rcases Tests.Compiler.TopShareComposedTest.ts_mem c (List.mem_of_getElem? hc') with rfl | rfl
      · exact Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main O T
          (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons hM0
          (fun mctx cctx _ w raw D _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR0)
          (fun mctx cctx w raw D hin _ => by
            obtain ⟨_, _, _, hadm', _⟩ := hin
            exact Tests.Compiler.TopShareComposedTest.ts0_C_closesA O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
          (by first | decide | decide +kernel)
      · exact Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main O T
          (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons hM1
          (fun mctx cctx _ w raw D _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR1)
          (fun mctx cctx w raw D hin _ => by
            obtain ⟨_, _, _, hadm', _⟩ := hin
            exact Tests.Compiler.TopShareComposedTest.ts1_C_closesA O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR1))
          (by first | decide | decide +kernel))

def _root_.Tests.Compiler.TopShareComposedTest.ts_Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape ∧
    JQC O 0 w

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
/- The endpoint of `topshare`: `machine_design_noShips_noBd_dc` at `n := 2`, `kD := 3`, `C := True`, `Bnd := topshare.epD2M_Bnd` (the start world is
`JQC O 0 w`, the outermost entry's world), with `soundL` / `composed` / `houtTy` / the four checks supplied by the pieces above.  The theorem
`topshare_noShips_noBd_dc` is ADDED by this command (its type is the inferred type of the term). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 2 Tests.Compiler.TopShareComposedTest.ts_Bnd (fun _ _ _ _ => True)
    ``Tests.Compiler.SeqDeepGenDiffTest.topshare Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData 3 Unit (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_soundLA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
    (fun hcore entry _ hB _ => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_composedA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
    Tests.Compiler.TopShareComposedTest.ts_houtTy
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_runFacts O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    (fun hcore hpost entry _ hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_outsCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_kidsMasked O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_designCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw))
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the endpoint term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc, levelParams := [], type := ty, value := e }

#print axioms Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc

open Tests.Compiler.SeqDeepGenDiffTest in
open Tools.ShippingSharedLeafNL Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingChildInv Tools.ShippingTopShareRun in
/-- **The source-semantics endpoint instance for `topshare`, with ONE witness (unit SR11, L8aq).**  From the outer run `h` of
`synthesizeCombinational topshare` that returns `y` (start world `JQC O 0 w`), the SAME `M`, `Dg` carry
* every conjunct of `topshare_entry_run_inst_ret` (the closing, the cache facts, the CORE run from the same `w` returning `(M, Dg)`, and the
  clean-up relation `y.1 = dropZeroWidthModule M …` / `mergeChecked …`, `y.2 = topMap …`);
* (i) RAW module/design: `ComposedG` (depth 2) of `(M, Dg)` — the raw module run by `runModuleTG (KSn …)` with the children of `Dg` computes the
  source outputs (the `composed` of the endpoint);
* (ii) the returned module `y.1` (the clean-up of `M`): `DesignSemConcl` — its `checkedOptimize` runs (`DesignSV`, children of `Dg`) and computes the source outputs;
* (iii) `y.2` looks up every module not named like `M` exactly as `Dg` does (`moduleByName`).
NOT claimed: `DesignSV` with the children of `y.2` itself (only the lookup agreement (iii)): OPEN.  `O`, `T`, `hA`, the four `MachineDefines`
and `JQC O 0 w` are PREMISES; `RealChildA`/`ServedRealA`/`JQC` are histories, not freshness or semantic correctness in the current environment. -/
theorem Tests.Compiler.TopShareComposedTest.topshare_wired
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂]
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenInstTest.wrap = some y₁ ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
        mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``Tests.Compiler.SeqDeepGenDiffTest.topshare
        topshare.machineData 3 M Dg (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits))) ∧
      Tools.ShippingSeqParentAt.DesignSemConcl 2 ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData 3
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        y.1 M Dg ∧
      (∀ mn : String, mn ≠ M.name →
        Sparkle.IR.Machine.moduleByName y.2.modules mn = Sparkle.IR.Machine.moduleByName Dg.modules mn) := by
  obtain ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl, hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost⟩ :=
    Tests.Compiler.TopShareRetInstTest.topshare_entry_run_inst_ret O T hA entryT entryW entryW3 hR0 hw h
  have hpostb : y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    hpost.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hpost2 : y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg ∨
      y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
        (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) :=
    hpost.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl, hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost,
    Tests.Compiler.TopShareComposedTest.ts_composedA O T hA entryW hR0 entryW3 hR0 hw hcore entryT,
    ?_, Tools.ShippingSeqParentAt.moduleByName_post_other M Dg y.2 hpost2⟩
  exact Tools.ShippingSeqParentAt.machine_design_noShips_noBd_dc_at 2
    Tests.Compiler.TopShareComposedTest.ts_Bnd (fun _ _ _ _ => True)
    topshare.machineData
    (kD := 3) (ι := Unit) (dom := fun _ => Sparkle.Core.Domain.defaultDomain)
    (fun hcore entry _ hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_soundLA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
    (fun hcore entry _ hB _ => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_composedA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
    Tests.Compiler.TopShareComposedTest.ts_houtTy
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_runFacts O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    (fun hcore hpost entry _ hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_outsCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_kidsMasked O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_designCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
    hcore hpostb entryT trivial ⟨O, T, hA, entryW, hR0, entryW3, hR0, hw⟩

#print axioms Tests.Compiler.TopShareComposedTest.topshare_wired

open Tools.ShippingSharedLeafNL Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingChildInv Tools.ShippingTopShareRun in

/-- The hand-written expected statement of `topshare_wired` (v = 0), with type-correct mutations: 1 `ComposedG` for the design `y₁.2`; 2 `ComposedG` for the module `t'`;
3 `DesignSemConcl` for the RAW `M` instead of the clean-up `y.1`; 4 for the design `y.2`; 5 raw argument `t'`; 6 depth 1; 7 `kD = 2`; 8 core run starts at `w'`;
9 lookup agreement against `y₁.2`; 10 `DesignSemConcl` depth 1; 11 `wrap.machineData` instead of `topshare.machineData`; 12 declName `wrap`; 13 lookup agreement
without `mn ≠ M.name`; 15 only the first clean-up disjunct; 16 start world `JQC O 1 w`. -/
def Tests.Compiler.TopShareComposedTest.TopShareWiredFull (v : Nat) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O (if v = 16 then 1 else 0) w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w'),
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂]
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenInstTest.wrap = some y₁ ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
        mctx mref cctx cref (if v = 8 then w' else w) (M, Dg) wc ∧ cv wc = cv w10 ∧
      (let A := (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg)
       let B := (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))
       if v = 15 then A else (A ∨ B)) ∧
      ComposedG (fun D => KSn (childMap D.modules) (if v = 6 then 1 else 2)) (ResetNk (if v = 6 then 1 else 2)) (if v = 12 then ``Tests.Compiler.SeqDeepGenInstTest.wrap else ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
        topshare.machineData (if v = 7 then 2 else 3) (if v = 2 then t' else M) (if v = 1 then y₁.2 else Dg) (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits))) ∧
      Tools.ShippingSeqParentAt.DesignSemConcl (if v = 10 then 1 else 2) ``Tests.Compiler.SeqDeepGenDiffTest.topshare (if v = 11 then Tests.Compiler.SeqDeepGenInstTest.wrap.machineData else topshare.machineData) 3
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (if v = 3 then M else y.1) (if v = 5 then t' else M) (if v = 4 then y.2 else Dg) ∧
      (∀ mn : String, (if v = 13 then True else mn ≠ M.name) →
        Sparkle.IR.Machine.moduleByName y.2.modules mn = Sparkle.IR.Machine.moduleByName (if v = 9 then y₁.2 else Dg).modules mn)

end

open Lean Meta in
/-- The mutation switches `if v = k then … else …` of `TopShareWiredFull v` are evaluated (the decidable instance is reduced) so that the
comparison with the theorem's type is syntactic (reducible transparency): a mutation is rejected at its first differing argument without
unfolding `ComposedG` / `DesignSemConcl`. -/
def evalIteSR11 (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.isAppOfArity ``ite 5 then
      let inst := e.getAppArgs[2]!
      let r ← withDefault (whnf inst)
      if r.isAppOf ``Decidable.isTrue then return .visit e.getAppArgs[3]!
      if r.isAppOf ``Decidable.isFalse then return .visit e.getAppArgs[4]!
      throwError "SR11 AUDIT FAILED: cannot evaluate the switch {e.getAppArgs[1]!}"
    return .continue)

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let thm := ``Tests.Compiler.TopShareComposedTest.topshare_wired
  let ty := (← getConstInfo thm).type
  forallTelescope ty fun xs _ => do
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "O", "T", "hA", "entryT", "entryW", "entryW3", "hR0", "w", "w'", "y", "hw", "h"] do
      throwError "SR11 AUDIT FAILED: premises of {thm} are {names}"
  if ty.hasMVar then throwError "SR11 AUDIT FAILED: metavariables in the statement"
  Meta.check ty
  let full (v : Nat) : MetaM Lean.Expr := do
    let some b ← unfoldDefinition? (mkApp (mkConst ``Tests.Compiler.TopShareComposedTest.TopShareWiredFull) (mkNatLit v))
      | throwError "SR11 AUDIT FAILED: cannot unfold TopShareWiredFull"
    evalIteSR11 (← instantiateMVars b)
  unless ← withReducible (isDefEq ty (← full 0)) do throwError "SR11 AUDIT FAILED: the statement of {thm} differs from the hand-written expected statement"
  let mut rejected : List Nat := []
  for v in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16] do
    if ← withReducible (isDefEq ty (← full v)) then throwError "SR11 AUDIT FAILED: the mutation {v} of the expected statement was ACCEPTED"
    rejected := v :: rejected
  let concl ← forallTelescope ty fun xs b => pure (b.containsFVar xs[13]!.fvarId!)
  unless concl do throwError "SR11 AUDIT FAILED: the conclusion does not mention y"
  logInfo m!"SR11 STATEMENT AUDIT: {thm} equals the hand-written TopShareWiredFull 0 (isDefEq under reducible transparency after evaluating the switches, no mvars, Meta.check); the conclusion mentions y; mutations rejected: {rejected.reverse}"

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR11 AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let oldGen : List Name := [`Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2, `Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_design_svNR2,
    `Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_composedNR1, `Tests.Compiler.SeqDeepGenDiffTest.wrap3.seq_child_runN_ofR1,
    `Tests.Compiler.SeqDeepGenInstTest.wrap.machine_composedNR1, `Tests.Compiler.SeqDeepGenInstTest.wrap.seq_child_runN_ofR1]
  for f in oldGen do
    unless (← getEnv).contains f do throwError "SR11 AUDIT FAILED: the old generated name {f} does not exist (the audit would check nothing)"
  for new in [``Tests.Compiler.TopShareComposedTest.topshare_wired, ``Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc] do
    stdAxioms new
    let cl ← depClosure new
    let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "SR11 AUDIT FAILED: {new}: old boundary / old child predicate in closure: {bad}"
    for old in oldGen do
      if cl.contains old then throwError "SR11 AUDIT FAILED: the old generated theorem {old} is in the closure of {new}"
    for must in [``Tests.Compiler.TopShareComposedTest.ts_composedA, ``Tests.Compiler.TopShareComposedTest.ts_soundLA,
        ``Tests.Compiler.TopShareComposedTest.ts_runFacts, ``Tests.Compiler.TopShareComposedTest.ts_outsCheck,
        ``Tests.Compiler.TopShareComposedTest.ts_kidsMasked, ``Tests.Compiler.TopShareComposedTest.ts_designCheck,
        ``Tests.Compiler.TopShareComposedTest.ts_ranA, ``Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2,
        ``Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2,
        ``Tests.Compiler.TopShareTraceTest.topshare_closes0, ``Tests.Compiler.TopShareTraceTest.topshare_machineRun,
        ``Tools.ShippingTopShareRan.machineRanA_start0,
        ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
        ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
        ``Tools.ShippingMachineShipsDepth.composedG_of_NW] do
      unless cl.contains must do throwError "SR11 AUDIT FAILED: {must} not in the closure of {new}"
    logInfo m!"SR11 CLOSURE AUDIT: {new}: standard axioms; closure {cl.size} constants; none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC, no RefLaws/RefLawsCore/toAOps/toA; the old generated topshare/wrap/wrap3 composed theorems are not in it; the start-world pieces are"
  -- the original-lemma instance: outer Prop premises and the boundary in the conclusion
  let ty := (← getConstInfo ``Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR11 AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  unless (concl.find? (·.isConstOf ``Tests.Compiler.TopShareComposedTest.ts_Bnd)).isSome do throwError "SR11 AUDIT FAILED: ts_Bnd not in the conclusion"
  logInfo m!"SR11 AUDIT OK: topshare_noShips_noBd_dc outer Prop premises ASSERTED {premises}; ts_Bnd stays in the conclusion"
