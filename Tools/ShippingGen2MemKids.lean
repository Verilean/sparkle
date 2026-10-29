import Tools.ShippingSrm4Core4
import Tools.ShippingSrm4Core6
import Tools.ShippingMemOnly
set_option autoImplicit false

/-! # M2-a C4: `kidsMem` of the emitted module from the A-run (scripts/gen2/MEMPARENT_FREEZE.md rev1, approved 121c09fe)

The A-form of `memOnly_kidsMem` / `core_kidsMemM` (Tools/ShippingMemOnly.lean:81, :185): for a machine whose every call
entry has a memory origin, the emitted module's instances are all built memory modules with no `out_rdata`
connection. The prelude (run decomposition up to the instance's `CallStmtG`) is copied from
`core_callConns_ranAM` (Tools/ShippingSrm4Core4.lean:37-130); the conclusion uses `KidTA.mem'`,
`mem_conns_noRdata` (Tools/ShippingMemKidFacts.lean:396), `kidsMem_one` (:143) and `kidsMem_of`
(Tools/ShippingMemOnly.lean:56). -/
namespace Tools.ShippingGen2
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
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA Tools.ShippingSrm4Core1 Tools.ShippingSrm4Core2
open Tools.ShippingInstTagged (originAt)

open Tools.ShippingSrm4Core4 Tools.ShippingSrm4Core6
open Sparkle.Compiler.MachMemory (memModule)

theorem core_kidsMem_ranAM (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (hmemO : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
      (originAt d.shape k).child? = some (memModule cb aw dw))
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingMachineShipsHier.kidsMem (childMap D.modules) b.body = true := by
  have hbody' : b.body = M.body :=
    (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, hMC⟩
  · exact absurd hf0 hfne
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  obtain ⟨hlenC, hallC⟩ := hreal
  refine Tools.ShippingMemOnly.kidsMem_of fun mn iname conns hst => ?_
  rw [hbody'] at hst
  rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hst rfl with
    h0 | ⟨args, outs, child, mc, hcs, hfind, hne0, hall⟩
  · exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hseq0 _ h0)
  obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ outs := by
    cases outs with
    | nil => exact absurd rfl hne0
    | cons a rest => exact ⟨a, List.Mem.head _⟩
  obtain ⟨hargs0, hch0, -⟩ := hall e0 he0
  have hk0 : e0.1 < d.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hargs0).1
    simpa using this
  obtain ⟨y, hy, hor⟩ := hallC e0.1 hk0
  rw [hy] at hch0
  have hyn : y.1.name = child.1.name := by
    simpa only [Option.map_some, Option.some.injEq] using hch0
  have hre := kidTA_ofO hk0 hMC hy hor
  have hyfind :=
    ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y (List.mem_of_getElem? hy)).1
  rw [hyn, hfind] at hyfind
  have hmcy : mc = y.1 := Option.some.inj hyfind
  obtain ⟨cb, aw, dw, hom⟩ := hmemO e0.1 hk0
  have hy' : y = memModule cb aw dw := KidTA.mem' hre hom
  have hmcm : mc = (memModule cb aw dw).1 := by rw [hmcy, hy']
  have hmn : mn = mc.name := Tools.ShippingOutsExtractedParts.callStmtG_name hcs
  have hfind' : moduleByName D.modules mn = some mc := by
    rw [hmn, (Tools.ShippingHierPremisesBase.moduleByName_mem hfind).2]
    exact hfind
  have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
    congrArg (fun o : Option Sparkle.IR.AST.Module =>
      o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hfind'
  rw [hmcm] at hcs hCm
  exact Tools.ShippingMemKid.kidsMem_one hCm (Tools.ShippingMemKid.mem_conns_noRdata hcs)

end Tools.ShippingGen2
