import Tools.ShippingKidsSelfA
import Tools.ShippingSrm4Core1
-- BUILT (unit SRM5): s5e2 exit 0 (dev run, default heartbeats, no heartbeat option); the final-SHA rebuild is in REPORT-SRM5.md.
-- SCOPE (binding): INSTANCE-TARGET IDENTIFICATION.  An instance statement `inst mn _ _` of the module `M` a machine run produced (`MachineRanA O … M D`) names, BY NAME, the module of the CHILD of some call `k`:
-- `mn = y.1.name`, `moduleByName D.modules mn = some y.1` and the child's own design resolves in `D`, where `y = children[k]` is the run's `k`-th child — NOT a module of that child's own design (`y.2.modules`).  Together with the closing's
-- `ChildrenRealA` this gives `RealChildA O (insts[k]).1 y` (ordinary entry: `hnomem`) or the memory-origin disjunct (`(insts-origins k).child? = some y`).
-- Proved from the closing alone (`closeInsts_insts` / `closeInstsG_insts`, `closeInsts_names` / `closeInstsG_names`) and `closedBody_kinds_of_run` (the closed machine has no instance of its own); no new premise.
-- `RealChildA` is a history of past synthesis results, not freshness or runtime fit.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm5Ident
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingChildInv Tools.ShippingClosedKinds
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingCallsMemA (KidTA)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingSrm4Core1 (kidTA_ofO)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **Instance-target identification (general closing)**: every instance statement of the run's module names, by name, the module of call `k`'s child `y`; `y` is the origin-built child or a `RealChildA`. -/
theorem inst_target_ranA (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ mn i conns, Stmt.inst mn i conns ∈ M.body →
      ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
        ((d.shape.instOrigins.getD k .ord).child? = some y ∨ RealChildA O (d.shape.insts[k]).1 y) ∧
        mn = y.1.name ∧ moduleByName D.modules mn = some y.1 ∧
        (∀ g ∈ y.2.modules, moduleByName D.modules g.name = some g) ∧
        (d.shape.instFields ≠ [] → KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y) := by
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  have h0 : ∀ st ∈ (closeMachine d.shape.layout t').body, isInst st = false := fun st hs => by
    have := List.all_eq_true.mp hseq0 st hs
    cases st <;> simp_all [seqStmtOk, isInst]
  intro mn i conns hm
  rcases hmt with ⟨hi, hM, hD⟩ | ⟨hne, children, hcc, hreal⟩
  · subst hM
    exact absurd (h0 _ hm) (by simp [isInst])
  have hMC : d.shape.instFields ≠ [] → MemChildren d.shape children := by
    intro hf
    rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩
    · exact absurd hf0 hf
    · exact h
  obtain ⟨hlenC, hall⟩ := hreal
  have hfin : ∀ (k : Nat) (y : Res), children[k]? = some y → mn = y.1.name →
      moduleByName D.modules y.1.name = some y.1 → (∀ g ∈ y.2.modules, moduleByName D.modules g.name = some g) →
      ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
        ((d.shape.instOrigins.getD k .ord).child? = some y ∨ RealChildA O (d.shape.insts[k]).1 y) ∧
        mn = y.1.name ∧ moduleByName D.modules mn = some y.1 ∧
        (∀ g ∈ y.2.modules, moduleByName D.modules g.name = some g) ∧
        (d.shape.instFields ≠ [] → KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y) := by
    intro k y hy hmn hres hres2
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨y', hy', hor⟩ := hall k hk
    rw [hy] at hy'
    cases hy'
    exact ⟨k, hk, y, hor, hmn, hmn ▸ hres, hres2, fun hf => kidTA_ofO hk (hMC hf) hy hor⟩
  rcases hcc with ⟨hfe, hI⟩ | ⟨hfe, hG, hmc⟩
  · rcases Tools.ShippingMachineInst.closeInsts_insts hI _ hm rfl with h0' | ⟨k, args, child, mc, hargs, hchild, hmc', hcs⟩
    · exact absurd (h0 _ h0') (by simp [isInst])
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, hstE⟩ := hcs
    simp only [Stmt.inst.injEq] at hstE
    have hn : mc.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc'
    exact hfin k child hchild (hstE.1.trans hn)
      ((Tools.ShippingChildServe.closeInsts_names hI).2 child (List.mem_of_getElem? hchild))
      ((Tools.ShippingChildServe.closeInsts_acyclic hI).2.2.2 child (List.mem_of_getElem? hchild))
  · rcases Tools.ShippingMachineInstG.closeInstsG_insts hG _ hm rfl with h0' | ⟨args, outs, child, mc, hcs, hmc', hne', hall'⟩
    · exact absurd (h0 _ h0') (by simp [isInst])
    obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, hstE⟩ := hcs
    simp only [Stmt.inst.injEq] at hstE
    have hn : mc.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc'
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil outs hne'
    obtain ⟨-, hnm, -⟩ := hall' e he
    cases hy : children[e.1]? with
    | none => rw [hy] at hnm; cases hnm
    | some y =>
      rw [hy, Option.map_some, Option.some.injEq] at hnm
      have hnames := (Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y (List.mem_of_getElem? hy)
      exact hfin e.1 y hy (hstE.1.trans (hn.trans hnm.symm)) hnames.1 hnames.2

/-- **Ordinary entries** (`hnomem`): the statement's target is the `RealChildA` child `y` of call `k`, by name: `mn = y.1.name`, resolved to `y.1` itself (not a module of `y.2.modules`). -/
theorem inst_target_ord_ranA (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ∀ mn i conns, Stmt.inst mn i conns ∈ M.body →
      ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
        RealChildA O (d.shape.insts[k]).1 y ∧ mn = y.1.name ∧ moduleByName D.modules mn = some y.1 ∧
        ∀ g ∈ y.2.modules, moduleByName D.modules g.name = some g := by
  intro mn i conns hm
  obtain ⟨k, hk, y, hor, hmn, hres, hres2, -⟩ := inst_target_ranA O d ok hbody hC hslots hdomB ran mn i conns hm
  rcases hor with h | h
  · rw [nomem_tag hnomem hk] at h; cases h
  · exact ⟨k, hk, y, h, hmn, hres, hres2⟩

end Tools.ShippingSrm5Ident

#print axioms Tools.ShippingSrm5Ident.inst_target_ranA
#print axioms Tools.ShippingSrm5Ident.inst_target_ord_ranA
