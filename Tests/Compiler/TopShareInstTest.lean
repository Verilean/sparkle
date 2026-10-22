import Tests.Compiler.SeqDeepGenDiffTest
import Tools.ShippingTopShareRun
-- UNBUILT (unit SR9): see REPORT-SR9.md for run names / exits at the final committed SHA.
-- SCOPE (binding): INSTANTIATION of `Tools.ShippingTopShareRun.topshare_entry_run4` at the real declarations
-- `topshare` (callees `wrap`, `wrap3`; the shared leaf `acc`) of `Tests/Compiler/SeqDeepGenDiffTest.lean`.  The generator still REFUSES
-- `topshare` (no guard / generator change).  PROVED here: the data premises about `wrap`, `wrap3`, `acc`, `topshare` (kernel-checked
-- `decide`, the stored `machineData`).  PREMISES (named, in the statement of `topshare_entry_run_inst`): `O`, `hA`, `T`, `MachineDefines`
-- of `topshare`, `wrap`, `wrap3`, `acc` (the entry's reads of the environment), and `MachineClosesAtA` of `topshare` itself.
namespace Tests.Compiler.TopShareInstTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA
open Tools.ShippingMachineEntry
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingChildRunAKids Tools.ShippingChildInv
open Tests.Compiler.SeqDeepGenDiffTest
open Tools.ShippingTopShareRun Tools.ShippingSharedLeafNL

abbrev wrapN : Lean.Name := ``Tests.Compiler.SeqDeepGenInstTest.wrap
abbrev accN : Lean.Name := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc

/-- the call structure of `topshare` and `wrap3`, KERNEL-checked -/
theorem topshare_callees : topshare.machineData.shape.insts.map (·.1) =
    [wrapN, wrapN, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3] := by decide

theorem wrap3_insts_acc : ∀ (k : Nat) (hk : k < wrap3.machineData.shape.insts.length),
    (wrap3.machineData.shape.insts[k]).1 = accN := by
  first | decide | decide +kernel

theorem wrap_insts_acc : ∀ (k : Nat) (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length),
    (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 = accN := by
  first | decide | decide +kernel

theorem origin_child_none (o : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (h : Tools.ShippingMemCloses.memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [Tools.ShippingMemCloses.memKey])

theorem wrap3_hent : ∀ (k : Nat) (hk : k < wrap3.machineData.shape.insts.length),
    (wrap3.machineData.shape.insts[k]).1 = accN ∧
      Tools.ShippingMemCloses.memKey (originAt wrap3.machineData.shape k) = none := by
  first | decide | decide +kernel

/-- `MachineClosesAtA` of `wrap3` (the textual instance of the generator's per-callee `closesA` for `C = wrap3`, `G = acc`) -/
theorem wrap3_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape := by
  have hent := wrap3_hent
  have hkid : ∀ (k : Nat) (hk : k < wrap3.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt wrap3.machineData.shape k)
        (wrap3.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl accN) topdiff2.epD2M0_G_nk
        (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    unfold Tools.ShippingCallsMemA.KidTA at hy
    rw [origin_child_none _ ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok
        Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body (by decide) (by decide) hR0
        (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := 3) O T hA wrap3.machineData
    wrap3.machine_ok wrap3.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl accN) (fun _ => topdiff2.epD2M0_G_nk)
    (fun _ => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : accN ≠ ``Tests.Compiler.SeqDeepGenDiffTest.wrap3))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ wrap3.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

/-- `LeafOK` of `acc` from its stored data, `MachineDefines` of `acc` the only premise. -/
theorem acc_leafOK {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    LeafOK mctx mref cctx cref accN :=
  ⟨Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData,
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok,
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body, by decide, by decide, hR0,
    fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _⟩

theorem wrap_instTagged_acc : ∀ x ∈ Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.instTagged,
    x.1 = accN ∧ x.2.child? = none := by
  first | decide | decide +kernel

theorem wrap3_instTagged_acc : ∀ x ∈ wrap3.machineData.shape.instTagged,
    x.1 = accN ∧ x.2.child? = none := by
  first | decide | decide +kernel

/-- **`CalleeOK` of `wrap`** (the callee with the shared leaf `acc`): everything except the premises `entry` (`MachineDefines`
of `wrap`) and `hR0` (`MachineDefines` of `acc`) and `T` (the telescope boundary of the existing generator). -/
theorem wrap_calleeOK {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref wrapN
      Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    CalleeOK O mctx cctx wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData :=
  ⟨Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok, Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body,
    ⟨3, by first | decide | decide +kernel, by first | decide | decide +kernel⟩,
    by first | decide | decide +kernel, by first | decide | decide +kernel, by first | decide | decide +kernel,
    fun x hx => by
      obtain ⟨h1, h2⟩ := wrap_instTagged_acc x hx
      rw [h1]; exact ⟨h2, acc_leafOK hR0⟩,
    fun k hk => by rw [wrap_insts_acc k hk]; decide,
    entry, topdiff2.epD2M0_C_closesA O T hA hR0⟩

theorem wrap3_calleeOK {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3
      wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    CalleeOK O mctx cctx ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData :=
  ⟨wrap3.machine_ok, wrap3.machine_body,
    ⟨3, by first | decide | decide +kernel, by first | decide | decide +kernel⟩,
    by first | decide | decide +kernel, by first | decide | decide +kernel, by first | decide | decide +kernel,
    fun x hx => by
      obtain ⟨h1, h2⟩ := wrap3_instTagged_acc x hx
      rw [h1]; exact ⟨h2, acc_leafOK hR0⟩,
    fun k hk => by rw [wrap3_insts_acc k hk]; decide,
    entry, wrap3_closesA O T hA hR0⟩

end Tests.Compiler.TopShareInstTest

#print axioms Tests.Compiler.TopShareInstTest.wrap_calleeOK
#print axioms Tests.Compiler.TopShareInstTest.wrap3_calleeOK
