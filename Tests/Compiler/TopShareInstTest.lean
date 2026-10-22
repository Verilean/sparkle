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
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildPinC Tools.ShippingChildDepthC
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit

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

theorem topshare_instTagged_names : topshare.machineData.shape.instTagged.map (·.1) =
    [wrapN, wrapN, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3, ``Tests.Compiler.SeqDeepGenDiffTest.wrap3] := by
  first | decide | decide +kernel

theorem topshare_instTagged_child : ∀ x ∈ topshare.machineData.shape.instTagged, x.2.child? = none := by
  first | decide | decide +kernel

/-- the parent's call list has exactly the shape `[c₁, c₁, c₂, c₂]` of `topshare_entry_run4` (origins: all without a child) -/
theorem topshare_instTagged_shape : ∃ o₁ o₁' o₂ o₂' : Sparkle.Compiler.MachInstOrigin.InstOrigin,
    o₁.child? = none ∧ o₁'.child? = none ∧ o₂.child? = none ∧ o₂'.child? = none ∧
    topshare.machineData.shape.instTagged = [(wrapN, o₁), (wrapN, o₁'),
      (``Tests.Compiler.SeqDeepGenDiffTest.wrap3, o₂), (``Tests.Compiler.SeqDeepGenDiffTest.wrap3, o₂')] := by
  have h1 := topshare_instTagged_names
  have h2 := topshare_instTagged_child
  revert h1 h2
  generalize topshare.machineData.shape.instTagged = L
  intro h1 h2
  rcases L with _ | ⟨⟨n1, o1⟩, _ | ⟨⟨n2, o2⟩, _ | ⟨⟨n3, o3⟩, _ | ⟨⟨n4, o4⟩, _ | ⟨e, L⟩⟩⟩⟩⟩
  · simp at h1
  · simp at h1
  · simp at h1
  · simp at h1
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    obtain ⟨e1, e2, e3, e4⟩ := h1
    subst e1 e2 e3 e4
    exact ⟨o1, o2, o3, o4, h2 (wrapN, o1) (by simp), h2 (wrapN, o2) (by simp), h2 (``Tests.Compiler.SeqDeepGenDiffTest.wrap3, o3) (by simp), h2 (``Tests.Compiler.SeqDeepGenDiffTest.wrap3, o4) (by simp), rfl⟩
  · simp at h1

theorem topshare_calleeOKs_ne : ∀ k (hk : k < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length),
    (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k]).1 ≠ ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 := by
  intro k hk; rw [wrap_insts_acc k hk]; decide

/-- **THE PARENT'S OWN RUN AT `wrap`, `wrap3`, `acc` (`topshare`).** A returning run of `synthesizeCombinational topshare`
from a `JQC O 0` world: the machine synthesis's result is the pure `closeInstsG` of `[y₁, y₁, y₂, y₂]`; the end cache is
`CacheCoh` with `y₁` at `wrap`, `y₂` at `wrap3`; the `hcross` shape holds for `(y₁, y₂)`; and for every pair of calls (one of
`wrap`, one of `wrap3`) to the shared leaf `acc`, the cache's entry `e` has its module `e.1` inside BOTH designs.
PREMISES (named): `O`, `hA`, `T` (`RefLawsATele`, as the existing generator), `MachineDefines` of `topshare`, `wrap`, `wrap3`,
`acc`, `MachineClosesAtA` of `topshare` ITSELF (not derived in this change; see REPORT-SR9). The generator still REFUSES `topshare`. -/
theorem topshare_entry_run_inst {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    (closesT : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 : Void IO.RealWorld),
      Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂]
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? wrapN = some y₁ ∧ (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules := by
  obtain ⟨o₁, o₁', o₂, o₂', h1, h1', h2, h2', hP⟩ := topshare_instTagged_shape
  exact topshare_entry_run4 O hA (by decide) h1 h1' h2 h2' topshare.machineData topshare.machine_ok
    topshare.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel) hP
    entryT closesT _ _ (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0)
    topshare_calleeOKs_ne hw h

end Tests.Compiler.TopShareInstTest

#print axioms Tests.Compiler.TopShareInstTest.wrap_calleeOK
#print axioms Tests.Compiler.TopShareInstTest.wrap3_calleeOK
#print axioms Tests.Compiler.TopShareInstTest.topshare_entry_run_inst
