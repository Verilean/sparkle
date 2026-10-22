import Tests.Compiler.SeqDeepGenDiffTest
import Tools.ShippingTopShareRun
-- BUILT (unit SR9): i5, i8, i9, i11, a1 exit 0 (dev runs); see REPORT-SR9.md for the final-SHA rebuild.
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

/-! ## `MachineClosesAtStart0` of `topshare` ITSELF, derived (`machineSynth_ne_none4`) -/

theorem wrap3_hsep {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    ∀ (k : Nat) (hk : k < wrap3.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (wrap3.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.wrap3) := by
  have hn := wrap3_insts_acc
  refine Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids (mctx := mctx) (cctx := cctx) O wrap3.machineData ?_
    (fun k hk => by rw [hn k hk]; decide)
  intro k hk
  rw [hn k hk]
  exact ⟨Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData,
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok,
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body, by decide, by decide, hR0,
    fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _⟩

theorem wrap3_hgk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    ∀ (k : Nat) (hk : k < wrap3.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (wrap3.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl accN] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl accN] := by
  intro k hk y' hy g hg
  rw [wrap3_insts_acc k hk] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_body
    (by decide) (by decide) hR0 (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

theorem wrap3_ifaceP {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entry : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.wrap3)
      (Tools.ShippingMachineEntry.machNIn wrap3.machineData.shape)
      (wrap3.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl accN] y.1 y.2 :=
  Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP O T wrap3.machineData wrap3.machine_ok wrap3.machine_body (nDecl := 3)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) 3
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    _ (wrap3_hgk O hR0) (wrap3_hsep O hR0) entry
    (fun _ _ hA' => wrap3_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

/-- group functions of the parent's four calls (`wrap`, `wrap`, `wrap3`, `wrap3`) -/
def nameK (k : Nat) : String :=
  if k < 2 then Sparkle.IR.ModuleName.ofDecl wrapN
  else Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.wrap3
noncomputable def nkK (k : Nat) : Nat :=
  if k < 2 then machNIn Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape
  else machNIn wrap3.machineData.shape
noncomputable def outsK (k : Nat) : List String :=
  if k < 2 then Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.layout.outs.map (·.name)
  else wrap3.machineData.shape.layout.outs.map (·.name)
def namesK (_ : Nat) : List String := [Sparkle.IR.ModuleName.ofDecl accN]

theorem topshare_halias : topshare.machineData.letsAliasOk = true := by first | decide | decide +kernel
theorem topshare_hC : topshare.machineData.callsOk 3 = true := by first | decide | decide +kernel
theorem topshare_hslots : topshare.machineData.ss.length = topshare.machineData.shape.layout.slots.length := by
  first | decide | decide +kernel
theorem topshare_hdomB : ∀ b ∈ topshare.machineData.shape.binders.drop 3, b.2 ≠ .domain := by
  first | decide | decide +kernel
theorem topshare_hlen4 : topshare.machineData.shape.insts.length = 4 := by first | decide | decide +kernel
theorem topshare_hmk : ∀ k (hk : k < topshare.machineData.shape.insts.length),
    Tools.ShippingMemCloses.memKey (originAt topshare.machineData.shape k) = none := by
  first | decide | decide +kernel
theorem topshare_hargsN : ∀ (k : Nat) (hk : k < topshare.machineData.shape.insts.length),
    nkK k = (topshare.machineData.shape.insts[k]).2.1.length := by
  first | decide | decide +kernel
theorem topshare_hfieldOut : ∀ (k : Nat), k < topshare.machineData.shape.insts.length →
    topshare.machineData.shape.instFields.getD k "" ∈ outsK k := by
  first | decide | decide +kernel
theorem topshare_hfieldsNd : ∀ (k : Nat) (hk : k < topshare.machineData.shape.insts.length) (k' : Nat)
    (hk' : k' < topshare.machineData.shape.insts.length),
    (topshare.machineData.shape.insts[k]).1 = (topshare.machineData.shape.insts[k']).1 →
    Tools.ShippingMemCloses.memKey (originAt topshare.machineData.shape k) =
      Tools.ShippingMemCloses.memKey (originAt topshare.machineData.shape k') →
    (topshare.machineData.shape.insts[k]).2.1 = (topshare.machineData.shape.insts[k']).2.1 →
    topshare.machineData.shape.instFields.getD k "" = topshare.machineData.shape.instFields.getD k' "" → k = k' := by
  first | decide | decide +kernel
theorem topshare_hsep : ∀ (k : Nat) (hk : k < topshare.machineData.shape.insts.length) (k' : Nat)
    (hk' : k' < topshare.machineData.shape.insts.length), nameK k = nameK k' →
    (topshare.machineData.shape.insts[k]).1 = (topshare.machineData.shape.insts[k']).1 ∧
      Tools.ShippingMemCloses.memKey (originAt topshare.machineData.shape k) =
        Tools.ShippingMemCloses.memKey (originAt topshare.machineData.shape k') := by
  first | decide | decide +kernel
theorem topshare_hparent : ∀ (k : Nat), k < topshare.machineData.shape.insts.length →
    nameK k ≠ Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.topshare := by
  first | decide | decide +kernel
theorem topshare_hfresh : ∀ (gi : Nat) (k : Nat), k < topshare.machineData.shape.insts.length →
    ∀ o ∈ topshare.machineData.shape.layout.outs, o.name ≠ s!"inst{gi}_{nameK k}" := by
  intro gi k _ o ho
  have : ∀ o ∈ topshare.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i' := by
    first | decide | decide +kernel
  exact Tools.ShippingCallsGate.instName_ne_of_head (this o ho) gi _
theorem topshare_hparentD : ∀ (k : Nat), k < topshare.machineData.shape.insts.length →
    Sparkle.IR.ModuleName.ofDecl ``Tests.Compiler.SeqDeepGenDiffTest.topshare ∉ namesK k := by
  first | decide | decide +kernel

/-- **THE PARENT'S OWN RUN AT `wrap`, `wrap3`, `acc` (`topshare`), without a `MachineClosesAtA` premise on `topshare`.**
Same conclusion as `topshare_entry_run_inst`; the parent's no-fallback premise is DERIVED at the entry's start world
(`machineSynth_ne_none4`: `closeLets` accepted, the closing returns `closeInstsG … [y₁,y₁,y₂,y₂]` which is `some` by
`closeInstsG_of_kidsPT` with `hcross` from `topshare_quad`; the children's interfaces `ChildIfaceP` from `RealChildA`:
the end cache is a `CacheInvA` cache; the data facts are kernel-checked). PREMISES (named): `O`, `hA`, `T`,
`MachineDefines` of `topshare`, `wrap`, `wrap3`, `acc`. The generator still REFUSES `topshare`. -/
theorem topshare_entry_run_inst' {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
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
  have closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape := by
    intro tenv b w9 r w10 hj hcv hr
    exact machineSynth_ne_none4 O hA (by decide) h1 h1' h2 h2' topshare.machineData topshare.machine_ok
      topshare.machine_body topshare_halias topshare_hC topshare_hslots topshare_hdomB
      (by first | decide | decide +kernel) (by first | decide | decide +kernel) hP topshare_hlen4 topshare_hmk
      _ _ (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0) topshare_calleeOKs_ne
      nameK nkK outsK namesK
      (fun y hy k hk => by
        have := topdiff2.epD2M0_C_ifaceP O T entryW hR0 hy
        simpa [nameK, nkK, outsK, namesK, if_pos hk] using this)
      (fun y hy k hk2 hk4 => by
        have := wrap3_ifaceP O T hA entryW3 hR0 hy
        simpa [nameK, nkK, outsK, namesK, if_neg (Nat.not_lt.mpr hk2)] using this)
      topshare_hargsN topshare_hfieldOut topshare_hfieldsNd topshare_hsep topshare_hparent topshare_hfresh
      topshare_hparentD hj hcv hr
  exact topshare_entry_run4' O hA (by decide) h1 h1' h2 h2' topshare.machineData topshare.machine_ok
    topshare.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel) hP
    entryT closes0 _ _ (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0)
    topshare_calleeOKs_ne hw h

/-! ## The expected WHOLE statement, written independently, compared by `isDefEq`; type-correct mutations are REJECTED -/

/-- The expected statement of `topshare_entry_run_inst'`, written out by hand (premises AND conclusion). `v = 0` is the
expected statement; `v = 1…8, 10` are TYPE-CORRECT mutations that must be rejected:
1 the children list `[y₁,y₂,y₁,y₂]`; 2 the cache entries swapped (`wrap ↦ y₂`); 3 the shared-leaf clause puts the module in
`y₁` twice; 4 the end world at depth `1`; 5 the children list `[y₁,y₂]`; 6 `hcross` for `(y₁,y₁)`; 7 the start world at
depth `1`; 8 the end cache is that of the START world; 10 the closing's lets are not required.
(An extra premise, e.g. `MachineClosesAtA` of `topshare` as in `topshare_entry_run_inst`, is rejected by the premise-name check.) -/
def TopShareFull (v : Nat) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O (if v = 7 then 1 else 0) w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w'),
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 : Void IO.RealWorld),
      (if v = 10 then True else Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t') ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields
        (if v = 1 then [y₁, y₂, y₁, y₂] else if v = 5 then [y₁, y₂] else [y₁, y₁, y₂, y₂])
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O (if v = 4 then 1 else 0) w' ∧ cv w' = cv (if v = 8 then w else w10) ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? wrapN = some (if v = 2 then y₂ else y₁) ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some (if v = 2 then y₁ else y₂) ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf (if v = 6 then y₁ else y₂), a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ (if v = 3 then y₁ else y₂).2.modules

open Lean Meta Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let thm := ``Tests.Compiler.TopShareInstTest.topshare_entry_run_inst'
  let ty := (← getConstInfo thm).type
  -- the premises are exactly these (in particular NO `closes` premise on `topshare` itself)
  forallTelescope ty fun xs _ => do
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "O", "T", "hA", "entryT", "entryW", "entryW3", "hR0", "w", "w'", "y", "hw", "h"] do
      throwError "SR9 AUDIT FAILED: premises of {thm} are {names}"
  if ty.hasMVar then throwError "SR9 AUDIT FAILED: metavariables in the statement"
  Meta.check ty
  let full (v : Nat) : Lean.Expr := mkApp (mkConst ``Tests.Compiler.TopShareInstTest.TopShareFull) (mkNatLit v)
  let mut rejected : List Nat := []
  unless ← isDefEq ty (full 0) do throwError "SR9 AUDIT FAILED: the statement of {thm} differs from the hand-written expected statement"
  for v in [1, 2, 3, 4, 5, 6, 7, 8, 10] do
    if ← isDefEq ty (full v) then throwError "SR9 AUDIT FAILED: the mutation {v} of the expected statement was ACCEPTED"
    rejected := v :: rejected
  logInfo m!"SR9 STATEMENT AUDIT: {thm} equals the hand-written TopShareFull 0 (isDefEq, no mvars, Meta.check); premises exactly [O, T, hA, entryT, entryW, entryW3, hR0, hw, h]; type-correct mutations rejected: {rejected.reverse}"

end Tests.Compiler.TopShareInstTest

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for n in [``Tests.Compiler.TopShareInstTest.wrap_calleeOK, ``Tests.Compiler.TopShareInstTest.wrap3_calleeOK,
      ``Tests.Compiler.TopShareInstTest.topshare_entry_run_inst, ``Tests.Compiler.TopShareInstTest.topshare_entry_run_inst'] do
    Tests.Compiler.ChildVertAuditTest.stdAxioms n
    let s ← Tests.Compiler.ChildVertAuditTest.depClosure n
    let hs := Tests.Compiler.ChildVertAuditTest.hits s
    unless hs.isEmpty do throwError "SR9 AUDIT FAILED: {n} depends on the old boundary: {hs}"
    logInfo m!"SR9 AUDIT: {n}: closure {s.size} constants, standard axioms only, no RefLaws / RefLawsCore / toAOps / toA"

#print axioms Tests.Compiler.TopShareInstTest.wrap_calleeOK
#print axioms Tests.Compiler.TopShareInstTest.wrap3_calleeOK
#print axioms Tests.Compiler.TopShareInstTest.topshare_entry_run_inst
#print axioms Tests.Compiler.TopShareInstTest.topshare_entry_run_inst'
