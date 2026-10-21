import Tools.ShippingKidsSelfA
import Tools.ShippingKidsChildIface
-- BUILT (unit SR3m): d1, d2 exit 0 (d2 with #print axioms: propext, Classical.choice, Quot.sound for both theorems).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Witness `O : RefLawsAOps MkRefd mref cref`, `T : RefLawsATele O.quiet mref cref` (ADDED boundary).

/-! # A NON-LEAF child interface from `RealChildA O c y` that KEEPS the grandchildren's design (unit SR3m)

`Tools.ShippingSeqChildIfaceA.seqChild_of_realA` is the LEAF interface: it needs `d.shape.insts = []` and
concludes `ChildIfaceG` with `design.modules = []`.  The leaf-only conclusion cannot be applied to a child with
calls; there the served design `y.2` must be KEPT: it holds the grandchildren's modules.

`deepChild_ifaceA` (PROVED, relative to `O`, `T`, the child's data conditions, `MachineDefines`,
`MachineClosesAtA` in every context, and `hsep`): for `RealChildA O c y` with `c` having calls, the served module
`y.1` is the post-processing of a core run of `c` (in the contexts/world of the history `RealChildA` records), `y.2.modules`
IS the design `D.modules` of that run (NOT `[]`), and the run's facts hold: the module's name, body/outputs of
`y.1`, every instance of the module resolves in `D`, and every module of `D` is a `RealChildA` grandchild's module or
one of its design.  This is the new-boundary shape of `Tools.ShippingGenKid.GenKid.core` (+ `core_kids_facts`).

`hsep` is the analogue of `GenKid.self`/`GenKid.kid` (the old route got it from `KidNames`): no module produced by
a `RealChildA` grandchild carries the name of `c`.  It is a NAMED hypothesis of the interface, not derived here.

`deepChild_kidsSelfA` (PROVED) is the connection to ONE existing consumer, `Tools.ShippingKidsSelfA.core_kids_selfA`
(the new-boundary `core_kids_self`, which `GenKid.check` uses on the old boundary): its premises `hcore`, `hw`, `hc`
are discharged by the interface, giving for the served design `y.2` that every module is a `RealChildA`
grandchild's module (or of its design) and is resolved by name in `y.2.modules`.

NOT done (OPEN, see REPORT-SR3m.md): `KidFacts`/`GenKid` themselves are stated over the OLD `RealChild`; their
`RealChildA` counterparts are not in the repository.  A history of past synthesis results, not freshness, not
runtime fit. -/

namespace Tools.ShippingSeqChildIfaceDeepA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingKidsChildIface

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **A `RealChildA` of a machine WITH calls: its served module is the post-processing of a core run, its design is
that run's (the grandchildren's), and the run's facts hold.** -/
theorem deepChild_ifaceA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (w w1 : Void IO.RealWorld)
      (M : Sparkle.IR.AST.Module) (D : Design),
      AdmCtx O.quiet mctx' cctx' ∧ JQ O.quiet (dv w) w ∧ CacheInvA O (cv w) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules ∧
      M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ y.1.body = M.body ∧ y.1.outputs = M.outputs ∧
      (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
      (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
        RealChildA O (d.shape.insts[k]).1 y' ∧ (g = y'.1 ∨ g ∈ y'.2.modules) ∧
        ∀ g2 ∈ y'.1 :: y'.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
    have hw : JQ O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have hc : CacheInvA O (cv w) := fun c r h => cache c r h
    have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
      (closes mctx' cctx') hw (Or.inr hc)
    obtain ⟨hMn, hb, ho, hinst, hreal, hassign⟩ :=
      core_kids_facts_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
    refine ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, hdesL ?_, hMn, hb, ho, hinst,
      hreal, hassign⟩
    intro x hx e
    obtain ⟨k, hk, y', hre, hor, -⟩ := hreal x hx
    refine hsep k hk y' hre x ?_ (e.trans hMn)
    rcases hor with heq | hin
    · rw [heq]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hin

set_option maxHeartbeats 4000000 in
/-- **Connection to ONE existing consumer: `core_kids_selfA`** (the new-boundary `core_kids_self`).  Its premises
(the core run, its start world, the cache half) are supplied by `deepChild_ifaceA`'s run; the conclusion is about the
SERVED design `y.2` of the non-leaf child: each module of it is a `RealChildA` grandchild's module or one of its design,
and the served design resolves them to themselves. -/
theorem deepChild_kidsSelfA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∀ g ∈ y.2.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' ∧ (g = y'.1 ∨ g ∈ y'.2.modules) ∧
      moduleByName y.2.modules y'.1.name = some y'.1 ∧
      ∀ g2 ∈ y'.2.modules, moduleByName y.2.modules g2.name = some g2 := by
  obtain ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, -, hdes, -⟩ :=
    deepChild_ifaceA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  rw [hdes]
  exact core_kids_selfA O adm T d ok hbody hC hslots hdomB hins hnomem hcore
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx') hw (Or.inr hc)

end Tools.ShippingSeqChildIfaceDeepA

#print axioms Tools.ShippingSeqChildIfaceDeepA.deepChild_ifaceA
#print axioms Tools.ShippingSeqChildIfaceDeepA.deepChild_kidsSelfA
