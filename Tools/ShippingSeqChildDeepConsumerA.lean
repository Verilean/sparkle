import Tools.ShippingSeqChildIfaceDeepA
import Tools.ShippingSeqChildIfaceA
import Tools.ShippingModuleName
-- BUILT (unit SR3n): n1 exit 0 (with #print axioms: propext, Classical.choice, Quot.sound for all three theorems).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Witness `O : RefLawsAOps MkRefd mref cref`, `T : RefLawsATele O.quiet mref cref` (ADDED boundary).

/-! # Depth 2, steps 1 and 3 (unit SR3n): `hsep` DERIVED from leaf grandchildren; the `kidsMasked` consumer

* `hsep_of_leaf_kids` (PROVED): the hypothesis `hsep` of `deepChild_ifaceA` for `c`, DERIVED when every call
  entry's callee is a machine WITHOUT calls (its data and `MachineDefines`/`MachineCloses` as `seqChild_of_realA` takes
  them) and differs from `c`.  Proof: `seqChild_of_realA` gives the served module the name `ofDecl callee` and the
  EMPTY design; `ofDecl` is injective (`Tools.ShippingModuleName.ofDecl_ne`, general, any names).  The only remaining
  fact is `callee ≠ c`, a decidable comparison of two concrete names (supplied by the caller).
* `deepChild_ifaceA'` (PROVED): `deepChild_ifaceA` with `closes` asked only in contexts that satisfy `AdmCtx`
  (strictly weaker than `deepChild_ifaceA`'s every-context premise, which the existing closing generators cannot give: they
  need `hA : AdmCtx`).  Same conclusion.
* `deepChild_kidsMaskedA` (PROVED): ONE parent consumer beyond `core_kids_selfA`: the `kidsMasked` part of the
  GenKid/KidFacts chain on the new boundary — for a `RealChildA O c y` of a machine WITH calls and instance fields,
  `kidsMaskedN y.2.modules y.1.body = true` (every instance of the served module resolves, in the served design, to a
  module with masked outputs), from `core_kidsMaskedN_topA`, whose `hkidM` the caller supplies per grandchild.

`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqChildDeepConsumerA
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

/-- **`hsep` for `c`, derived from leaf grandchildren.** -/
theorem hsep_of_leaf_kids (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData)
    (leaf : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∃ dk : MachineData, dk.ok = true ∧
      dk.shape.body = quote dk.dom
        (fun j => inputExpr dk.shape.binders.length (dk.bpos j))
        (fun j => inputExpr dk.shape.binders.length (dk.vpos j)) dk.packed ∧
      dk.shape.insts = [] ∧
      (∀ o ∈ dk.shape.layout.outs, o.ty.bitWidth = o.width) ∧
      MachineDefines mctx mref cctx cref (d.shape.insts[k]).1 dk.shape ∧
      (∀ (mctx' : Meta.Context) (cctx' : Core.Context),
        MachineCloses mctx' mref cctx' cref (d.shape.insts[k]).1 dk.shape))
    (hne : ∀ (k : Nat) (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ c) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c) := by
  intro k hk y' hy g hg
  obtain ⟨dk, ok, hbody, hno, outTy, entry, closes⟩ := leaf k hk
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O dk ok hbody hno outTy entry closes hy
  rcases List.mem_cons.mp hg with rfl | hin
  · rw [hI.name]
    exact Tools.ShippingModuleName.ofDecl_ne (hne k hk)
  · rw [hI.design] at hin
    cases hin

set_option maxHeartbeats 4000000 in
/-- **`deepChild_ifaceA` with `closes` asked in `AdmCtx` contexts only.** -/
theorem deepChild_ifaceA' (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
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
      (closes mctx' cctx' adm) hw (Or.inr hc)
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
/-- **The `kidsMasked` consumer** (new-boundary counterpart of the `kidsMasked` part of `GenKid`/`KidFacts`): the
instances of the served module of a non-leaf child resolve, in its SERVED design, to modules with masked outputs.
The grandchildren's `outsMaskedN` (`hkidM`) is the caller's, as in `core_kidsMaskedN_topA`. -/
theorem deepChild_kidsMaskedA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidM : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      Tools.ShippingMachineShipsDepth.outsMaskedN y'.1 = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN y.2.modules y.1.body = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, hdes, -⟩ :=
    deepChild_ifaceA' O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  rw [hdes]
  exact core_kidsMaskedN_topA O adm T d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidM
    hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx' adm) hw
    (Or.inr hc) hpost

end Tools.ShippingSeqChildDeepConsumerA

#print axioms Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids
#print axioms Tools.ShippingSeqChildDeepConsumerA.deepChild_ifaceA'
#print axioms Tools.ShippingSeqChildDeepConsumerA.deepChild_kidsMaskedA
