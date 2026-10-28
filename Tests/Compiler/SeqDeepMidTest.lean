import Tests.Compiler.KidsMaskedParentATest
import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingSeqChildDeepMaskedA
-- BUILT (unit SR3n): n3 exit 0 (n2 exit 1: implicit mctx/cctx of hsep_of_leaf_kids); #print axioms standard for all four. In-test audit THROWS on failure.
-- SCOPE (binding): the concrete depth-2 chain `grand -> mid -> cnt` of `ShippingMachineSeqTest`, the CHILD `mid` only
-- (its callee `cnt` is a leaf register machine).  PROVED here, relative to `O`, `T : RefLawsATele` (ADDED boundary), `hA`,
-- and `MachineDefines` of `mid` / `cnt`: `hsep` for `mid` DERIVED (not a premise), `MachineClosesAtA O mctx cctx mid` in every
-- `AdmCtx` context, the interface `deepChild_ifaceA'` for a `RealChildA O mid y`, and `kidsMaskedN y.2.modules y.1.body`.
-- Also (unit SR3o): `mid_outsMaskedA` (`outsMaskedN y.1` of `mid` itself).  Built: o5 exit 0.
-- NOT done (OPEN): the depth-2 GENERATOR (still REFUSED); the `KidFacts.check` field over `RealChildA` (ledger L8x), `epA_Bnd` at depth 2.
-- RealChildA is a history of past synthesis results, not freshness; not runtime fit.
namespace Tests.Compiler.SeqDeepMidTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tests.Compiler.KidsMaskedParentATest (cntNk)

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAtA mid`** (general closing; `nDecl = 2`; callee `cnt`, a leaf). -/
theorem mid_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``mid mid.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length),
      (mid.machineData.shape.insts[k]).1 = ``cnt ∧ originAt mid.machineData.shape k = .field k := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt mid.machineData.shape k)
        (mid.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``cnt) cntNk
        (cnt.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    rw [ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O cnt.machineData cnt.machine_ok
        cnt.machine_body (by decide) (by decide) hR0 (fun mc cc => cnt.machine_closes mc _ cc _) hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := 2) O T hA mid.machineData
    mid.machine_ok mid.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``cnt) (fun _ => cntNk)
    (fun _ => cnt.machineData.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``cnt ≠ ``mid))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ mid.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

/-- **`hsep` for `mid`, DERIVED**: no module of a `RealChildA` of a call entry of `mid` is named `ofDecl mid`.  Inputs: the
leaf `cnt`'s generated facts (`machine_ok`, `machine_body`, no calls, output widths), `MachineDefines cnt`, and the decided
`cnt ≠ mid`. -/
theorem mid_hsep {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (mid.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl ``mid) := by
  have hn : ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length),
      (mid.machineData.shape.insts[k]).1 = ``cnt := by
    first | decide | decide +kernel
  refine Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids (mctx := mctx) (cctx := cctx) O mid.machineData ?_
    (fun k hk => by rw [hn k hk]; decide)
  intro k hk
  rw [hn k hk]
  exact ⟨cnt.machineData, cnt.machine_ok, cnt.machine_body, by decide, by decide, hR0,
    fun mc cc => cnt.machine_closes mc _ cc _⟩

set_option maxHeartbeats 4000000 in
/-- **The interface of a `RealChildA O mid y`** (`deepChild_ifaceA'`) with `hsep` and the closing both SUPPLIED here. -/
theorem mid_ifaceA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y) :
    ∃ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      AdmCtx O.quiet mctx' cctx' ∧ JQ O.quiet (dv w) w ∧ CacheInvA O (cv w) ∧
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``mid [] false)
        mctx' mref cctx' cref w (M, D) w1 ∧
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules ∧ M.name = (Sparkle.IR.ModuleName.ofDecl ``mid) ∧ y.1.body = M.body ∧
      y.1.outputs = M.outputs ∧
      (∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ M.body →
        ∃ mc, Sparkle.IR.Machine.moduleByName D.modules mn = some mc) ∧
      (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
        RealChildA O (mid.machineData.shape.insts[k]).1 y' ∧ (g = y'.1 ∨ g ∈ y'.2.modules) ∧
        ∀ g2 ∈ y'.1 :: y'.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true :=
  Tools.ShippingSeqChildDeepConsumerA.deepChild_ifaceA' O T mid.machineData mid.machine_ok mid.machine_body
    (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

set_option maxHeartbeats 4000000 in
/-- **`kidsMaskedN` of the SERVED `mid`**: every instance of `y.1` resolves in the served design `y.2` to a module with masked
outputs (`deepChild_kidsMaskedA`; `hkidM` of `cnt` from `leaf_real_kidMA`).  (`outsMaskedN y.1` of `mid` itself: `mid_outsMaskedA` below.) -/
theorem mid_kidsMaskedA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN y.2.modules y.1.body = true := by
  have hn : ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length),
      (mid.machineData.shape.insts[k]).1 = ``cnt := by
    first | decide | decide +kernel
  have hkidM : ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (mid.machineData.shape.insts[k]).1 y' →
      Tools.ShippingMachineShipsDepth.outsMaskedN y'.1 = true := by
    intro k hk y' hy
    rw [hn k hk] at hy
    exact Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := cnt.machineData.nIn) O cnt.machineData
      cnt.machine_ok cnt.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hR0 (fun mc cc => cnt.machine_closes mc _ cc _) hy
  exact Tools.ShippingSeqChildDeepConsumerA.deepChild_kidsMaskedA O T mid.machineData mid.machine_ok
    mid.machine_body (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidM (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

set_option maxRecDepth 100000 in
theorem mid_outChars : ∀ o ∈ mid.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem mid_outScalar : ∀ o ∈ mid.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`outsMaskedN` of the SERVED `mid` itself** (SR3o step 1; the `masked` field of `KidFacts mid`): `deepChild_outsMaskedA`
with the argument split `kD = 2` and the output-port data decided; no `hkidM`. -/
theorem mid_outsMaskedA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  exact Tools.ShippingSeqChildDeepMaskedA.deepChild_outsMaskedA O T mid.machineData mid.machine_ok
    mid.machine_body (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) 2
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mid_outChars o ho)) mid_outScalar
    (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
run_cmd Lean.Elab.Command.liftTermElabM do
  let cl ← depClosure ``mid_kidsMaskedA
  for must in [``Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids, ``Tools.ShippingSeqChildDeepConsumerA.deepChild_kidsMaskedA,
      ``mid_closesA, ``Tools.ShippingModuleName.ofDecl_ne, ``Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA] do
    unless cl.contains must do throwError "SR3n AUDIT FAILED: {must} not in the closure of mid_kidsMaskedA"
  logInfo m!"SR3n: mid_hsep derived; mid_kidsMaskedA closure contains hsep_of_leaf_kids, mid_closesA, ofDecl_ne, leaf_real_kidMA"

#print axioms mid_closesA
#print axioms mid_hsep
#print axioms mid_ifaceA
#print axioms mid_kidsMaskedA
#print axioms mid_outsMaskedA

end Tests.Compiler.SeqDeepMidTest
