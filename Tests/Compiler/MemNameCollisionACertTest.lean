import Tests.Compiler.MemNameCollisionCertTest
import Tools.ShippingCallsMemPinned
import Tools.ShippingSeqChildIfaceA
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit CPX): see REPORT-CPX.md for run names / exits.

/-! # The MemNameCollision parents on the NEW boundary (unit CPX)

TARGET-ONLY (NOT in `Tests.AllTests`), like `MemNameCollisionCertTest` which it imports: that file
declares its own `SparkleMem.sync.4.8` (the leaf register `fakeReg`), a different function from
`MemNameCollisionTest`'s, and the two cannot be in one environment. Hence this file is not in the
`ChildVertAuditTest` theorem list either (that file is in AllTests); instead it carries its own
in-file audit at the end (run_cmd, THROWS): standard axioms and no `RefLaws`/`RefLawsCore`/`toAOps`/`toA`
in the closure (walk follows definition, theorem AND opaque bodies), using ChildVertAuditTest's walker.

`collSame_closesA` / `collArgs_closesA`: `MachineClosesAtA` of the two parents (a synchronous 4/8 memory
and a call of the leaf register `fakeReg` under the memory's placeholder name, origins `.mem false 4 8`
and `.ord`) by `Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'` (no `hdistOrd`). The ord
child's interface `hkid` comes from `Tools.ShippingSeqChildIfaceA.seqChild_of_realA` (a `RealChildA`,
not the old `InvW`/`RealChild`).

REMAINING PREMISES (per instance): `O : RefLawsAOps`, `T : RefLawsATele` (separate assumption family),
`hA : AdmCtx`, `MachineDefines syncName fakeD.shape` (the reflection of the colliding declaration).
Data/name conditions are discharged by `decide` as in the old file. `RealChildA` is a history of past
synthesis results, not semantic correctness; not a runtime-fit proof. -/
namespace Sparkle.Tests.Compiler.MemNameCollisionCertTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingInstTagged (KidT originAt)
open Tools.ShippingMemCloses (ChildIfaceP)

/-- **A `RealChildA` of the colliding declaration has the interface** (port of `fake_iface`). -/
theorem fake_ifaceA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape)
    {y : Tools.ShippingChildInv.Res} (hy : Tools.ShippingChildCacheA.RealChildA O syncName y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl syncName) fakeNk
      (fakeD.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
  have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O fakeD fake_ok fake_body fake_leaf
    fake_outTy hRc (fun mc cc => fake_closes mc _ cc _) hy
  exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
    (fun hx => nomatch hx)

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAtA` of a parent whose call entries are a synchronous 4/8
memory and calls of the declaration carrying that memory's placeholder name**
— by the origin-based closing, from the reflection of that declaration only.
The data conditions are premises here, decided per parent below. -/
theorem closes_of_collisionA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {declName : Name}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (hent : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).1 = syncName ∧
        (originAt d.shape k = .mem false 4 8 ∨ originAt d.shape k = .ord))
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nkO (originAt d.shape k) = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsO (originAt d.shape k))
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      Tools.ShippingMemCloses.memKey (originAt d.shape k) =
        Tools.ShippingMemCloses.memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (houtHead : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i')
    (hpar : Sparkle.IR.ModuleName.ofDecl syncName ≠ Sparkle.IR.ModuleName.ofDecl declName)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape := by
  have hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y →
      ChildIfaceP (nameO (originAt d.shape k)) (nkO (originAt d.shape k))
        (outsO (originAt d.shape k)) (namesO (originAt d.shape k)) y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    rcases ho with ho | ho
    · rw [ho] at hy ⊢
      rcases hy with hy | ⟨hy, -⟩
      · have e : y = Sparkle.Compiler.MachMemory.memModule false 4 8 := (Option.some.inj hy).symm
        subst e
        exact Tools.ShippingMemCloses.memIface false 4 8
      · exact absurd (Tools.ShippingInstTagged.child?_mem false 4 8) (by rw [hy]; exact fun h => nomatch h)
    · rw [ho] at hy ⊢
      rcases hy with hy | ⟨-, hre⟩
      · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
      · rw [hn] at hre
        exact fake_ifaceA O hRc hre
  have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameO (originAt d.shape k) = nameO (originAt d.shape k') →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (originAt d.shape k) =
          Tools.ShippingMemCloses.memKey (originAt d.shape k') := by
    intro k hk k' hk' he
    obtain ⟨hn, ho⟩ := hent k hk
    obtain ⟨hn', ho'⟩ := hent k' hk'
    refine ⟨hn.trans hn'.symm, ?_⟩
    rcases ho with ho | ho <;> rcases ho' with ho' | ho'
    · rw [ho, ho']
    · rw [ho, ho'] at he
      exact absurd he.symm (decl_ne_mem syncName)
    · rw [ho, ho'] at he
      exact absurd he (decl_ne_mem syncName)
    · rw [ho, ho']
  have hparent : ∀ (k : Nat), k < d.shape.insts.length →
      nameO (originAt d.shape k) ≠ Sparkle.IR.ModuleName.ofDecl declName := by
    intro k hk
    rcases (hent k hk).2 with ho | ho
    · rw [ho]
      exact fun e => decl_ne_mem declName e.symm
    · rw [ho]
      exact hpar
  have hparentD : ∀ (k : Nat), k < d.shape.insts.length →
      Sparkle.IR.ModuleName.ofDecl declName ∉ namesO (originAt d.shape k) := by
    intro k hk
    rcases (hent k hk).2 with ho | ho
    · rw [ho]
      exact decl_notin_mem declName
    · rw [ho]
      show Sparkle.IR.ModuleName.ofDecl declName ∉ ([] : List String)
      exact fun hx => nomatch hx
  have hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (originAt d.shape k) =
          Tools.ShippingMemCloses.memKey (originAt d.shape k')) →
      nameO (originAt d.shape k) ∉ namesO (originAt d.shape k') ∧
        ∀ x ∈ namesO (originAt d.shape k), x ∉ namesO (originAt d.shape k') := by
    intro k hk k' hk' hne
    obtain ⟨hn, ho⟩ := hent k hk
    obtain ⟨hn', ho'⟩ := hent k' hk'
    rcases ho with ho | ho <;> rcases ho' with ho' | ho'
    · exact (hne ⟨hn.trans hn'.symm, by rw [ho, ho']⟩).elim
    · rw [ho, ho']
      show (memModule false 4 8).1.name ∉ ([] : List String) ∧
        ∀ x ∈ [(memModule false 4 8).1.name], x ∉ ([] : List String)
      exact ⟨fun hx => (nomatch hx), fun _ _ hx => nomatch hx⟩
    · rw [ho, ho']
      show Sparkle.IR.ModuleName.ofDecl syncName ∉ [(memModule false 4 8).1.name] ∧
        ∀ x ∈ ([] : List String), x ∉ [(memModule false 4 8).1.name]
      exact ⟨decl_notin_mem syncName, fun _ hx => nomatch hx⟩
    · exact (hne ⟨hn.trans hn'.symm, by rw [ho, ho']⟩).elim
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) O T hA d ok hbody halias hC hslots hdomB hfne
    (fun k => nameO (originAt d.shape k)) (fun k => nkO (originAt d.shape k))
    (fun k => outsO (originAt d.shape k)) (fun k => namesO (originAt d.shape k))
    hkid hargsN hfieldOut hfieldsNd hsep hparent
    (fun gi _ _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (houtHead o ho) gi _)
    hparentD hdisjD


/-! ## The two collision parents on the new boundary -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAtA collSameR`**. -/
theorem collSame_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``collSameR collSameD.shape :=
  closes_of_collisionA (declName := ``collSameR) (nDecl := 4) O T hA collSameD collSame_ok collSame_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel)) hRc

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAtA collArgsR`**. -/
theorem collArgs_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``collArgsR collArgsD.shape :=
  closes_of_collisionA (declName := ``collArgsR) (nDecl := 4) O T hA collArgsD collArgs_ok collArgs_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel)) hRc

#print axioms Tools.ShippingSeqChildIfaceA.seqChild_of_realA
#print axioms closes_of_collisionA
#print axioms collSame_closesA
#print axioms collArgs_closesA

end Sparkle.Tests.Compiler.MemNameCollisionCertTest

/-! ## In-file audit (THROWS) -/
open Lean Elab Command Meta Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingSeqChildIfaceA.seqChild_ifaceA, ``Tools.ShippingSeqChildIfaceA.seqChild_of_realA,
      ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.closes_of_collisionA,
      ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collSame_closesA,
      ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collArgs_closesA] do
    stdAxioms n
    let s ← depClosure n
    let hs := hits s
    unless hs.isEmpty do
      throwError "CPX AUDIT FAILED: {n} depends on the old boundary: {hs}"
    for must in [``Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'] do
      if n == ``Sparkle.Tests.Compiler.MemNameCollisionCertTest.collSame_closesA && !s.contains must then
        throwError "CPX AUDIT FAILED: {n} does not use {must}"
    let (axs, ops, exts, impls) ← boundary s
    logInfo m!"CPX AUDIT {n}: closure {s.size} constants, no RefLaws/RefLawsCore/toAOps/toA; BOUNDARY axioms {axs}; opaque {ops.length}; extern {exts.length}; implemented_by {impls.length} (structural counts, not a runtime-fit proof)"
