import Tests.Compiler.NoPortsTest
import Tests.Compiler.ParentDesignCheckATest
import Tools.ShippingChecksMaskedLeafA
import Tools.ShippingKidsSelfA
import Tools.ShippingCallsMemPinned
-- BUILT (unit SR3c, par/u-sr3c): sr3c6 exit 0 (sr3c3-5 exit 1: missing opens, decide shapes, intro tenv). In-test audit THROWS on failure. See REPORT-SR3c.md.
-- SCOPE (binding): facts about the CHECK `kidsMaskedN` of the shipped module of `parent`
-- (`ShippingMachineSeqTest`: one call of the leaf register machine `cnt`, a struct result, `instFields ≠ []`) on the
-- NEW boundary; NOT a parent semantic-equivalence head and NOT the endpoint. Not runtime fit.

/-! # Unit SR3c: `hkidM` (masked outputs) for a parent with instance fields — `core_kidsMaskedN_topA` on `parent`

`parent` calls the leaf register machine `cnt` (two outputs `n`, `hit`), so `instFields ≠ []` and
`core_kidsMaskedN_topA` applies.  Supplied here, with NO per-child binder:
* the closing `MachineClosesAtA parent` (`parent_closesA`): `machineClosesAtA_of_memKids'` (the general
  closing; origin `.field k` per entry), `hkid` from `seqChild_of_realA`; data conditions decided;
* `hkidM`: `leaf_real_kidMA` (`Tools/ShippingChecksMaskedLeafA.lean`) from `cnt.machine_leafKid` — the masked
  outputs of the module a `RealChildA` run of `cnt` returned (mergeChecked masks guard); `RealChildA` is a history.

PREMISES left (per theorem): `O`, `hA : AdmCtx`, `T : RefLawsATele` (separate, ADDED boundary), the core run, the
start world `JQ O.quiet D₀ w` + `D₀ = 0 ∨ CacheInvA`, the post-processing disjunction, `MachineDefines` for `parent`
and for `cnt`.  `cnt.machine_closes` (old form: `MachineCloses` in every context) is discharged by the generated
theorem (data decision), as in the old tests. -/

namespace Tests.Compiler.KidsMaskedParentATest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)

/-- `cnt`'s number of argument ports (`seqChild_of_realA`'s form). -/
noncomputable def cntNk : Nat :=
  ((cnt.machineData.shape.binders.take (cnt.machineData.shape.binders.length -
    cnt.machineData.shape.layout.slots.length - cnt.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAtA parent`**: the general closing, two `.field` entries (the two fields of one call) of the leaf `cnt`. -/
theorem parent_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``parent parent.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length),
      (parent.machineData.shape.insts[k]).1 = ``cnt ∧ originAt parent.machineData.shape k = .field k := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt parent.machineData.shape k)
        (parent.machineData.shape.insts[k]).1 y →
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
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := 1) O T hA parent.machineData
    parent.machine_ok parent.machine_body (by first | decide | decide +kernel)
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
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``cnt ≠ ``parent))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ parent.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

set_option maxHeartbeats 4000000 in
/-- **`kidsMaskedN` of `parent`'s shipped module** on the new boundary: `core_kidsMaskedN_topA` with `hkidM` from
`leaf_real_kidMA` of `cnt` and the closing `parent_closesA`. -/
theorem parent_kidsMaskedN_topA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``parent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  have hn : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length),
      (parent.machineData.shape.insts[k]).1 = ``cnt := by
    first | decide | decide +kernel
  have hkidM : ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (parent.machineData.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
    intro k hk y hy
    rw [hn k hk] at hy
    exact Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := cnt.machineData.nIn) O cnt.machineData
      cnt.machine_ok cnt.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hR0 (fun mc cc => cnt.machine_closes mc _ cc _) hy
  exact Tools.ShippingKidsSelfA.core_kidsMaskedN_topA O hA T parent.machineData parent.machine_ok
    parent.machine_body (nDecl := 1) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidM
    hcore entry (parent_closesA O T hA hR0) hw hc hpost

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest Tests.Compiler.ParentDesignCheckATest in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, k) in [(``parent_closesA, 3), (``parent_kidsMaskedN_topA, 8)] do
    auditParentA n k
  -- the hkidM supplier is in the closure of the theorem (not a premise)
  let cl ← depClosure ``parent_kidsMaskedN_topA
  for must in [``Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA, ``Tools.ShippingKidsSelfA.core_kidsMaskedN_topA,
      ``Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'] do
    unless cl.contains must do throwError "SR3c AUDIT FAILED: {must} not in the closure"

#print axioms parent_closesA
#print axioms parent_kidsMaskedN_topA

end Tests.Compiler.KidsMaskedParentATest
