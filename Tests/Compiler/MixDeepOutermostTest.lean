import Tests.Compiler.CacheChainClosedTest
import Tests.Compiler.CallsKidsSharedMixDeepTest
import Tools.ShippingCacheCoherentOuter

variable {tenv : Lean.Environment}

/-! # `mixDeep`: the closing for OUTERMOST starts, from reflections only

WRITTEN, NOT BUILT (par/a-38). Target-only; not in `Tests.AllTests`. Every
data condition is a kernel `decide`; nothing evaluates reflected data in
compiled code. NO EXISTING ENDPOINT OR GENERATOR IS TOUCHED, and nothing
here is the existing endpoint `mixDeep.machine_design_noPortsNR2` losing a
premise.

`mixDeep → {mid2 → midH → rcH, midH → rcH, cnt}`.

* `cnt_entryOk`, `mid2_entryOk`: `EntryOk` from reflections only (with
  `midH_entryOk_closed`, `rcH_entryStill` of `CacheChainClosedTest`, BUILT);
* `mixDeep_closes_prov`: the machine synthesis of `mixDeep` does not fall
  back from an invariant world of positive depth whose cache satisfies
  `Prov` — the built relative closing `mixDeep.closes_shared` consumed by
  `machine_closes_of_entryOk`;
* **`mixDeep_closes_outermost`** — SCOPE: OUTERMOST STARTS ONLY. For a core
  run of `mixDeep` from a world where the synthesis ref is set, the
  diagnostics are quiet and the synthesis depth reads 0 (the depth-0 half of
  `ChildBnd`, for the witness `L`): the machine synthesis the entry performs
  returns the run's result (it does not fall back). Premises: the five
  reflections and that start condition. It is what `MachineClosesAt mixDeep`
  provides AT THAT ONE WORLD; it is NOT `MachineClosesAt mixDeep` (every
  invariant world of positive depth), and the built endpoint — which takes
  `MachineClosesAt mixDeep` and hands it down to `kids_runFacts`,
  `kids_outsCheck`, `kids_maskedN`, `kids_designCheck` — cannot be applied
  to it (`docs/parallel/A-cache-coherence-7.md` §3).

The run command checks the statements (no `HarnessStill` / `EntryStill` /
`CoreVia` / `MachineClosesAt` premise; the reflections present) and the file
prints binder lists and axioms. -/
namespace Tests.Compiler.MixDeepOutermostTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingChildInv (RefLaws InvV bodyRel harnessRel_of translateRel)
open Tools.ShippingCacheCoherentCert (EntryOk EntryStill HarnessStill entryOk_leaf
  entryOk_machine machine_closes_of_entryOk)
open Tools.ShippingCacheCoherentRun (Prov)
open Tools.ShippingHarnessStill (harnessStill_frag bool_pos_of_map bits_pos_of_map)
open Tools.ShippingWalkStill (wfrag)
open Tests.Compiler.CacheChainClosedTest (cnt_entryStill rcH_entryStill midH_entryOk_closed)

/-! ## `cnt` -/

/-- `EntryOk` of the leaf `cnt`, for any key set, from its reflection. -/
theorem cnt_entryOk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) (K : Lean.Name → Prop)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) : EntryOk L ``cnt K :=
  entryOk_leaf L (cnt_entryStill L hRc) fun y hy =>
    let h := Tools.ShippingSeqChildIface.seqChild_of_real cnt.machineData cnt.machine_ok
      cnt.machine_body rfl (by decide) hRc (fun mc cc => cnt.machine_closes mc _ cc _) hy
    ⟨h.name, h.design⟩

/-! ## `mid2` -/

theorem mid2_wf :
    (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).packed.WF
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).kb
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).kv
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).vw := by
  first | decide | decide +kernel

theorem mid2_frag :
    wfrag (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).packed = true := by
  first | decide | decide +kernel

theorem mid2_harnessStill {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref) :
    HarnessStill L ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.binders
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.body :=
  harnessStill_frag L mid2_wf mid2_frag
    (bool_pos_of_map (by first | decide | decide +kernel))
    (bits_pos_of_map (by first | decide | decide +kernel))
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_body

/-- Every call entry of `mid2` is of `midH`. -/
theorem mid2_callees :
    ∀ x ∈ (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.insts,
      x.1 = ``midH := by
  first | decide | decide +kernel

/-- **`EntryOk` of `mid2`, from three reflections only**: the keys its run
adds are `midH`'s and `rcH`'s. -/
theorem mid2_entryOk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref)
    (hR2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    EntryOk L ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (fun k => k = ``midH ∨ k = ``rcH) :=
  entryOk_machine L (fun L' => bodyRel L') (fun L' => harnessRel_of L' (translateRel L'))
    (Tests.Compiler.CacheChainMidHTest.mid2_coreVia L hR2 hRm hRr)
    (mid2_harnessStill L)
    (fun b => Tools.ShippingCacheCoherentData.hout_of_data
      Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData
      Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_ok
      Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_body (nDecl := 2)
      (by decide) (by decide) (by decide) b)
    (fun _ x hx => Or.inl (mid2_callees x hx))
    (fun x hx _ => by
      obtain ⟨i, hi, e⟩ := Tools.ShippingInstTagged.fst_mem_of_instTagged hx
      rw [← e]
      exact Or.inl (mid2_callees i hi))
    (fun c' hc' => by
      rcases hc' with hc' | hc'
      · subst hc'
        exact (midH_entryOk_closed L hRm hRr).mono (fun k hk => Or.inr hk)
      · subst hc'
        exact Tests.Compiler.CacheChainMidHTest.rcH_entryOk L _ hRr (rcH_entryStill L hRr))
    (by
      show ¬ (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 = ``midH ∨
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 = ``rcH)
      decide)

/-! ## `mixDeep` -/

theorem mixDeep_wf :
    (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).packed.WF
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).kb
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).kv
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).vw := by
  first | decide | decide +kernel

theorem mixDeep_frag :
    wfrag (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).packed = true := by
  first | decide | decide +kernel

theorem mixDeep_harnessStill {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref) :
    HarnessStill L ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.binders
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.body :=
  harnessStill_frag L mixDeep_wf mixDeep_frag
    (bool_pos_of_map (by first | decide | decide +kernel))
    (bits_pos_of_map (by first | decide | decide +kernel))
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body

/-- Every call entry of `mixDeep` is of `mid2`, `midH` or `cnt`. -/
theorem mixDeep_callees :
    ∀ x ∈ (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts,
      x.1 = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 ∨ x.1 = ``midH ∨
        x.1 = ``cnt := by
  first | decide | decide +kernel

/-- `mixDeep` is closed by the general closing. -/
theorem mixDeep_general :
    ¬ ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.instFields.isEmpty
      = true) := by
  first | decide | decide +kernel

/-- The descendants of `mixDeep`. -/
def KD (k : Lean.Name) : Prop :=
  k = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 ∨ k = ``midH ∨ k = ``rcH ∨ k = ``cnt

/-- **The machine synthesis of `mixDeep` does not fall back from a `Prov`
world** (an invariant world of positive depth whose cache satisfies `Prov`),
from the four reflections of its descendants. -/
theorem mixDeep_closes_prov {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref)
    (hR2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (b : Bool) (w9 : Void IO.RealWorld) (r : Option Tools.ShippingChildInv.Res)
    (w10 : Void IO.RealWorld) (hw9 : InvV L w9) (hd9 : L.dval w9 ≠ 0) (hp9 : Prov (L.val w9))
    (hrun : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeMachineCertified
      (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named)
      (Tools.ShippingChildInv.profLogIO b)
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
      mctx mref cctx cref w9 r w10) : r ≠ none := by
  have hS : Tools.ShippingCallsKidsS.MachineClosesAtS mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape
      ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts.map
        (·.1)) := by
    apply Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.closes_shared <;> assumption
  have hR : ∀ c, KD c → EntryOk L c KD := by
    intro c hc
    rcases hc with hc | hc | hc | hc
    · subst hc
      exact (mid2_entryOk L hR2 hRm hRr).mono
        (fun k hk => hk.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))
    · subst hc
      exact (midH_entryOk_closed L hRm hRr).mono (fun k hk => Or.inr (Or.inr (Or.inl hk)))
    · subst hc
      exact Tests.Compiler.CacheChainMidHTest.rcH_entryOk L _ hRr (rcH_entryStill L hRr)
    · subst hc
      exact cnt_entryOk L _ hRc
  exact machine_closes_of_entryOk _ hS L (fun L' => bodyRel L')
    (fun L' => harnessRel_of L' (translateRel L')) (K := KD)
    (mixDeep_harnessStill L)
    (Tools.ShippingCacheCoherentData.hout_of_data
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body (nDecl := 1)
      (by decide) (by decide) (by decide) b)
    (fun h => absurd h mixDeep_general)
    (fun x hx _ => by
      obtain ⟨i, hi, e⟩ := Tools.ShippingInstTagged.fst_mem_of_instTagged hx
      rw [← e]
      exact (mixDeep_callees i hi).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inr h)))))
    hR hw9 hd9 hp9 hrun

/-- **`mixDeep`, OUTERMOST STARTS ONLY**: a core run of `mixDeep` from a
world where the synthesis ref is set, the diagnostics are quiet and the
synthesis depth reads 0 IS a machine synthesis of its reflected shape that
returns the run's result — the closing succeeds. Premises: the five
reflections and the start condition (the depth-0 half of `ChildBnd`, for the
witness `L`). NOT `MachineClosesAt mixDeep`; no endpoint consumes it. -/
theorem mixDeep_closes_outermost {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref)
    (hRg : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hR2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hs : L.sval w = some Sparkle.Compiler.Elab.synthesizeChild) (hq : L.quiet w)
    (hd0 : L.dval w = 0)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep [] false)
      mctx mref cctx cref w (M, D) w') :
    ∃ (tenv : Lean.Environment) (b : Bool) (w9 w10 : Void IO.RealWorld),
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeMachineCertified
        (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named)
        (Tools.ShippingChildInv.profLogIO b)
        ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
        (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
        mctx mref cctx cref w9 (some (M, D)) w10 ∧
      InvV L w9 ∧ L.dval w9 ≠ 0 ∧ Prov (L.val w9) :=
  Tools.ShippingCacheCoherentOuter.coreVia0_of L (fun L' => bodyRel L')
    (fun L' => harnessRel_of L' (translateRel L')) hRg
    (fun b w9 r w10 hw9 hd9 hp9 hrun =>
      mixDeep_closes_prov L hR2 hRm hRr hRc b w9 r w10 hw9 hd9 hp9 hrun)
    hs hq hd0 hr

#check @cnt_entryOk
#check @mid2_entryOk
#check @mixDeep_closes_outermost
#print axioms cnt_entryOk
#print axioms mid2_entryOk
#print axioms mixDeep_closes_prov
#print axioms mixDeep_closes_outermost

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  IO.eprintln "MIXDEEPOUT START: checking the statements"
  (← IO.getStderr).flush
  let bad := [``Tools.ShippingCacheCoherentCert.HarnessStill,
    ``Tools.ShippingCacheCoherentCert.EntryStill, ``Tools.ShippingCacheCoherentCert.CoreVia,
    ``Tools.ShippingChildInv.MachineClosesAt]
  for n in [``Tests.Compiler.MixDeepOutermostTest.cnt_entryOk,
      ``Tests.Compiler.MixDeepOutermostTest.mid2_entryOk,
      ``Tests.Compiler.MixDeepOutermostTest.mixDeep_closes_outermost] do
    let some info := (← Lean.getEnv).find? n | throwError "{n}: missing"
    for c in bad do
      if (info.type.find? (·.isConstOf c)).isSome then
        throwError "{n}: its statement has the premise {c}"
    unless (info.type.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineDefines)).isSome do
      throwError "{n}: its statement does not mention MachineDefines"
  -- the existing endpoint is untouched: no closed form was created
  let closed := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep ++
    `machine_design_noPortsNR2_closed
  if (← Lean.getEnv).contains closed then throwError "{closed}: exists — not made here"
  Lean.logInfo m!"MIXDEEPOUT: cnt_entryOk, mid2_entryOk, mixDeep_closes_outermost (OUTERMOST starts only: L.dval w = 0) — premises: reflections and the depth-0 start condition; no endpoint touched"

end Tests.Compiler.MixDeepOutermostTest
