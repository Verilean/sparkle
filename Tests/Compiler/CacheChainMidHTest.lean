import Tests.Compiler.CoreViaMidHTest
import Tests.Compiler.NoPortsTopD2Test
import Tools.ShippingCacheCoherentData

/-! # The provenance chain of the `mixDeep` family, as far as it goes: `rcH → midH` (and `mid2`'s `CoreVia`)

WRITTEN, NOT BUILT (par/a-36). Target-only; not in `Tests.AllTests`. No
endpoint is connected or narrowed.

`mixDeep → {mid2 → midH → rcH, midH → rcH, cnt}`. This file writes the chain
`entryOk_leaf` (for `rcH`) → `entryOk_machine` (for `midH`) as ACTUAL TERMS:
every ingredient is a theorem (built, or of this branch's base), EXCEPT the
hypotheses listed at `midH_entryOk` below. It also instantiates `CoreVia`
for `mid2`.

* `mid2_coreVia`: `CoreVia L mid2 shape`, from the three reflections
  `mid2_kid` carries; the closing is the BUILT `mid2.closes_deep`, whose two
  arguments are tried in both orders (`first`), exactly as
  `Tests.Compiler.NoPortsTopD2Test.mid2_kid` does — the order cannot be read
  off the source (the theorem is generated).
* `rcH_entryOk`: `EntryOk L rcH K` for ANY `K`, from `EntryStill L rcH`
  (NOT a theorem) and the built gate facts (`rcH.gate_full`).
* `midH_entryOk`: `EntryOk L midH (· = rcH)`.

## The hypotheses of `midH_entryOk` that are NOT theorems

| hypothesis | what it is | state |
|---|---|---|
| `hRm`, `hRr` | the reflections `MachineDefines midH`, `EntryDefines rcH` | premises of every endpoint about `midH` (ALLOWED; unchanged) |
| `hstillH : HarnessStill L midH shape.binders shape.body` | the harness on `midH`'s transition leaves the cache | **NOT a theorem.** Its core — the translator on the quoted body — is `Tools.ShippingWalkStill.walk_still` (this branch) IF `midH`'s packed term is in the fragment; the harness shell around it is not written |
| `hstillR : EntryStill L rcH` | a run of `rcH`'s entry leaves the cache | **NOT a theorem.** `rcH` is on the GATE route: the same shell, plus the gate arm of the entry |

Everything else is discharged here: `CoreVia midH` (`midH_coreVia`, BUILT),
the harness's result facts (`hout_of_data` over `midH.machine_ok` /
`machine_body` / `oneout_callsOk` / `oneout_slotLen` / `oneout_domB`), the
callees (`decide` on the reflected call entries), the name condition
(`midH ≠ rcH`, `decide`), the leaf's name and design
(`ChildFull.iface (rcH.gate_full …)`).

The run command prints the axioms of the three theorems. -/
namespace Tests.Compiler.CacheChainMidHTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingChildInv (RefLaws RealChild bodyRel harnessRel_of translateRel)
open Tools.ShippingCacheCoherentCert (CoreVia EntryOk EntryStill HarnessStill entryOk_leaf
  entryOk_machine)

/-- `CoreVia` of `mid2` (callee `midH`, the general closing). -/
theorem mid2_coreVia {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    CoreVia L ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape :=
  Tools.ShippingCacheCoherentVia.coreVia_of L
    (fun L' => bodyRel L')
    (fun L' => harnessRel_of L' (translateRel L'))
    (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm2)
    (fun _ _ => by
      first
        | exact Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.closes_deep
            (Tools.ShippingReflectCtx.MachineDefines.ctx hRm)
            (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
        | exact Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.closes_deep
            (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
            (Tools.ShippingReflectCtx.MachineDefines.ctx hRm))

/-- The leaf `rcH` (a gate child): `EntryOk` for any key set, from
`EntryStill` (NOT a theorem) and the built gate facts. -/
theorem rcH_entryOk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) (K : Lean.Name → Prop)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hstillR : EntryStill L ``rcH) : EntryOk L ``rcH K :=
  entryOk_leaf L hstillR fun y hy =>
    let h := Tools.ShippingCallsGate.ChildFull.iface (rcH.gate_full hRr hy)
    ⟨h.2.2.1, h.2.2.2⟩

/-- Every call entry of `midH` is of `rcH` (membership form of
`Tests.Compiler.NoPortsGrandHTest.midH_entry`). -/
theorem midH_callees : ∀ x ∈ midH.machineData.shape.insts, x.1 = ``rcH := by
  first | decide | decide +kernel

/-- **`EntryOk` of `midH`**: the keys its run adds are `rcH`'s only. -/
theorem midH_entryOk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hstillH : HarnessStill L ``midH midH.machineData.shape.binders midH.machineData.shape.body)
    (hstillR : EntryStill L ``rcH) :
    EntryOk L ``midH (fun k => k = ``rcH) :=
  entryOk_machine L (fun L' => bodyRel L') (fun L' => harnessRel_of L' (translateRel L'))
    (Tests.Compiler.CoreViaMidHTest.midH_coreVia L hRm hRr)
    hstillH
    (fun b => Tools.ShippingCacheCoherentData.hout_of_data midH.machineData midH.machine_ok
      midH.machine_body midH.oneout_callsOk midH.oneout_slotLen midH.oneout_domB b)
    (fun _ => midH_callees)
    (fun x hx _ => midH_callees x hx)
    (fun c' hc' => by
      subst hc'
      exact rcH_entryOk L _ hRr hstillR)
    (by
      show ¬ (``midH = ``rcH)
      decide)

#print axioms mid2_coreVia
#print axioms rcH_entryOk
#print axioms midH_entryOk

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  IO.eprintln "CACHECHAIN START: checking the three statements"
  (← IO.getStderr).flush
  for n in [``mid2_coreVia, ``rcH_entryOk, ``midH_entryOk] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
  -- the chain's end must still carry the two statements that are not theorems
  let some info := (← Lean.getEnv).find? ``midH_entryOk | throwError "midH_entryOk"
  for c in [``Tools.ShippingCacheCoherentCert.HarnessStill,
      ``Tools.ShippingCacheCoherentCert.EntryStill] do
    unless (info.type.find? (·.isConstOf c)).isSome do
      throwError "midH_entryOk no longer has the premise {c}: update the record"
  Lean.logInfo m!"CACHECHAIN: rcH_entryOk, midH_entryOk (premises: the two reflections, HarnessStill midH, EntryStill rcH), mid2_coreVia"

end Tests.Compiler.CacheChainMidHTest
