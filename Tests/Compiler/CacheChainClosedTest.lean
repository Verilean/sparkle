import Tests.Compiler.CacheChainMidHTest
import Tests.Compiler.WalkStillFragTest
import Tools.ShippingHarnessStill
import Tools.ShippingGateChild

/-! # `HarnessStill` / `EntryStill` for concrete declarations, and `midH`'s `EntryOk` with no underived hypothesis

WRITTEN, NOT BUILT (par/a-37). Target-only; not in `Tests.AllTests`. No
endpoint is connected or narrowed. Nothing here evaluates reflected data in
compiled code: every data condition is a kernel `decide`.

* `midH_harnessStill`, `cnt_harnessStill`: `HarnessStill` of the two machine
  transitions (`Tools.ShippingHarnessStill.harnessStill_frag`; the packed
  terms are in the fragment — `midH_frag`, `cnt_frag`, BUILT);
* `cnt_entryStill`: `EntryStill L cnt` (a machine without calls), from the
  reflection `MachineDefines cnt` and the BUILT `cnt.machine_closes`;
* `rcH_entryStill`: `EntryStill L rcH` (a gate child on the mixed route),
  from the reflection `EntryDefines rcH` and the BUILT `rcH.gate_old` /
  `gate_peel` / `gate_wf`; `rcH.gateTerm` is in the fragment as it stands
  (`rcH_frag`: `mux` at bits, `compare`, `bitsLit`, `binary`, a bits input —
  no constructor had to be added);
* **`midH_entryOk_closed`**: `EntryOk L midH (· = rcH)` from the TWO
  REFLECTIONS ONLY (`MachineDefines midH`, `EntryDefines rcH`).

The run command checks that the statement of `midH_entryOk_closed` mentions
neither `HarnessStill` nor `EntryStill`, and the file prints its binder list
(`#check`) and the axioms of the five theorems. -/
namespace Tests.Compiler.CacheChainClosedTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingChildInv (RefLaws bodyRel harnessRel_of translateRel)
open Tools.ShippingCacheCoherentCert (EntryOk EntryStill HarnessStill)
open Tools.ShippingHarnessStill (harnessStill_frag entryStill_leaf entryStill_gate
  bool_pos_of_map bits_pos_of_map)
open Tools.ShippingWalkStill (wfrag)

/-- The harness on `midH`'s transition leaves the child cache. -/
theorem midH_harnessStill {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref) :
    HarnessStill L ``midH midH.machineData.shape.binders midH.machineData.shape.body :=
  harnessStill_frag L Tests.Compiler.WalkStillFragTest.midH_wf
    Tests.Compiler.WalkStillFragTest.midH_frag
    (bool_pos_of_map (by first | decide | decide +kernel))
    (bits_pos_of_map (by first | decide | decide +kernel))
    midH.machine_body

/-- The harness on `cnt`'s transition leaves the child cache. -/
theorem cnt_harnessStill {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref) :
    HarnessStill L ``cnt cnt.machineData.shape.binders cnt.machineData.shape.body :=
  harnessStill_frag L Tests.Compiler.WalkStillFragTest.cnt_wf
    Tests.Compiler.WalkStillFragTest.cnt_frag
    (bool_pos_of_map (by first | decide | decide +kernel))
    (bits_pos_of_map (by first | decide | decide +kernel))
    cnt.machine_body

/-- `cnt` has no call. -/
theorem cnt_noInsts : cnt.machineData.shape.insts = [] := by
  first | decide | decide +kernel

/-- A run of `cnt`'s entry leaves the child cache. -/
theorem cnt_entryStill {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) : EntryStill L ``cnt :=
  entryStill_leaf L (fun L' => bodyRel L') (fun L' => harnessRel_of L' (translateRel L'))
    (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRc)
    (fun mc cc => Tools.ShippingChildInv.machineClosesAt_of_closes (cnt.machine_closes mc _ cc _))
    cnt_noInsts (cnt_harnessStill L)

/-- `rcH`'s gate term is in the fragment. -/
theorem rcH_frag : wfrag rcH.gateTerm = true := by
  first | decide | decide +kernel

/-- A run of `rcH`'s entry leaves the child cache. -/
theorem rcH_entryStill {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    EntryStill L ``rcH :=
  entryStill_gate L (fun L' => bodyRel L')
    (fun _ _ => Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
    rcH.gate_old rcH.gate_peel rcH.gate_wf rcH_frag
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide))

/-- **`EntryOk` of `midH`, from the two reflections only.** -/
theorem midH_entryOk_closed {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : RefLaws mref cref)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    EntryOk L ``midH (fun k => k = ``rcH) :=
  Tests.Compiler.CacheChainMidHTest.midH_entryOk L hRm hRr (midH_harnessStill L)
    (rcH_entryStill L hRr)

#check @midH_entryOk_closed
#print axioms midH_harnessStill
#print axioms cnt_entryStill
#print axioms rcH_entryStill
#print axioms midH_entryOk_closed

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  IO.eprintln "CACHECLOSED START: checking the statement of midH_entryOk_closed"
  (← IO.getStderr).flush
  let n := ``Tests.Compiler.CacheChainClosedTest.midH_entryOk_closed
  let some info := (← Lean.getEnv).find? n | throwError "{n}: missing"
  for c in [``Tools.ShippingCacheCoherentCert.HarnessStill,
      ``Tools.ShippingCacheCoherentCert.EntryStill,
      ``Tools.ShippingCacheCoherentCert.CoreVia] do
    if (info.type.find? (·.isConstOf c)).isSome then
      throwError "{n}: its statement still has the premise {c}"
  for c in [``Tools.ShippingMachineEntry.MachineDefines,
      ``Tools.ShippingInlineSoundness.EntryDefines,
      ``Tools.ShippingCacheCoherentCert.EntryOk] do
    unless (info.type.find? (·.isConstOf c)).isSome do
      throwError "{n}: its statement does not mention {c}"
  Lean.logInfo m!"CACHECLOSED: {n} : EntryOk L midH (· = rcH), premises: MachineDefines midH, EntryDefines rcH — no HarnessStill, no EntryStill, no CoreVia"

end Tests.Compiler.CacheChainClosedTest
