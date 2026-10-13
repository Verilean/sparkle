import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingCacheCoherentVia
import Tools.ShippingChildHarness
import Tools.ShippingChildLegacy
import Tools.ShippingChildBody

/-! # `CoreVia` of a built machine-route declaration: `midH`

WRITTEN, NOT BUILT (par/a-35). Target-only; not in `Tests.AllTests`.

`midH` (`Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH`): a machine
with a register and one one-output call of the gate child `rcH` — the
smallest built machine-route declaration WITH a call, and a callee of
`mid2` and of `mixDeep`.

`midH_coreVia`: `Tools.ShippingCacheCoherentCert.CoreVia L midH shape` — a
returning core run of `midH` from an invariant world of positive depth is
the machine synthesis of its reflected shape, returning the run's result,
with the run's start and end cache. Premises: the two reflections that
every endpoint about `midH` carries (`MachineDefines midH`, `EntryDefines
rcH`, as in `Tests.Compiler.NoPortsGrandHTest.midH_kid`); the closing is the
BUILT `midH.closes_deep`. `bodyRel`, `harnessRel_of`, `translateRel` are the
built relative theorems.

The run command asserts that the theorem exists and prints its axioms. -/
namespace Tests.Compiler.CoreViaMidHTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest

theorem midH_coreVia {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Tools.ShippingChildInv.RefLaws mref cref)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    Tools.ShippingCacheCoherentCert.CoreVia L ``midH midH.machineData.shape :=
  Tools.ShippingCacheCoherentVia.coreVia_of L
    (fun L' => Tools.ShippingChildInv.bodyRel L')
    (fun L' => Tools.ShippingChildInv.harnessRel_of L' (Tools.ShippingChildInv.translateRel L'))
    (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm)
    (fun _ _ => midH.closes_deep (Tools.ShippingReflectCtx.EntryDefines.ctx hRr))

#print axioms midH_coreVia

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  IO.eprintln "COREVIA START midH: checking the theorem's statement"
  (← IO.getStderr).flush
  let n := ``Tests.Compiler.CoreViaMidHTest.midH_coreVia
  let some info := (← Lean.getEnv).find? n | throwError "{n}: missing"
  unless (info.type.find? (·.isConstOf ``Tools.ShippingCacheCoherentCert.CoreVia)).isSome do
    throwError "{n}: its statement does not mention CoreVia"
  Lean.logInfo m!"COREVIA midH: {n} : CoreVia L midH midH.machineData.shape, from MachineDefines midH and EntryDefines rcH"

end Tests.Compiler.CoreViaMidHTest
