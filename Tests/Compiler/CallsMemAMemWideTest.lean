import Tests.Compiler.NoPortsMemOnlyClosedMemWideTest
import Tools.ShippingCallsMemA
-- UNBUILT (unit CM): run names/exits are recorded in REPORT-CM.md.

/-! # `MachineClosesAtA memWide` on the new boundary (unit CM)

`memWide`: a memory-only parent (one combinational-read memory, aw 6, dw 16). The old boundary has
`memWide_closes : MachineClosesAt …` (`NoPortsMemOnlyClosedMemWideTest`, from `machineClosesAt_of_memOnlyData`).
Here the same decided data (`memWide_data`, `memWide_closeData`) give `MachineClosesAtA` via
`machineClosesAtA_of_memOnlyData_names`. Premises: `O`, `hA`, `T` (a SEPARATE assumption family,
`RefLawsATele`), and the reader data. NO distinct-callee restriction (a memory-only parent has no ord
entry). `ChildrenRealA` is a history; not a runtime-fit proof. -/

namespace Tests.Compiler.CallsMemAMemWideTest
open Tools.ShippingChildFresh Tools.ShippingChildInvA Tools.ShippingChildRunAKids

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem memWide_closesA (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape :=
  Tools.ShippingCallsMemA.machineClosesAtA_of_memOnlyData_names O T hA
    Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_data
    Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_closeData

end Tests.Compiler.CallsMemAMemWideTest

#print axioms Tests.Compiler.CallsMemAMemWideTest.memWide_closesA
