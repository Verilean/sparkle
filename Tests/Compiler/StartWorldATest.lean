import Tests.Compiler.LeafDesignClosedATest
import Tools.ShippingStartWorldA
-- UNBUILT (unit ST, par/u-st): see REPORT-ST.md.

/-! Unit ST: `dead7.machine_design_closedA` with `hA` discharged for the command's Meta context
and `hw` split into `quiet` + the ref contents. Premises left: run, `MachineDefines`,
`O : RefLawsAOps`, `O.quiet w`, `StartContents w` (R13/R14, OPEN). -/

namespace Sparkle.Tests.Compiler.StartWorldATest
open Tools.ShippingStartWorldA Tools.ShippingChildInvA Tools.ShippingChildVCA
open Sparkle.Tests.Compiler.LeafDeadInitTest


/-- `dead7.machine_design_closedA` at the command's Meta context (`Command.mkMetaContext`):
`hA` is PROVED (`admCtx_command`), and `hw` is replaced by `O.quiet w` and the two ref contents
`StartContents w` (R13/R14, OPEN). Conclusion: that of `machine_design_closedA`, verbatim. -/
def dead7.machine_design_closedCmd
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational `Sparkle.Tests.Compiler.LeafDeadInitTest.dead7)
      Lean.Elab.Command.mkMetaContext mref cctx cref w (b, design) w')
    (entry : Tools.ShippingMachineEntry.MachineDefines Lean.Elab.Command.mkMetaContext mref cctx cref
      `Sparkle.Tests.Compiler.LeafDeadInitTest.dead7 dead7.machineData.shape)
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (hq : O.quiet w) (hc : StartContents w) :=
  dead7.machine_design_closedA hr entry O (admCtx_command O.quiet cctx) (jq_zero_of O.quiet hq hc)

#print axioms dead7.machine_design_closedCmd
end Sparkle.Tests.Compiler.StartWorldATest
