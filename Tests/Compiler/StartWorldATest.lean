import Tests.Compiler.LeafDesignClosedATest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingStartWorldA
import Tools.ShippingStartWorldA2
-- BUILT (unit ST, par/u-st): st4 exit 0 (WIP state); closure audit below added at integration (par/int-r15),
-- re-verified by the integration run. `machine_design_closedCmd` is a `def`, but being a `def` is no reason to
-- skip the audit: its closure is checked like the theorems'.

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

/-! Closure audit of `dead7.machine_design_closedCmd` (the vert audit's `depClosure`, theorem/opaque bodies read):
standard axioms, no old boundary (RefLaws/RefLawsCore/toAOps/toA) and no ChildBnd/StartV/RefLawsATele. THROWS. -/
open Lean Meta Elab in
run_meta do
  let n := ``Sparkle.Tests.Compiler.StartWorldATest.dead7.machine_design_closedCmd
  Tests.Compiler.ChildVertAuditTest.stdAxioms n
  let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
  let bad := Tests.Compiler.ChildVertAuditTest.hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
     `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{n}: old-boundary dependencies {bad}"
  logInfo m!"STARTWORLD-A AUDIT OK: {n}: standard axioms; closure {cl.size} constants, no RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV/RefLawsATele"

/-! Unit ST2: in-file closure audit of the entry-run preservation theorems (same cycle rule as above). -/
open Lean Meta Elab in
run_meta do
  for n in [``Tools.ShippingStartWorldA2.startContents_entry, ``Tools.ShippingStartWorldA2.startContents_of_runs,
      ``Tools.ShippingStartWorldA2.startContents_endW, ``Tools.ShippingStartWorldA2.startContents_session] do
    Tests.Compiler.ChildVertAuditTest.stdAxioms n
    let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
    let bad := Tests.Compiler.ChildVertAuditTest.hits cl ++ cl.toList.filter fun c =>
      [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
       `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "{n}: old-boundary dependencies {bad}"
    logInfo m!"STARTWORLD-A2 AUDIT OK: {n}: standard axioms; closure {cl.size} constants"
