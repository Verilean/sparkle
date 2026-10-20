import Tests.Compiler.LeafEntryFamilyTest
import Tests.Compiler.LeafDesignClosedTest

/-! # `#machine_leaf_design_closed` on more leaves (round par/audit2)

BUILT by the integrator: lf1 exit 0 (713 jobs; with ChildVertAuditTest). All six rows GENERATED and audited (8 antecedents walked each, 1 DesignSV run). Integrator-written.

`Tests/Compiler/LeafDesignClosedTest.lean` closed `dead7` (whose optimizer REMOVES a register).
Here the same generator (`Tools.ShippingLeafDesignClosedCommand.generate`) is applied to the
leaf register machines whose `f.machine_leafKid` / `f.machine_closes` are built by
`Tests/Compiler/LeafEntryFamilyTest.lean`:

| declaration | shape (from LeafEntryFamilyTest) |
|---|---|
| `acc` | one 8-bit register, structure result (`BitVec 8` and `Bool`) |
| `pe` | two 32-bit registers, three 32-bit inputs, structure result |
| `twoHW` | an 8-bit and a `Bool` register, structure result |
| `toggle` | a `Bool` register, a `Bool` output |
| `loopPair` | `Signal.loop` over a pair of 32-bit registers (one packed 64-bit port) |
| `toggleL` | `Signal.loop`, one `Bool` register |

For each: (1) EVALUATED on the real compile (`synthesizeCombinational f`): registers of `b`,
registers kept by `checkedOptimize b`, their widths, the output ports — logged as
`LEAFFAMILY DATA` (kept registers / Bool / several outputs / different widths are read off
this line, not assumed); (2) the generator, inside `try`: outcome `GENERATED` or the refusal
message; (3) for `GENERATED`, the audit of `LeafDesignClosedTest` (`auditDesignClosed`:
standard axioms, outer premises exactly the run / `MachineDefines` / `ChildBnd`, no nested
antecedent other than the `DesignSV` run mentions a checker / seeding / width constant).
The file THROWS at the end unless every row is `GENERATED` and audited.

Not shown: the printed SV string, the runtime fit of `ChildBnd`, coverage beyond these rows.
A merge-drop / optimizer-reject example (`tgtSt2`'s non-register clearing) stays NOT
REPRODUCED (Tests/Compiler/MergeDropProbe.lean). -/

namespace Sparkle.Tests.Compiler.LeafDesignClosedFamilyTest
open Lean Elab Command Meta Term

def rows : List Name :=
  [``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc,
   ``Sparkle.Tests.Compiler.MultiInstance.pe,
   ``Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW,
   ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle,
   ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair,
   ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL]

end Sparkle.Tests.Compiler.LeafDesignClosedFamilyTest

open Sparkle.Tests.Compiler.LeafDesignClosedFamilyTest

/-! ## (1) the compile's data, evaluated -/

open Lean Elab Command Meta Sparkle.Compiler.Elab in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  for f in rows do
    let _saved ← Meta.saveState
    try
      sparkleSynthDepth.set 0
      sparkleChildCache.set {}
      let (b, _) ← synthesizeCombinational f
      let opt := Sparkle.IR.OptCheck.checkedOptimize b
      let regsB := (Sparkle.IR.OptCheck.seqRegs b).map (·.1)
      let regsO := (Sparkle.IR.OptCheck.seqRegs opt).map (·.1)
      let widths := regsO.map fun r => (r, Tools.ShippingDesignSV.weS opt r)
      let outs := b.outputs.map fun p => (p.name, reprStr p.ty)
      logInfo m!"LEAFFAMILY DATA {f}: regs of b {regsB}; kept by checkedOptimize {regsO} (all kept: {regsB.all regsO.contains}); widths {widths}; outputs {outs}; opt = b: {opt == b}"
    finally
      sparkleSynthDepth.set 0
      sparkleChildCache.set {}

/-! ## (2)+(3) generate and audit every row -/

open Lean Elab Command Meta Term in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let mut failed : List (Name × String) := []
  for f in rows do
    try
      let n ← Tools.ShippingLeafDesignClosedCommand.generate f
      let (a, r) ← Sparkle.Tests.Compiler.LeafDesignClosedTest.auditDesignClosed n
      logInfo m!"LEAFFAMILY GENERATED {n}: audited ({a} antecedents, {r} DesignSV runs)"
    catch e =>
      let msg ← e.toMessageData.toString
      logInfo m!"LEAFFAMILY REFUSED {f}: {msg}"
      failed := (f, msg) :: failed
  unless failed.isEmpty do
    throwError "LEAFFAMILY: not generated/audited: {failed.map (·.1)}"
