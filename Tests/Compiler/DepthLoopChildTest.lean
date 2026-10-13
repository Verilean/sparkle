import Lean.Elab.Command
import Tools.ShippingMachineDepthCommandR
import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.ShippingCallsCloseDeepTest
import Tests.Compiler.ShippingMachineDepthTest
import Tests.Compiler.ShippingMachineSeqLoopTest

/-! # A `Signal.loop` child at depth, by the generator alone (round par/b-23)

WRITTEN, NOT BUILT. TARGET-ONLY (not in `Tests/AllTests.lean`: NAME CLASH
below).

`generateSeqChildN` (`Tools/ShippingMachineDepthCommand.lean`) accepted only
a child whose `machine_sound` is built from `machine_trace_of_data`; the
built `Tests/Compiler/NoPortsLoopParentTest.lean` therefore supplies
`toggleL.seq_child_runN` by hand (`seqChildRunNOfLoop`) before it runs
`#machine_design_svNR loopParent 1`. Round par/b-23 adds the two branches
(`machine_trace_of_loop`, `machine_trace_of_regs` → their wired twins, the
head table of the depth-0 `generateSeqChild`).

This file has the imports of `NoPortsLoopParentTest` WITHOUT that file, so
nothing supplies the child's theorem, and runs the command:

    #machine_design_svNR loopParent 1

EXPECTED (each step THROWS otherwise): before the command
`toggleL.seq_child_runN` is absent and `toggleL.machine_sound` has the head
`machine_trace_of_loop`; after it `toggleL.seq_child_runN` is a theorem
whose proof's head is `Tools.ShippingMachineDepthRun.seqChildRunN_full`,
whose statement mentions `SeqChildRunN`, on standard axioms; and
`loopParent.machine_design_svNR1` exists.

LOGGED: the fingerprint (`Expr.hash` of the type, number of leading binders)
of `toggleL.seq_child_runN` and of the three `loopParent.machine_*NR1`
statements. `Tests/Compiler/DepthLoopChildCompareTest.lean` logs the
fingerprint of the HAND-written `toggleL.seq_child_runN` and decides
`isDefEq` there; equal fingerprints in the two logs additionally say the two
are the same term. `Tests/Compiler/DepthSwitchPinTest.lean` pins
`loopParent`'s three statements as built with the hand-written child
theorem.

NAME CLASH: this file generates `toggleL.seq_child_runN` and
`loopParent.machine_composedNR1` / `machine_ships_hierNR1` /
`machine_design_svNR1`, as `NoPortsLoopParentTest` (in `AllTests`) and
`RemainingProbeTest` do. It must not be imported together with either, and
so it cannot be in `AllTests`.

SCOPE: one child (`toggleL`, a 1-bit `Signal.loop` register) under one
parent, depth 1. The `machine_trace_of_regs` branch is WRITTEN and NOT
exercised by any test of this round (no built parent calls a register
product child at depth).
-/

namespace Tests.Compiler.DepthLoopChildTest

/-- The number of leading binders of a statement. -/
partial def binderCount : Lean.Expr → Nat
  | Lean.Expr.forallE _ _ b _ => binderCount b + 1
  | Lean.Expr.mdata _ e => binderCount e
  | _ => 0

end Tests.Compiler.DepthLoopChildTest

run_cmd Lean.Elab.Command.liftCoreM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL
  let env ← Lean.getEnv
  for n in [c ++ `seq_child_runN, f ++ `machine_composedNR1, f ++ `machine_ships_hierNR1,
      f ++ `machine_design_svNR1] do
    if env.contains n then
      throwError "{n}: exists already — is NoPortsLoopParentTest or RemainingProbeTest imported? (NAME CLASH, see the header)"
  match env.find? (c ++ `machine_sound) with
  | some (Lean.ConstantInfo.thmInfo ti) =>
    unless ti.value.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_loop do
      throwError "{c}.machine_sound is not built from machine_trace_of_loop: this file would not test the new branch"
  | _ => throwError "{c}.machine_sound: not a theorem of the imports"
  Lean.logInfo m!"DEPTH LOOP CHILD: before the command — {c}.seq_child_runN absent, {c}.machine_sound built from machine_trace_of_loop"

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent 1

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftCoreM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL
  let env ← Lean.getEnv
  let name := c ++ `seq_child_runN
  let mut lines : List String := []
  match env.find? name with
  | some (Lean.ConstantInfo.thmInfo ti) =>
    unless ti.value.getAppFn.isConstOf ``Tools.ShippingMachineDepthRun.seqChildRunN_full do
      throwError "{name}: its proof is not an application of seqChildRunN_full"
    unless (ti.type.find? (fun e => e.isConstOf ``Tools.ShippingMachineDepth.SeqChildRunN)).isSome do
      throwError "{name}: its statement does not mention SeqChildRunN"
    lines := lines ++ [s!"{name}: hash {ti.type.hash.toNat}, {Tests.Compiler.DepthLoopChildTest.binderCount ti.type} binders"]
  | _ => throwError "{name}: not generated as a theorem by #machine_design_svNR"
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  for n in [f ++ `machine_composedNR1, f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1] do
    match env.find? n with
    | some (Lean.ConstantInfo.thmInfo ti) =>
      lines := lines ++ [s!"{n}: hash {ti.type.hash.toNat}, {Tests.Compiler.DepthLoopChildTest.binderCount ti.type} binders"]
    | _ => throwError "{n}: not generated as a theorem"
  Lean.logInfo m!"DEPTH LOOP CHILD: {name} GENERATED by generateSeqChildN inside #machine_design_svNR {f} 1 (no hand-written theorem in this closure): seqChildRunN_full at the wired twin of a machine_trace_of_loop endpoint, standard axioms. Fingerprints: {lines}. SCOPE: one Signal.loop child, depth 1; the machine_trace_of_regs branch is not exercised"
