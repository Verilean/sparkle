import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.OneOutFamilyTest
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tests.Compiler.ShippingCallsCloseDeepTest
import Tests.Compiler.ShippingMachineDepthTest

/-! # The remaining design-level endpoints: BUILT generators tried on the declarations nobody ran them on (G1, round par/a-12)

LOGS ONLY — nothing in this file is asserted and no step throws: a step
that fails is logged `REMAINING PROBE <tag>: FAILED — <the error>` and the
environment and the message log are put back to what they were before that
step. The census `docs/parallel/A-remaining.md` (§1) was made by READING;
this file turns its three "not read to the end" rows into measurements, and
records the refusal line of every other row.

## (A) Declarations whose SHAPE is in the scope of a BUILT check-free chain, but with a missing prerequisite

| declaration | shape (by reading) | steps tried | what is NOT known |
|---|---|---|---|
| `mid` (`ShippingMachineSeqTest`) | `@[hardware_module]`, domain-polymorphic, a register, one call of the leaf register machine `cnt`, structure result | `#machine_endpoint`, `#machine_design_svNR mid 1`, `#machine_closes_at`, `#machine_no_ports mid 1` | whether the depth generator accepts a domain-polymorphic ENTRY (`parent`, `chained`, `two` are over `defaultDomain`); whether `mid` has a machine endpoint of its own in the imports |
| `loopParent` (`ShippingMachineSeqLoopTest`) | a register, one call of `toggleL` (a `Signal.loop` register, `Bool` result) | `#machine_design_svNR loopParent 1`, `#machine_closes_at`, `#machine_no_ports loopParent 1` | whether a `Signal.loop` child's register is a `layout.slots` entry (`LeafKid.slots`, `scopeP`'s "it has no register"); its closing `toggleL.machine_closes`; the depth generator on a loop child |
| `callerInner` (`ShippingMachineInstTest`) | a register, two call entries of the gate child `pick`, one of them inside the flattened sub-machine `innerPick` | `#machine_design_svHR`, `#machine_closes_at`, `#machine_oneout` | everything after `#machine_endpoint`: no linked / composed theorem of it is in the tests |

NO prediction is made for (A): the three outcomes are not known. Where a
chain goes through, the audit of the corresponding test
(`NoPortsTwoTest.audit` / `OneOutFamilyTest.audit`) is run and ITS failure
is logged too (`REMAINING PROBE <f> audit: FAILED — …`), never thrown.

TARGET-BUILT ONLY — NOT for `Tests/AllTests.lean`. A step that succeeds
leaves constants under the declarations' usual names in THIS module
(`mid.machine_design_svNR1`, `toggleL.machine_closes`,
`callerInner.machine_design_svHR`, …). A module that does not import this
one and generates the same name (a later proper test; a generator that adds
a child's closing on demand) cannot be loaded together with it. The two
imports `ShippingCallsCloseDeepTest` (where `mid.machine_closes_at` is
generated for `grand`'s depth endpoint) and `ShippingMachineDepthTest` are
there for that reason only.

## (B) Declarations a check-free generator REFUSES by scope: the refusal line, measured

`#machine_no_ports_try f n` on the depth parents and the memory / slotless
parents: one `NOPORTS REFUSED f at depth n: <reason>` line each. Predicted
reasons (by reading `scopeP`, in its order):

| declaration | depth | predicted refusal |
|---|---|---|
| `grandH` | 1 | `the callee …midH is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)` |
| `mixD1` | 1 | the same, callee `midH` (the first callee read) |
| `topD2` | 2 | the same, callee `mid2` |
| `mixDeep` | 2 | the same, callee `mid2` |
| `grand` | 2 | the same, callee `mid` |
| `seqMem` | 1 | `the callee … is not a leaf register machine: it is a memory child …` or, if `cnt` is read first, no depth endpoint (`seqMem.machine_ships_hierNR1` is not there) |
| `memCounter` | 0 | `parent without a register …` if a `Signal.loop` register is not a slot, else the memory-child line |
| `engineOnce` | 1 | `parent without a register (core_portsMatch_raw_leaf asks d.shape.layout.slots ≠ [] …)` |

UNVERIFIED at the time of writing: this file was not built. -/

namespace Tests.Compiler.RemainingProbeTest
open Lean Meta Elab Command

/-- `#probe_log "tag" in cmd`: elaborate `cmd`; when it throws or logs an
error, put the environment and the message log back and LOG the failure. -/
elab "#probe_log " tag:str " in " c:command : command => do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let thrown ← try
      elabCommand c
      pure none
    catch ex => pure (some (← ex.toMessageData.toString))
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match thrown with
    | some msg => some msg
    | none => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  match failure with
  | some msg =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"REMAINING PROBE {tag.getString}: FAILED — {msg}"
  | none =>
    logInfo m!"REMAINING PROBE {tag.getString}: OK"

/-- After the steps of a depth-1 chain on `f`: where the closed check-free
endpoint exists, the audit of `NoPortsTwoTest` (its failure LOGGED). -/
def afterNoPorts (f : Name) (kids : List Name) : MetaM Unit := do
  let closed := f ++ `machine_design_noPortsNR1_closed
  let openN := f ++ `machine_design_noPortsNR1
  let old := f ++ `machine_design_svNR1
  let env ← getEnv
  let yn (n : Name) : String := if env.contains n then "yes" else "no"
  unless env.contains closed do
    logInfo m!"REMAINING PROBE {f}: no {closed} (the open form {openN} exists: {yn openN}; the depth endpoint {old} exists: {yn old}) — no premise counts as removed for {f}"
    return
  try
    let gapName := f ++ `machine_design_noPortsNR1_closed_gap
    unless (← getEnv).contains gapName do
      let report ← Tools.ShippingFinalGoalCommand.gapOf closed gapName
      logInfo m!"GOALGAP {gapName} from {closed}\n{String.intercalate "\n" report.toList}"
    Tests.Compiler.NoPortsTwoTest.audit f kids
    logInfo m!"REMAINING PROBE {f} audit: OK — {closed} passes the audit of NoPortsTwoTest (its NOPORTS TWO line above carries the scope)"
  catch ex =>
    logInfo m!"REMAINING PROBE {f} audit: FAILED — {ex.toMessageData}"

/-- After the one-output steps on `f`: where the endpoint exists, the audit
of `OneOutFamilyTest` (its failure LOGGED). -/
def afterOneOut (f : Name) (kids : List Name) : MetaM Unit := do
  let full := f ++ `machine_design_svH_full
  let old := f ++ `machine_design_svHR
  let env ← getEnv
  let yn (n : Name) : String := if env.contains n then "yes" else "no"
  unless env.contains full do
    logInfo m!"REMAINING PROBE {f}: no {full} (the endpoint {old} exists: {yn old}) — no premise counts as removed for {f}"
    return
  try
    Tests.Compiler.OneOutFamilyTest.audit f kids false
    logInfo m!"REMAINING PROBE {f} audit: OK — the audit of OneOutFamilyTest ran (its ONEOUT FAMILY line above carries the scope; a SKIPPED line there means no closed form)"
  catch ex =>
    logInfo m!"REMAINING PROBE {f} audit: FAILED — {ex.toMessageData}"

end Tests.Compiler.RemainingProbeTest

/-! ## (A1) `mid` -/

set_option maxHeartbeats 0 in
#probe_log "mid: #machine_endpoint (FAILED is expected when its endpoint already exists)" in
  #machine_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid

set_option maxHeartbeats 0 in
#probe_log "mid: #machine_design_svNR 1" in
  #machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid 1

set_option maxHeartbeats 0 in
#probe_log "mid: #machine_closes_at" in
  #machine_closes_at Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid

set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid 1

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.RemainingProbeTest.afterNoPorts ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
    [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt]

/-! ## (A2) `loopParent` -/

set_option maxHeartbeats 0 in
#probe_log "loopParent: #machine_design_svNR 1" in
  #machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent 1

set_option maxHeartbeats 0 in
#probe_log "loopParent: #machine_closes_at" in
  #machine_closes_at Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent

set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent 1

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.RemainingProbeTest.afterNoPorts
    ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
    [``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL]

/-! ## (A3) `callerInner` -/

set_option maxHeartbeats 0 in
#probe_log "callerInner: #machine_design_svHR" in
  #machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner

set_option maxHeartbeats 0 in
#probe_log "callerInner: #machine_closes_at" in
  #machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner

set_option maxHeartbeats 0 in
#probe_log "callerInner: #machine_oneout" in
  #machine_oneout Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.RemainingProbeTest.afterOneOut
    ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick]

/-! ## (B) The refusal lines of the declarations out of scope -/

set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH 1
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 1
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 2
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep 2
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 2
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem 1
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter 0
set_option maxHeartbeats 0 in
#machine_no_ports_try Sparkle.Tests.Compiler.MultiInstance.engineOnce 1
