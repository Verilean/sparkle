import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.ShippingCallsCloseDeepTest
import Tests.Compiler.ShippingMachineDepthTest
import Tests.Compiler.ShippingMachineSeqLoopTest

/-! # `#machine_no_ports` on `loopParent`: a register parent of a `Signal.loop` leaf child (G1, round par/a-22)

`loopParent` (`Tests/Compiler/ShippingMachineSeqLoopTest.lean` 21–32):

    @[hardware_module]
    def toggleL {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool :=
      Signal.loop fun (s : Signal dom Bool) =>
        Signal.register false (Signal.mux en (~~~s) s)

    def loopParent (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
      circuit do
        let r0 ← Signal.reg false
        let t := toggleL en
        r0 <~ t
        return (r0 : Signal defaultDomain Bool)

## What was MEASURED before this file (`docs/parallel/verification-a12.md` 72–75, the log-only probe)

    REMAINING PROBE loopParent: #machine_design_svNR 1: FAILED — seq child …toggleL: …toggleL.machine_sound is not built from Tools.ShippingMachineAuto.machine_trace_of_data
    REMAINING PROBE loopParent: #machine_closes_at: OK
    NOPORTS REFUSED …loopParent at depth 1: …: no depth endpoint at depth 1 (…machine_ships_hierNR1 is not there: run #machine_design_svNR … 1 first)

The refusal of `#machine_no_ports` is its SECOND test: `scopeP`
(`Tools/ShippingNoPortsCommand.lean` 79–100) ran first and passed, so by
that log `toggleL` is a machine with an endpoint, without calls, with a
register slot, and `toggleL.machine_closes` is derived (the last test of
`Tools.ShippingShipsFreeCommand.scope`).

## The one missing piece, READ (not measured)

`generateSeqChildN` (`Tools/ShippingMachineDepthCommand.lean` 40–51) builds
`c.seq_child_runN` for a leaf child ONLY from an endpoint whose proof term
is `machine_trace_of_data` (`soundArgs c ``machine_trace_of_data`, line 43):
it takes the arguments of that head and applies the wired twin
`machine_traceL_of_data` to them. `toggleL`'s endpoint is built from
`machine_trace_of_loop` (`loopProof`, `Tools/ShippingMachineCommand.lean`
2150).

The THEOREM it applies, `Tools.ShippingMachineDepthRun.seqChildRunN_full`
(276–303), does not ask that head: its first explicit argument is any
`sound : … → MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc`.
The depth-0 generator `generateSeqChild`
(`Tools/ShippingMachineSeqCommand.lean` 46–66) already maps the three heads
`machine_trace_of_data / _of_loop / _of_regs` to their wired twins
`machine_traceL_of_data / _of_loop / _of_regs` and applies
`seqChildRun_full` — BUILT on `toggleL` (`#machine_composedTS loopParent`,
`ShippingMachineSeqLoopTest` 39). So what is missing is a BRANCH OF A
GENERATOR, not a theorem: the same head test in `generateSeqChildN`.

`generateSeqChildN` returns the existing constant when
`c.seq_child_runN` is already there (line 42). This file therefore adds
`toggleL.seq_child_runN` itself, with `generateSeqChildN`'s own code and
`generateSeqChild`'s head table (`seqChildRunNOfLoop` below — ten lines, no
new theorem), and then runs the BUILT commands. Editing
`Tools/ShippingMachineDepthCommand.lean` (one `else if`) is the proper
repair and is NOT done here (existing file).

## EXPECTED (stated before the build; each step THROWS otherwise)

    NOPORTS LOOPPARENT DATA …
    NOPORTS LOOPPARENT SEQCHILD toggleL.seq_child_runN: …
    loopParent.machine_design_svNR1: source → shipped design's closed emitted texts at depth 1, …
    (#machine_closes_at loopParent: its log line; premise MachineDefines toggleL)
    NOPORTS [loopParent.machine_design_noPortsNR1, loopParent.machine_design_noPortsNR1_closed]: … check antecedent left: none …
    GOALGAP loopParent.machine_design_noPortsNR1_closed_gap … (no gap_ hypothesis)
    NOPORTS PREMISE …_closed: ALLOWED binder hr    : RunsTo (synthesizeCombinational `loopParent) …
    NOPORTS PREMISE …_closed: ALLOWED binder entry : MachineDefines … `loopParent loopParent.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED binder hR0   : MachineDefines … `toggleL toggleL.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED antecedent under the existentials : ChildBnd mref cref w ∧ MachineDefines … `toggleL …
    NOPORTS TWO …loopParent: …      (the audit's line; its name is the audit's)
    NOPORTS LOOPPARENT: …

| endpoint | premise of `loopParent.machine_design_svNR1` | predicted state |
|---|---|---|
| `loopParent.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt loopParent` (open form) | predicted absent in `_closed` (`loopParent.machine_closes_at`, probe: OK), pending build |
| | `hr`, `MachineDefines loopParent`, `MachineDefines toggleL`, `ChildBnd` | run boundary: they stay premises |

`loopParent.machine_design_svNR1` is generated HERE (the base endpoint did
not exist: the probe's failure); the audit's inventory assertion checks that
it does ask the four check premises.

## What is NOT known before the build (in the order the steps run)

1. the eight decided data conditions of `seqChildRunN_full` at `toggleL`
   (`insts = []`, `instFields = []`, a slot, the three lengths, the output
   widths, the reset values' fit): seven of them are those of
   `seqChildRun_full`, decided at `toggleL` by the BUILT depth-0 generator;
   `instFields = []` is new here;
2. the rest of `#machine_design_svNR loopParent 1` after the child's theorem
   (never reached by the probe): the composed theorem over a `Bool` result of
   a `Signal.loop` child;
3. `toggleL.machine_leafKid` (`leafKidTheorem`: `callsOk`, the binders after
   the declared ones, the output name / width / scalar conditions of a `Bool`
   output named by the loop reader) — a failed `decide` is reported by the
   command as `… the generated proof fails`;
4. the audit's shape assertions (`instFields ≠ []` of `loopParent`: a `Bool`
   call result goes through the general closing by the first census,
   `A-remaining.md` §1 row 18 — consistent with `#machine_design_svNR`'s own
   test at `Tools/ShippingMachineDepthCommandR.lean` 188).

## SCOPE (binding for any report)

ONE declaration, `loopParent`: a parent WITH a register, one leaf register
machine child written as a `Signal.loop` (`toggleL`), depth 1, the general
closing. Data conditions decided per declaration; the compiler's guards with
fallback; the conclusion is about `DesignSV (childMap D.modules) 1
(checkedOptimize b)` — the module list, not the SV string, not `#sim`; the
run, the two reflections and `ChildBnd` stay premises (no runtime model).
Nothing is claimed about `toggleL` as an ENTRY.

NAME CLASH: `Tests/Compiler/RemainingProbeTest.lean` section (A2) runs the
same commands on `loopParent` (they fail there and leave nothing, but
`#machine_closes_at loopParent` succeeds and is kept): this file does not
import it and the two must not be imported together.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL
  let r ← Tools.ShippingMachineCommand.readMachine f
  let cr ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let head : String :=
    match env.find? (c ++ `machine_sound) with
    | some (Lean.ConstantInfo.thmInfo ti) =>
      if ti.value.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_loop then
        "machine_trace_of_loop"
      else if ti.value.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_regs then
        "machine_trace_of_regs"
      else if ti.value.isAppOf ``Tools.ShippingMachineAuto.machine_trace_of_data then
        "machine_trace_of_data"
      else "another head"
    | _ => "no machine_sound"
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [f ++ `machineData, f ++ `machine_ok, f ++ `machine_body, f ++ `machine_sound,
      f ++ `machine_composedTS, f ++ `machine_ships_hier, f ++ `machine_closes_at,
      f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1, f ++ `machine_design_noPortsNR1,
      c ++ `machineData, c ++ `machine_ok, c ++ `machine_body, c ++ `machine_sound,
      c ++ `machine_closes, c ++ `seq_child_run, c ++ `seq_child_runN, c ++ `machine_leafKid] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"NOPORTS LOOPPARENT DATA {f}: nDecl={r.nDecl}, binders={r.shape.binders.length}, slots={r.shape.layout.slots.length}, lets={r.shape.layout.lets}, call entries {r.shape.insts.map (·.1)}, argument lets {r.shape.insts.map (·.2.1)}, instFields={r.shape.instFields}, outputs {r.shape.layout.outs.map (·.name)}. CHILD {c}: nDecl={cr.nDecl}, binders={cr.shape.binders.length}, slots={cr.shape.layout.slots.length}, lets={cr.shape.layout.lets}, loops={cr.shape.loops.length}, call entries {cr.shape.insts.map (·.1)}, instFields={cr.shape.instFields}, outputs {cr.shape.layout.outs.map (·.name)}; the head of its machine_sound: {head}. In the environment: {have_}; not: {lack}"
  unless (r.shape.insts.map (·.1)).eraseDups == [c] do
    throwError "{f}: the called declarations are {(r.shape.insts.map (·.1)).eraseDups}, expected [{c}]"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  unless cr.shape.insts.isEmpty do throwError "{c}: it has calls — not a leaf"
  if cr.shape.layout.slots.isEmpty then throwError "{c}: no register slot"
  unless head == "machine_trace_of_loop" || head == "machine_trace_of_regs" do
    throwError "{c}: the head of its machine_sound is {head}; this file is written for machine_trace_of_loop / _of_regs (with machine_trace_of_data the built generator needs no help: use NoPortsMidTest's pattern)"
  for n in [c ++ `seq_child_runN, f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1,
      f ++ `machine_design_noPortsNR1, f ++ `machine_closes_at] do
    if env.contains n then
      throwError "{n}: exists already — is Tests.Compiler.RemainingProbeTest imported? (NAME CLASH, see the header)"
  for n in [c ++ `machine_closes, f ++ `machine_ok, f ++ `machine_body] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"

/-! ## The child's theorem at depth: `generateSeqChildN`'s code with `generateSeqChild`'s head table -/

namespace Tests.Compiler.NoPortsLoopParentTest
open Lean Meta

/-- `c.seq_child_runN` for a leaf register child whose endpoint is built from
`machine_trace_of_loop` or `machine_trace_of_regs`:
`Tools.ShippingMachineDepthRun.seqChildRunN_full` at the endpoint's wired
twin (`generateSeqChild`'s table, `Tools/ShippingMachineSeqCommand.lean`
53–58), its eight data conditions decided by the kernel (as
`generateSeqChildN`, `Tools/ShippingMachineDepthCommand.lean` 44–50). Added
through the generators' `addTheorem` (kernel-checked, standard axioms). -/
def seqChildRunNOfLoop (c : Name) : MetaM Name := do
  let name := c ++ `seq_child_runN
  if (← getEnv).contains name then throwError "{name}: exists already"
  let some (.thmInfo ti) := (← getEnv).find? (c ++ `machine_sound)
    | throwError "{c}: no machine_sound"
  let v := ti.value
  let headL ← if v.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_loop then
      pure ``Tools.ShippingMachineLoopL.machine_traceL_of_loop
    else if v.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_regs then
      pure ``Tools.ShippingMachineLoopL.machine_traceL_of_regs
    else throwError "{c}.machine_sound is not built from machine_trace_of_loop or _of_regs"
  let soundL := mkAppN (mkConst headL) v.getAppArgs
  let mut p ← mkAppOptM ``Tools.ShippingMachineDepthRun.seqChildRunN_full
    #[none, none, none, none, none, none, soundL]
  for _ in [0:8] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  Tools.ShippingMachineLinkedCommand.addTheorem name (← inferType p) p
  return name

end Tests.Compiler.NoPortsLoopParentTest

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsLoopParentTest.seqChildRunNOfLoop c
  Tests.Compiler.NoPortsTest.stdAxioms name
  let ty := (← Lean.getConstInfo name).type
  unless (ty.find? (·.isConstOf ``Tools.ShippingMachineDepth.SeqChildRunN)).isSome do
    throwError "{name}: its statement does not conclude SeqChildRunN"
  Lean.logInfo m!"NOPORTS LOOPPARENT SEQCHILD {name}: Tools.ShippingMachineDepthRun.seqChildRunN_full at the wired twin of {c}.machine_sound (a Signal.loop endpoint), its eight data conditions decided by the kernel, standard axioms — the theorem generateSeqChildN builds for a machine_trace_of_data child; nothing else is new in this file"

/-! ## The three BUILT commands -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent

set_option maxHeartbeats 0 in
#machine_no_ports Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent 1

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_design_noPortsNR1_closed

/-! ## The audit of `NoPortsTwoTest`, on `loopParent`

Premise listing (every binder and antecedent of the closed endpoint,
ALLOWED / NOT ALLOWED), the inventory of `loopParent.machine_design_svNR1`,
no checker constant in the three statements, no gap hypothesis, standard
axioms, one reflection binder per called declaration, the shape that was
read. It THROWS on any failure. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsTwoTest.audit
    ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
    [``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL
  -- the child's depth theorem is the one added above (the generator did not replace it)
  Tests.Compiler.NoPortsTest.stdAxioms (c ++ `seq_child_runN)
  -- nothing is claimed about the child as an entry: no design-level endpoint under its name
  for n in [c ++ `machine_design_svNR1, c ++ `machine_design_noPortsNR1,
      c ++ `machine_design_noPortsNR1_closed] do
    if (← Lean.getEnv).contains n then
      throwError "{n}: exists — this file must not produce a design-level endpoint for {c}"
  Lean.logInfo m!"NOPORTS LOOPPARENT: {f} — a parent WITH a register whose one callee {c} is a leaf register machine written as a Signal.loop. {f}.machine_design_noPortsNR1 and its _closed form by the BUILT #machine_design_svNR / #machine_closes_at / #machine_no_ports, after {c}.seq_child_runN was supplied from the loop endpoint's wired twin (the head test generateSeqChildN lacks). SCOPE: one declaration, depth 1, data conditions decided per declaration, compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim; the run, MachineDefines {f}, MachineDefines {c} and ChildBnd stay premises. Nothing about {c} as an entry"
