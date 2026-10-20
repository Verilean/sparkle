import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.ShippingCallsCloseDeepTest
import Tests.Compiler.ShippingMachineDepthTest

/-! # `#machine_no_ports` on `mid` AS AN ENTRY: a domain-polymorphic parent of one leaf register machine (G1, round par/a-13)

`mid` (`Tests/Compiler/ShippingMachineSeqTest.lean`):

    @[hardware_module] def mid {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal dom (BitVec 8))
        let k := cnt en          -- CntOut: n : BitVec 8, hit : Bool
        r <~ k.n
        return ({ n := rs, hit := k.hit } : CntOut dom)

A parent WITH a register whose one callee `cnt` is a LEAF REGISTER machine:
the scope `#machine_no_ports` states (`Tools/ShippingNoPortsCommand.lean`,
`scopeP`). No new theorem is written in this file: three BUILT commands are
run on one more declaration.

What was MEASURED before this file (round par/a-12, the log-only probe
`Tests/Compiler/RemainingProbeTest.lean`, `docs/parallel/verification-a12.md`):

    REMAINING PROBE mid: #machine_design_svNR 1: OK
    REMAINING PROBE mid: #machine_closes_at: OK
    REMAINING PROBE …mid audit: OK — …mid.machine_design_noPortsNR1_closed passes the audit of NoPortsTwoTest

A probe line counts for nothing: the probe asserts nothing and is not in
`Tests/AllTests.lean`. THIS file is the proper test: every command below
THROWS where the probe would only log.

What is NEW against `parent`, `chained`, `two` (all over `defaultDomain`,
all with a `Signal` result): the ENTRY is domain-polymorphic (the domain
binder is a declared binder without a port) and its result is a STRUCTURE
(`CntOut`: two outputs, `n` and `hit`), one of them (`hit`) a field of the
call's result passed through.

## NAME CLASH with the probe (integrator)

`Tests/Compiler/RemainingProbeTest.lean` creates the SAME constants in its
own module (`mid.machine_design_svNR1`, `mid.machine_ships_hierNR1`,
`mid.machine_runFacts`, …, `mid.machine_design_noPortsNR1(_closed)`,
possibly `mid.machine_closes_at`). This file does NOT import it and it must
not import this file; the two cannot be loaded into one module. Either drop
section (A1) `mid` (and (A3) `callerInner`, see
`Tests/Compiler/OneOutCallerInnerTest.lean`) from the probe, or keep the
probe target-built only (never in `Tests/AllTests.lean`, never built in the
same `lake build` as a module importing both).

The imports are the probe's imports that matter for `mid`:
`NoPortsTwoTest` (the audit), `ShippingCallsCloseDeepTest` (`grand`'s depth
endpoint and deep closing are generated there, with what they leave under
`mid`'s and `cnt`'s names) and `ShippingMachineDepthTest` — so the
environment before the first command is the one the probe measured in, for
`mid`.

## EXPECTED (stated before the build; each command THROWS otherwise)

    mid.machine_design_svNR1: source → shipped design's closed emitted texts at depth 1, …
    (#machine_closes_at mid: its log line; premise MachineDefines cnt)
    NOPORTS [mid.machine_design_noPortsNR1, mid.machine_design_noPortsNR1_closed]: … check antecedent left: none …
    GOALGAP mid.machine_design_noPortsNR1_closed_gap from … (no gap_ hypothesis)
    NOPORTS PREMISE …_closed: ALLOWED binder hr    : RunsTo (synthesizeCombinational `mid) …
    NOPORTS PREMISE …_closed: ALLOWED binder entry : MachineDefines … `mid mid.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED binder hR0   : MachineDefines … `cnt cnt.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED antecedent under the existentials : ChildBnd mref cref w ∧ MachineDefines … `cnt …
    NOPORTS TWO …mid: …            (the audit's line; its name is the audit's)
    NOPORTS MID: …

The binder names and the conjunct structure of the boundary are whatever
the generators write (not read off a build).

| endpoint | premise of `mid.machine_design_svNR1` | predicted state |
|---|---|---|
| `mid.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN (this test; the generators are built, the probe logged OK) — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt mid` (open form) | predicted absent in `_closed` (`mid.machine_closes_at`), pending build |
| | `hr`, `MachineDefines mid`, `MachineDefines cnt`, `ChildBnd` | run boundary: they stay premises |

`mid.machine_design_svNR1` is generated HERE (it did not exist as an
endpoint: `mid` had no design-level endpoint of its own); the audit's
inventory assertion checks that it does ask the four check premises, so
that "absent" is a comparison with a statement of this same build.

## SCOPE (binding for any report)

ONE declaration, `mid`, AS AN ENTRY: a parent WITH a register, one leaf
register machine child (`cnt`), depth 1, the general (multi-output) closing.
(i) Data conditions decided per declaration by the kernel — those listed in
`Tests/Compiler/NoPortsTest.lean` (i), for `mid` at its `nDecl` and for
`cnt` (`machine_leafKid`) — are conditions, not reductions. (ii) The result
depends on the compiler's guards with fallback. (iii) The conclusion is
about `DesignSV (childMap D.modules) 1 (checkedOptimize b)` — the module
list, not the SV string, not `#sim`. (iv) The run, the two reflections and
`ChildBnd` stay premises (no runtime model).

NOT covered, and NOT implied by this endpoint: `mid` AS A CHILD. `mid` is
`grand`'s child (`grand → mid → cnt`), a child WITH a call of its own under
the general closing. The endpoint here gives NOTHING for `grand`:
`grand.machine_design_svNR2` keeps every one of its check premises
(`shipsHierCheck`, `kidsMaskedN`, `designCheck 2`, `outsCheck 2`). The facts
generated here (`mid.machine_runFacts`, `_outsG1`, `_maskedG`, `_designP1`,
`_portsG`) are about the module of `mid`'s OWN entry run; `grand`'s theorems
ask them of the module the child cache serves (`RealChild mref cref mid y`),
at a depth one higher, for the UNOPTIMISED child module, over `grand`'s
design — unit U3 of `docs/parallel/A-remaining.md` (U2's bridge made
recursive for a child under the general closing), not written.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid

set_option maxHeartbeats 0 in
#machine_no_ports Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid 1

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_noPortsNR1_closed

/-! ## The audit of `NoPortsTwoTest`, on `mid`

Premise listing (every binder and antecedent of the closed endpoint,
ALLOWED / NOT ALLOWED), the inventory of `mid.machine_design_svNR1`, no
checker constant in the three statements, no gap hypothesis, standard
axioms, one reflection binder per called declaration, the shape that was
read (a call, `instFields ≠ []`, a register). It THROWS on any failure. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsTwoTest.audit ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
    [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt]

/-! ## The scope facts this file relies on, asserted on the reader's data, and what is NOT touched -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
  let cntN := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let grandN := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
  let r ← Tools.ShippingMachineCommand.readMachine f
  unless (r.shape.insts.map (·.1)).eraseDups == [cntN] do
    throwError "{f}: the call entries are {r.shape.insts.map (·.1)}, expected [{cntN}]"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  if r.shape.instFields.isEmpty then
    throwError "{f}: instFields = [] — not the general closing"
  unless r.shape.layout.outs.map (·.name) == ["n", "hit"] do
    throwError "{f}: the outputs are {r.shape.layout.outs.map (·.name)}, expected [n, hit]"
  let cr ← Tools.ShippingMachineCommand.readMachine cntN
  unless cr.shape.insts.isEmpty do throwError "{cntN}: it has calls — not a leaf"
  if cr.shape.layout.slots.isEmpty then throwError "{cntN}: no register"
  -- `grand`: nothing was generated under its check-free names, and its depth
  -- endpoint still asks the four check premises
  for n in [grandN ++ `machine_design_noPortsNR2, grandN ++ `machine_design_noPortsNR2_closed,
      grandN ++ `machine_design_noPortsNR1, grandN ++ `machine_runFacts] do
    if (← Lean.getEnv).contains n then
      throwError "{n}: exists — this file must not produce anything for {grandN}"
  let gOld := grandN ++ `machine_design_svNR2
  let gT := (← Lean.getConstInfo gOld).type
  for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (gT.find? (·.isConstOf c)).isSome do
      throwError "{gOld}: does not mention {c} (the reading of {grandN} is wrong)"
  Lean.logInfo m!"NOPORTS MID: {f} — nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, call entries [{cntN}] (a leaf register machine), instFields={r.shape.instFields}, outputs [n, hit]: a domain-polymorphic parent WITH a register and a structure result, the general closing, depth 1. Against {f}.machine_design_svNR1 (generated in this file) the premises shipsHierCheck, kidsMaskedN, designCheck, outsCheck are absent from {f}.machine_design_noPortsNR1 and its closed form (the audit above threw otherwise). This is {f} AS AN ENTRY. NOTHING for {grandN}: {gOld} still mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck, and no check-free constant exists under {grandN}'s names ({f} as a child with a call of its own under the general closing is unit U3, not written). SCOPE: one declaration, data conditions decided per declaration (conditions, not reductions), the run, the reflections and ChildBnd remain premises, compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim."
