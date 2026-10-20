import Tests.Compiler.OneOutFamilyTest

/-! # `#machine_oneout` on `midH`: a one-output parent that was in scope and never run (G1, round par/a-12)

`midH` (`Tests/Compiler/ShippingMachineDepthHTest.lean`):

    @[hardware_module] def midH {dom} (en : Signal dom Bool) : CntOut dom :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal dom (BitVec 8))
        let y := rcH rs
        r <~ Signal.mux en y rs
        return { n := rs, hit := rs === 7#8 }

By READING (`docs/parallel/A-remaining.md` §2, unit U1): a parent WITH a
register (`r`), ONE call entry of the GATE child `rcH` (`BitVec 8 → BitVec 8`,
domain-polymorphic like `pickD`; its `gate_*` data were left by
`#machine_composed midH`), a call result that is ONE `Signal (BitVec 8)` —
so `shape.instFields = []`, the ONE-OUTPUT closing. `midH.machine_design_svHR`
(`ShippingChildBoundaryTest` 349) and `midH.machine_closes_at`
(`ShippingCallsCloseTest` 78, `auditClosed … 1`) are BUILT. That is the scope
of `#machine_oneout` (`Tools/ShippingOneOutGenCommand.lean`, BUILT): no
refusal line of its scope test applies. No new theorem is written in this
file: the generator is run on one more declaration.

What is NEW against the seven gate-children parents that are built
(`caller`, `callerTwice`, `callerD`, `callerNested`, `callerRep`,
`callerMix`, `callerABA`):

* the PARENT has TWO outputs (`n : BitVec 8`, `hit : Bool`) — "one-output"
  is about the CALL's result, not the parent's result; the general theorems
  quantify over `d.shape.layout.outs` (`outTy`, `hon`, `hoty`) and none asks
  one output of the parent (read: `core_runFactsH`, `core_portsMatch_raw₁`,
  `core_hierTyped₁`, `core_designCheckH`, `core_outsCheck_all_gate`). NOT
  known before the build: `midH.oneout_outChars`, `_outScalar`, `_outTy` on
  the outputs `n`, `hit` (the same output structure `CntOut` passes the same
  three conditions in the BUILT `cnt.machine_leafKid`);
* the parent is itself a `@[hardware_module]` and domain-polymorphic
  (`nDecl = 2`: the domain binder, `en`), as `callerD`;
* the call's argument is the register's read `rs` (as `callerLN`'s first
  argument).

## EXPECTED (stated before the build; the command THROWS on another class)

    ONEOUT GEN …midH: GENERATED [midH.machine_design_svH_full, midH.machine_design_svH_full_closed] — …
      callArgsOk with midH.oneout_kidIns = [[8]], per entry the callee among [rcH] … [8]
    ONEOUT FULL PREMISE …_closed: run        | binder hr : RunsTo (synthesizeCombinational `midH) …
    ONEOUT FULL PREMISE …_closed: reflection | binder entry : MachineDefines … `midH midH.machineData.shape
    ONEOUT FULL PREMISE …_closed: reflection | binder hR0 : EntryDefines … `rcH rcH.gateValue
    ONEOUT FULL PREMISE …_closed: ChildBnd   | antecedent under the existentials : ChildBnd mref cref w
    ONEOUT FULL PREMISE …_closed: reflection | antecedent under the existentials : EntryDefines … `rcH rcH.gateValue
    GOALGAP midH.machine_design_svH_full_closed_gap … (none NOT ALLOWED)
    ONEOUT FAMILY midH: … other: NONE …

The numerals (`[[8]]`, `[8]`) are predictions; the generator prints the
computed ones. A FAILED outcome is `ONEOUT GEN midH: FAILED (data condition
… [the theorem's name]: …)`: then nothing is left under the names and NO
premise counts as removed for `midH`.

| endpoint | premise of `midH.machine_design_svHR` | predicted state |
|---|---|---|
| `midH.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck D.modules b` | WRITTEN (this test; the generator is built) — predicted absent, pending build |
| | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `hr`, `MachineDefines midH`, `EntryDefines rcH`, `ChildBnd` | run boundary: they stay premises |

## SCOPE (binding for any report)

ONE declaration, `midH`, AS AN ENTRY: a parent WITH a register, one gate
child, the one-output closing. Data conditions decided per declaration by
the kernel (`midH.oneout_*`, `rcH.gate_width`, what `#gate_child` left) are
conditions, not reductions; the run, `MachineDefines midH`, `EntryDefines
rcH`, `ChildBnd` stay premises; the result depends on the compiler's guards
with fallback; the conclusion is about `DesignSV (childMap D.modules) 0
(checkedOptimize b)` — the module list, not the SV string, not `#sim`.

NOT covered, and NOT implied by this endpoint: `midH` AS A CHILD. The depth
endpoints of its parents (`grandH.machine_design_svNR1/2`,
`mixD1.machine_design_svNR1/2`, `topD2.machine_design_svNR2/3`,
`mixDeep.machine_design_svNR2`) keep every one of their check premises
(`shipsHierCheck`, `kidsMaskedN`, `designCheck n`, `outsCheck n`): the facts
generated here are about the module of `midH`'s OWN entry run, the parents'
theorems ask them of the module the child cache serves
(`RealChild mref cref midH y`) — the bridge is unit U2 of
`docs/parallel/A-remaining.md`, not written.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
    [``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH] false

/-! ## The scope facts this file relies on, asserted on the reader's data

An error here means the READING above is wrong (the declaration is not the
shape the header says), independently of the generator's outcome. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let r ← Tools.ShippingMachineCommand.readMachine f
  unless r.shape.insts.map (·.1) == [rc] do
    throwError "{f}: the call entries are {r.shape.insts.map (·.1)}, expected [{rc}]"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  unless r.shape.instFields.isEmpty do
    throwError "{f}: instFields = {r.shape.instFields} — not the one-output closing"
  unless r.shape.layout.outs.map (·.name) == ["n", "hit"] do
    throwError "{f}: the outputs are {r.shape.layout.outs.map (·.name)}, expected [n, hit]"
  unless (← Lean.getEnv).contains (rc ++ `gate_peel) do
    throwError "{rc}: no gate_peel — not a gate child with #gate_child data"
  let full := f ++ `machine_design_svH_full
  let old := f ++ `machine_design_svHR
  let outNames := r.shape.layout.outs.map (·.name)
  if (← Lean.getEnv).contains full then
    Lean.logInfo m!"ONEOUT MIDH: {f} — nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, call entries [{rc}] (gate child), instFields=[], outputs {outNames}: a parent WITH a register and TWO outputs of its own, the one-output closing. The endpoint {full} and its closed form are in the environment; the audit above printed their complete premise lists. This is {f} AS AN ENTRY; the depth endpoints of its parents (grandH, mixD1, topD2, mixDeep) are untouched."
  else
    Lean.logInfo m!"ONEOUT MIDH: {f} has the shape read (nDecl={r.nDecl}, one gate call entry, instFields=[], outputs {outNames}) but NO endpoint was generated: no premise of {old} counts as removed."
