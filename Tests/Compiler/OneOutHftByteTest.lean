import Tests.Compiler.OneOutCallerFullTest
import Tests.Compiler.OneOutLeafAudit
import Tests.Compiler.ShippingMachineTeleTest
import Tools.ShippingLeafOneOut
import Tools.ShippingLeafOneOutGen
import Tools.ShippingOneOutConns
import Tools.ShippingOneOutFullCommand
import Tools.ShippingPortsMatchShipped
import Tools.ShippingHierGateAny
import Tools.ShippingChecksCoreGate
import Tools.ShippingCallWidthsStrict
import Tools.ShippingFinalGoalCommand

/-! # ONE endpoint, `hftByte` (child `Sparkle.IP.Net.HTTP.httpGetByte`, a slotless machine-route leaf with an implicit domain binder): the one-output head by hand (G1, round par/a-11)

`Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte inByte inValid :=
(hftStrategy inByte inValid).outByte`: the parser → emitter chain of
`IP/Net/HFTStrategy.lean`; `httpGetEmitter` calls the `@[hardware_module]`
byte table `httpGetByte {dom} (cntSig : Signal dom (BitVec 6)) : Signal dom
(BitVec 8)` inside its body. The compiler flattens the chain into ONE
machine (the telescope); the call sits in a sub-machine.

## What was READ, and what is only decided (nothing here was measured)

The parent `hftByte`:
* a register: YES by reading — `hftStrategy`'s own `cntR`, and the parser's
  and the emitter's registers are the flattened machine's slots. The
  theorem that says so is `hftByte_slots` (`slots ≠ []`).
* `nDecl`: `readMachine` sets it to the number of binders peeled off the
  entry — `inByte`, `inValid`, no domain binder (`defaultDomain` is written)
  — so 2 by reading. It is NOT written as a literal below: `hftNDecl` is
  `nIn - insts.length`, the one number for which `callsOk`'s first conjunct
  (`nDecl + insts.length = nIn`) can hold; the BUILT
  `hftByte.machine_closes_at` decided `gateCallsOk` at the reader's `nDecl`,
  so the two agree. The reading "2" is not a theorem here; the reader's
  number is printed by the `ONEOUT DATA` log line (nothing is asserted).
* entries: one, the callee `httpGetByte` by reading (one emitter, one call).
  The theorem is `hftByte_entries`, over every `k < insts.length`.
* `instFields = []`: implied by the BUILT `gateCallsOk` decide of
  `hftByte.machine_closes_at`; here `hftByte_instFields`.
* `hftByte.machine_design_svHR`: EXISTS (BUILT,
  `Tests/Compiler/ShippingChildBoundaryTest.lean` line 356), and
  `hftByte.machine_closes_at` with one premise, `MachineDefines` of
  `httpGetByte` (`Tests/Compiler/ShippingCallsCloseTest.lean`,
  `auditClosed … 1`).
* the output: the projection `.outByte` of the structure result; the
  entry's type is `Signal defaultDomain (BitVec 8)`, so `machOuts?` gives
  the one output `out` by reading (`hftByte_outTy`, `_outChars`,
  `_outScalar` are over whatever the layout has).

The child `httpGetByte` (`SlotlessLeaf`'s fields), `nIn = 2` by reading (the
domain binder and `cntSig`; no call):

| field | theorem | state by reading |
|---|---|---|
| `ok`, body | `httpGetByte.machine_ok`, `.machine_body` | generated, BUILT (`ShippingMachineCombTest`) |
| `gateCallsOk nIn` | `httpGetByte_gate` | the SAME decide is in the BUILT `hftByte.machine_closes_at` (at the reader's `nDecl`, which is `nIn` for a child without calls) — plausible |
| `callsOk nIn` | `httpGetByte_calls` | a conjunct of `gateCallsOk` (`gateCallsOk_parts`); plausible |
| no domain binder after `nIn` | `httpGetByte_dom` | a conjunct of `gateCallsOk`; the implicit domain binder is the FIRST binder, inside the first `nIn`; plausible |
| slot count | `httpGetByte_ss` | a conjunct of `gateCallsOk`; plausible |
| `insts = []` | `httpGetByte_insts` | `closesAtCore` checked `insts.isEmpty` by compiled code; `rfl` on a literal; plausible |
| `lets ≠ 0` | `httpGetByte_lets` | decided in the BUILT `machine_closes_at`; plausible |
| `slots = []` | `httpGetByte_slots` | `rfl` in the BUILT `machine_closes_at`; plausible |
| the one output `out` | `httpGetByte_one` | `⟨_, rfl, rfl⟩` in the BUILT `machine_closes_at`; plausible |
| `outTy` | `httpGetByte_outTy` | decided in the BUILT `machine_closes_at`; plausible |
| output name chars | `httpGetByte_outChars` | OPEN (never decided for this declaration); the name is `out` by the row above, so expected true; cost: `String.toList` of a 3-character literal |
| output scalar | `httpGetByte_outScalar` | OPEN (never decided here); `BitVec 8` is a scalar type by reading |
| own closing | `httpGetByte.machine_closes` | generated, BUILT (used by `hftByte.machine_closes_at`) |

KERNEL COST. The large terms are the two `machineData` constants: the
child's 12 hardware `let`s and 18-way mux, and the parent's flattened
telescope. `callsOk` walks every `let` field and the core (`fieldsOkB`,
`reads`): `httpGetByte_gate` (child) and `hftByte_callsOk` (parent) are the
two decides over whole terms; both were ALREADY decided once inside the
BUILT `machine_closes_at` at the default recursion depth. `hftByte_strict`,
`hftByte_callArgs`, `hftByte_entries`, `hftByte_domB`, `hftByte_nomem` touch
binder / entry lists only (but must reduce the `machineData` constant to
reach them: projections of a structure literal). Every decide is written
`first | decide | decide +kernel` under `maxRecDepth 100000`; a failure on
depth or time is a FAILED NAMED CONDITION, not a false theorem.

Each condition is its OWN theorem, so that a failing one is named by the
error; the bundle `httpGetByte_leaf` only assembles them.

## EXPECTED (stated before the build)

`ONEOUT DATA hftByte: nDecl=2 nIn=3 …` (a log line of what the reader reads;
the numbers are predictions) then `SVHFULL GENERATED
[hftByte.machine_design_svH_full, hftByte.machine_design_svH_full_closed]`;
the closed form's premises: the run, `MachineDefines` of `hftByte`,
`MachineDefines` of `httpGetByte`, and under `∃ raw D`: `ChildBnd`,
`MachineDefines` of `httpGetByte`. Class `other`: NONE on the closed form.
The test throws otherwise.

## SCOPE (binding for any report)

ONE declaration, `hftByte`: a parent WITH a register, the one-output
closing, a child that is a SLOTLESS LEAF MACHINE with the one output `out`.
Data conditions decided per declaration: conditions, not reductions. The
runtime boundary stays premises (the run, `MachineDefines hftByte`,
`MachineDefines httpGetByte`, `ChildBnd`). The result depends on the
compiler's guards. The conclusion is about
`DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module list, not
the SV string, not `#sim`. NOT covered: slotless PARENTS, machine children
with registers or with calls, several outputs, "all successful inputs".

NAME CLASH, on purpose not hidden: `#machine_oneout_any hftByte`
(`Tests/Compiler/OneOutAnyFamilyTest.lean`) generates the SAME endpoint
name. The two files must not both be imported by one module unless the
family test imports this one (then it reports PRESENT, not GENERATED).

UNVERIFIED at the time of writing: this file was not built. -/

-- What the reader reads (LOG ONLY; nothing is asserted here).
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let show1 (f : Lean.Name) : Lean.Meta.MetaM String := do
    let r ← Tools.ShippingMachineCommand.readMachine f
    let bs := r.shape.binders.map fun b =>
      if b.2 == Sparkle.Compiler.Elab.MixedGateBinder.domain then "dom"
      else toString (Tools.ShippingMachineEntry.kindTy b.2).bitWidth
    let insts := r.shape.insts.map fun c => s!"{c.1} args(let indices)={c.2.1}"
    let outs := r.shape.layout.outs.map fun o => s!"{o.name}:{o.width}"
    return s!"ONEOUT DATA {f}: nDecl={r.nDecl} nIn={r.nIn} slots={r.shape.layout.slots.length} lets={r.shape.layout.lets} insts={insts} instFields={r.shape.instFields} outs={outs} binders(width or dom)={bs}"
  let s1 ← show1 ``Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte
  Lean.logInfo m!"{s1}"
  let s2 ← show1 ``Sparkle.IP.Net.HTTP.httpGetByte
  Lean.logInfo m!"{s2}"

namespace Tests.Compiler.OneOutHftByteTest
open Sparkle.Tests.Compiler.ShippingMachineTeleTest

/-! ## The child `httpGetByte`: every condition its own theorem -/

set_option maxRecDepth 100000 in
/-- `gateCallsOk` at `nIn` (the decide of the BUILT `hftByte.machine_closes_at`). -/
theorem httpGetByte_gate :
    Tools.ShippingMachineAuto.MachineData.gateCallsOk Sparkle.IP.Net.HTTP.httpGetByte.machineData
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.nIn = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- `callsOk` at `nIn`: a conjunct of `httpGetByte_gate`. -/
theorem httpGetByte_calls :
    Tools.ShippingMachineAuto.MachineData.callsOk Sparkle.IP.Net.HTTP.httpGetByte.machineData
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.nIn = true := by
  first
    | exact (Tools.ShippingLeafOneOutGen.gateCallsOk_parts httpGetByte_gate).1
    | decide
    | decide +kernel

set_option maxRecDepth 100000 in
/-- No domain binder after the first `nIn` (the implicit domain binder is
among the first `nIn`): a conjunct of `httpGetByte_gate`. -/
theorem httpGetByte_dom :
    ∀ b ∈ Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.binders.drop
        Sparkle.IP.Net.HTTP.httpGetByte.machineData.nIn,
      b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain := by
  first
    | exact (Tools.ShippingLeafOneOutGen.gateCallsOk_parts httpGetByte_gate).2.2.1
    | decide
    | decide +kernel

/-- No call: a LEAF. -/
theorem httpGetByte_insts : Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.insts = [] := by
  first | rfl | decide

set_option maxRecDepth 100000 in
/-- The slot count: a conjunct of `httpGetByte_gate`. -/
theorem httpGetByte_ss :
    Sparkle.IP.Net.HTTP.httpGetByte.machineData.ss.length =
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.slots.length := by
  first
    | exact (Tools.ShippingLeafOneOutGen.gateCallsOk_parts httpGetByte_gate).2.1
    | decide
    | decide +kernel

set_option maxRecDepth 100000 in
theorem httpGetByte_outTy :
    ∀ o ∈ Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem httpGetByte_outChars :
    ∀ o ∈ Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem httpGetByte_outScalar :
    ∀ o ∈ Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- At least one hardware `let`. -/
theorem httpGetByte_lets : Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.lets ≠ 0 := by
  first | decide | decide +kernel

/-- SLOTLESS. -/
theorem httpGetByte_slots :
    Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.slots = [] := by
  first | rfl | decide

/-- The one output `out`. -/
theorem httpGetByte_one :
    ∃ o, Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs = [o] ∧ o.name = "out" :=
  ⟨_, rfl, rfl⟩

/-- **The bundle of `httpGetByte`'s per-declaration conditions**, given its
reflection in the run's contexts: the named theorems above, its generated
endpoint facts and its generated closing. -/
theorem httpGetByte_leaf {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    Tools.ShippingLeafOneOut.SlotlessLeaf mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData :=
  { any :=
      { ok := Sparkle.IP.Net.HTTP.httpGetByte.machine_ok
        body := Sparkle.IP.Net.HTTP.httpGetByte.machine_body
        calls := httpGetByte_calls
        dom := httpGetByte_dom
        leaf := httpGetByte_insts
        ss := httpGetByte_ss
        outTy := httpGetByte_outTy
        outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          (httpGetByte_outChars o ho)
        outScalar := httpGetByte_outScalar
        entry := hR0
        closes := fun mc cc => Sparkle.IP.Net.HTTP.httpGetByte.machine_closes mc _ cc _ }
    gate := httpGetByte_gate
    lets := httpGetByte_lets
    slots := httpGetByte_slots
    one := httpGetByte_one }

/-- The output ports of a real child of `httpGetByte` are its layout's. -/
theorem httpGetByte_outTys {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y) :
    Tools.ShippingChildIfaceTy.ChildOutTys
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs y.1 :=
  (httpGetByte_leaf hR0).outTys hy

/-- (`hkidT`) The emitter's width map resolves `httpGetByte`'s output port. -/
theorem httpGetByte_portsIn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y) :
    Tools.ShippingLeafTyped.PortsIn y.1 :=
  (httpGetByte_leaf hR0).portsIn hy

/-- (`hkidIn`, `hkidInD`) The `j`-th input port of a real child of
`httpGetByte` has the `j`-th declared width (the domain binder is not a
port: `declWidths` filters it) in the emitter's table AND in the IR's. -/
theorem httpGetByte_inWidths {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y)
    {j : Nat} {q : Sparkle.IR.AST.Port} (hq : y.1.inputs[j]? = some q) :
    ∃ wd, (Tools.ShippingPortWidthsPure.declWidths
        Sparkle.IP.Net.HTTP.httpGetByte.machineData)[j]? = some wd ∧
      Tools.ShippingDesignSV.weS y.1 q.name = wd ∧
      Sparkle.IR.RegDedup.declWidth y.1 q.name = wd :=
  (httpGetByte_leaf hR0).inWidths hy hq

/-- (`hkidTy`) A real child of `httpGetByte` is a width-typed child in its
own declared widths. -/
theorem httpGetByte_childTyped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y) :
    Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth y.1) y.1 = true :=
  (httpGetByte_leaf hR0).childTyped hy

/-- (`hkidK`) The children's text check of a real child of `httpGetByte`. -/
theorem httpGetByte_kidK {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true :=
  (httpGetByte_leaf hR0).kidK hy

/-- (`hkidA`) A real child of `httpGetByte` assigns its output; its design
is empty. -/
theorem httpGetByte_kidA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true :=
  (httpGetByte_leaf hR0).kidA hy

/-- (`hkidR`) A real child of `httpGetByte` has no instance statement. -/
theorem httpGetByte_kidR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``Sparkle.IP.Net.HTTP.httpGetByte y) :
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn :=
  (httpGetByte_leaf hR0).kidR hy

/-! ## The parent `hftByte`: the data conditions, each named -/

/-- The number of declaration binders of `hftByte`, as the data fixes it:
`callsOk d n` asks `n + insts.length = nIn`. By reading the source it is 2;
the reader's own number is in the `ONEOUT DATA` log line above. -/
noncomputable def hftNDecl : Nat :=
  hftByte.machineData.nIn - hftByte.machineData.shape.insts.length

/-- The argument widths of `httpGetByte`: its declared widths (the domain
binder filtered out), for every call entry of `hftByte`. -/
noncomputable def hftKidIns : Nat → List Nat := fun _ =>
  Tools.ShippingPortWidthsPure.declWidths Sparkle.IP.Net.HTTP.httpGetByte.machineData

set_option maxRecDepth 100000 in
theorem hftByte_callsOk :
    Tools.ShippingMachineAuto.MachineData.callsOk hftByte.machineData hftNDecl = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem hftByte_slotLen :
    hftByte.machineData.ss.length = hftByte.machineData.shape.layout.slots.length := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem hftByte_domB : ∀ b ∈ hftByte.machineData.shape.binders.drop hftNDecl,
    b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain := by
  first | decide | decide +kernel

theorem hftByte_insts : hftByte.machineData.shape.insts ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

theorem hftByte_instFields : hftByte.machineData.shape.instFields = [] := by
  first | rfl | decide

set_option maxRecDepth 100000 in
theorem hftByte_outTy : ∀ o ∈ hftByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem hftByte_nomem : ∀ c ∈ hftByte.machineData.shape.insts,
    Sparkle.Compiler.MachMemory.memChild? c.1 = none := by
  first | decide | decide +kernel

/-- The PARENT has a register. -/
theorem hftByte_slots : hftByte.machineData.shape.layout.slots ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

set_option maxRecDepth 100000 in
theorem hftByte_outChars : ∀ o ∈ hftByte.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem hftByte_outClean : ∀ o ∈ hftByte.machineData.shape.layout.outs,
    Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
  fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (hftByte_outChars o ho)

set_option maxRecDepth 100000 in
theorem hftByte_outScalar : ∀ o ∈ hftByte.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- Every call entry's callee is `Sparkle.IP.Net.HTTP.httpGetByte` (decided over all
`k < insts.length`; no entry count is written). -/
theorem hftByte_entries : ∀ (k : Nat) (hk : k < hftByte.machineData.shape.insts.length),
    (hftByte.machineData.shape.insts[k]).1 = ``Sparkle.IP.Net.HTTP.httpGetByte := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The width of the type of the binder of every call's result is the width
of `Sparkle.IP.Net.HTTP.httpGetByte`'s output field (the strict condition: with no field list, every
output of the child is compared). -/
theorem hftByte_strict :
    Tools.ShippingCallWidthsStrict.callWidthsStrict hftByte.machineData hftNDecl
      (fun _ => Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The widths of the types of `hftByte`'s `let` binders of every call's
arguments are `Sparkle.IP.Net.HTTP.httpGetByte`'s declared widths. -/
theorem hftByte_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk hftByte.machineData hftNDecl hftKidIns = true := by
  first | decide | decide +kernel


/-- (`hkidW`) Every output port of a real child of a call has the width of
the type of the call's binder. -/
theorem hftByte_kidW {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    ∀ (k : Nat) (hk : k < hftByte.machineData.shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildInv.RealChild mref cref (hftByte.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs,
        (hftByte.machineData.shape.binders[hftNDecl + k]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some p.ty.bitWidth :=
  Tools.ShippingPortsMatchRawLeafAny.hkidW_one
    (kidOuts := fun _ => Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.outs) hftByte_instFields
    hftByte_strict
    (by
      intro k hk y hy
      rw [hftByte_entries k hk] at hy
      exact httpGetByte_outTys hR0 hy)

/-! ## The four theorems of the head -/

set_option maxHeartbeats 0 in
/-- **The run's facts of `hftByte`'s full-entry module** (`core_runFactsH`). -/
theorem hftByte_factsH {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``hftByte [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingOneOutFacts.RunFactsH D.modules b :=
  Tools.ShippingOneOutFacts.core_runFactsH (nDecl := hftNDecl) hftByte.machineData
    hftByte.machine_ok hftByte.machine_body hftByte_callsOk hftByte_slotLen hftByte_domB
    hftByte_insts hftByte_instFields hftByte_outTy hftByte_nomem
    hB hcore hpost entry closes hftByte_slots

set_option maxHeartbeats 0 in
/-- **`outsCheck` of `hftByte`'s shipped module at depth 0, from the run**
(`core_outsCheck_all_gate`), under the statement-kind gate. No check
premise. -/
theorem hftByte_outsH {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``hftByte [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := hftNDecl) hftByte.machineData
    hftByte.machine_ok hftByte.machine_body hftByte_callsOk hftByte_slotLen hftByte_domB
    hftByte_insts hftByte_outTy hftByte_nomem
    (by
      intro k hk y hy
      rw [hftByte_entries k hk] at hy
      exact httpGetByte_kidA hR0 hy)
    (by
      intro k hk y hy
      rw [hftByte_entries k hk] at hy
      exact httpGetByte_kidR hR0 hy)
    hB hcore hpost entry closes hg 0

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `hftByte`'s full-entry module, from the run**
(`core_portsMatch_raw₁`). -/
theorem hftByte_portsRaw {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``hftByte [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_portsMatch_raw₁ (nDecl := hftNDecl) hftByte.machineData
    hftByte.machine_ok hftByte.machine_body hftByte_callsOk hftByte_slotLen hftByte_domB
    hftByte_insts hftByte_instFields hftByte_outTy hftByte_nomem
    (hftByte_kidW hR0)
    (by
      intro k hk y hy
      rw [hftByte_entries k hk] at hy
      exact httpGetByte_portsIn hR0 hy)
    (kidIns := hftKidIns) hftByte_callArgs
    (by
      intro k hk y hy j q hq
      rw [hftByte_entries k hk] at hy
      obtain ⟨wd, h1, h2, -⟩ := httpGetByte_inWidths hR0 hy hq
      exact ⟨wd, h1, h2⟩)
    hB hcore hpost entry closes hftByte_outClean hftByte_outScalar

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `hftByte`'s SHIPPED module, from the run.** -/
theorem hftByte_portsShipped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``hftByte [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingPortsMatchShipped.portsMatchB_shipped
    (Tools.ShippingHierGateAny.core_hierGate_any (nDecl := hftNDecl) hftByte.machineData
    hftByte.machine_ok hftByte.machine_body hftByte_callsOk hftByte_slotLen hftByte_domB
      hftByte_insts hftByte_outTy hftByte_nomem
      hB hcore hpost entry closes)
    (hftByte_portsRaw hcore hpost entry closes hB hR0)

set_option maxHeartbeats 0 in
/-- **`hierTyped` of `hftByte`'s full-entry module, from the run**
(`core_hierTyped₁`). No check premise. -/
theorem hftByte_hierTyped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``hftByte [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_hierTyped₁ (nDecl := hftNDecl) hftByte.machineData
    hftByte.machine_ok hftByte.machine_body hftByte_callsOk hftByte_slotLen hftByte_domB
    hftByte_insts hftByte_instFields hftByte_outTy hftByte_nomem
    (hftByte_kidW hR0)
    (by
      intro k hk y hy
      rw [hftByte_entries k hk] at hy
      exact httpGetByte_childTyped hR0 hy)
    (kidIns := hftKidIns) hftByte_callArgs
    (by
      intro k hk y hy j q hq
      rw [hftByte_entries k hk] at hy
      obtain ⟨wd, h1, -, h3⟩ := httpGetByte_inWidths hR0 hy hq
      exact ⟨wd, h1, h3⟩)
    hB hcore hpost entry closes hftByte_outClean hftByte_outScalar

set_option maxHeartbeats 0 in
/-- **`designCheck` of `hftByte`'s shipped module at depth 0, from the run,
with no check premise** (`core_designCheckH` fed with `hftByte_portsShipped`). -/
theorem hftByte_designFull {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``hftByte [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``hftByte
      hftByte.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingOneOutFacts.core_designCheckH (nDecl := hftNDecl) hftByte.machineData
    hftByte.machine_ok hftByte.machine_body hftByte_callsOk hftByte_slotLen hftByte_domB
    hftByte_insts hftByte_instFields hftByte_outTy hftByte_nomem
    hB hcore hpost entry closes hftByte_slots hftByte_outClean hftByte_outScalar
    (by
      intro k hk y hy
      rw [hftByte_entries k hk] at hy
      exact httpGetByte_kidK hR0 hy)
    0 (hftByte_portsShipped hcore hpost entry closes hB hR0)


end Tests.Compiler.OneOutHftByteTest

/-! ## The endpoint, by the existing command -/

set_option maxHeartbeats 0 in
#machine_design_svH_full Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte
  [Tests.Compiler.OneOutHftByteTest.hftByte_factsH,
   Tests.Compiler.OneOutHftByteTest.hftByte_hierTyped,
   Tests.Compiler.OneOutHftByteTest.hftByte_designFull,
   Tests.Compiler.OneOutHftByteTest.hftByte_outsH]

#check @Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full
#check @Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte
  let kid := ``Sparkle.IP.Net.HTTP.httpGetByte
  Tests.Compiler.OneOutLeafAudit.audit "ONEOUT MACHINE-LEAF" f [kid] []
    [``Tests.Compiler.OneOutHftByteTest.hftByte_factsH,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_outsH,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_portsRaw,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_portsShipped,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_hierTyped,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_designFull]
    [``Tests.Compiler.OneOutHftByteTest.hftByte_kidW,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_entries,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_strict,
     ``Tests.Compiler.OneOutHftByteTest.hftByte_callArgs,
     ``Tests.Compiler.OneOutHftByteTest.httpGetByte_leaf,
     ``Tests.Compiler.OneOutHftByteTest.httpGetByte_gate,
     ``Tools.ShippingLeafOneOutGen.gateCallsOk_parts]
    false
    (Tests.Compiler.OneOutLeafAudit.scopeOf f
      "for hftByte at hftNDecl = nIn - insts.length: hftByte_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots (the parent has a register), _outChars, _outScalar, _entries (every entry's callee is httpGetByte), _strict (callWidthsStrict against httpGetByte's layout outputs: the result binder's width), _callArgs (callArgsOk against httpGetByte's declared widths, the domain binder filtered out); for httpGetByte at nIn: httpGetByte_gate (gateCallsOk), _calls, _dom, _ss (its conjuncts), _insts (a leaf), _outTy, _outChars, _outScalar, _lets (lets ≠ 0), _slots (slotless), _one (the one output out), its generated machine_ok / machine_body and its generated closing machine_closes"
      "callerLN (not instantiated in this file)")
