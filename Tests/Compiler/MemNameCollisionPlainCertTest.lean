import Sparkle
import Tools.ShippingMachineCommand
import Tools.ShippingCallsGate
import Tools.ShippingInstTagged
import Tools.ShippingModuleName
import Tests.Compiler.MemNameCollisionTest
import Tests.Compiler.MemNameCollisionGateCertTest

/-! # Certificate: the ONE-output machine closing of a memory-name collision parent (no memory, by origin)

NOT BUILT as reworked (round par/o-plain; build pc1 built the `Tools` change
— `machineClosesAt_of_gateKidsO`, the corollary, its consumers; axioms
[propext, Classical.choice, Quot.sound] — and showed that the original
`plain` is NOT a machine shape). CLOSING ONLY (`MachineClosesAt`), not design
semantics.

## The original `plain` is on the LEGACY route (NOT covered)

`Tests/Compiler/MemNameCollisionTest.lean`'s case `plain` (a `Signal.loop`
parent, one call of the combinational `fakeSrc` declared under the synchronous
memory's placeholder name `MachMemory.memChildName false 4 8`, no memory) is
not read by `machineShape?` — neither the collision copy `collPlain` nor the
control `plain` (integrator probes pp1/pp2: a `Signal.loop` parent with gate
calls and no memory is not a machine shape; only a memory makes it one). It
is compiled by the legacy route, so no `MachineClosesAt` statement about it
is meaningful. ASSERTED here (`machineShape?` is `none` for both, at the
entry constant the reader uses), not certified.

## What is certified instead

`plainCD`: the same call (`fakeSrc wa (acc ^^^ wd) we addr`) in a
`circuit do` with two registers — the form of the one-output callers
`Tests/Compiler/ShippingMachineInstTest.lean` (`caller`) that
`#machine_closes_at` closes — and `collPlainCD`, the same with `fakeSrc`
replaced by the colliding declaration `SparkleMem.sync.4.8` (a copy of
`fakeSrc`, origin `.ord`). Asserted: both are machine shapes with
`instFields = []` (the one-output closing `closeInstsM`); `collPlainCD` has one
call entry, `syncName` of origin `.ord`, with `tagAgrees` false; and the
certified front end compiles `collPlainCD` to a top with exactly one instance,
of `ofDecl syncName`, no memory module (so the closing's route is the emitted
text's).

`Tools.ShippingCallsGate.machineClosesAt_of_gateKids` asked
`hnomem : ∀ x ∈ instTagged, x.2.child?.isNone ∧ (memChild? x.1).isNone` —
the NAME half is FALSE here (`collPlainCD_nomem_false`). Its proof used only
the ORIGIN half (`nomem_tag` reads `.1`; `closeInstsM` compiles every callee by
its declaration name), so it is now the corollary of
`machineClosesAt_of_gateKidsO`, whose tag premise is the origin half only
(`hnomemO`). This file applies the `O` form:

`collPlainCD_closes : MachineClosesAt … ``collPlainCD collPlainCD_D.shape`, ONE
premise: `EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue` (that
the gate reads the colliding declaration to the same value as `fakeSrc` is
kernel-checked: `syncGate_value`). Everything else is decided by the kernel on
the reader's data or on the gate's reading of `fakeSrc`. No `TagsAgree` (false:
`collPlainCD_not_agree`), no `MachineDefines`.

## Doubtful spots (expected build risks)

* the decided premises are `first | decide | decide +kernel`;
* NOTHING global is redeclared here: the colliding declaration
  `SparkleMem.sync.4.8` (from `MemNameCollisionTest`), its `gate*` constants,
  `fakeSrc` / `fakeSrc.gate_peel` / `gate_old` / `gate_wf` / `fakeSrcNk`,
  `syncGate_value` and the helpers `renameIn` / `addData` / `addRefl` are
  `MemNameCollisionGateCertTest`'s (imported; `fakeSrc` below is that file's,
  the `EntryDefines` premise is at its `fakeSrc.gateValue`). This file's own
  constants (`plainCD`, `collPlainCD`, `collPlainCD_*`, `nsP`, `compileCert`)
  are in its namespace. -/
namespace Sparkle.Tests.Compiler.MemNameCollisionPlainCertTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

-- reused from `MemNameCollisionGateCertTest` (NOT redeclared here: the colliding
-- declaration `SparkleMem.sync.4.8`, its `gate*` constants, `fakeSrc.gate_*`,
-- `syncGate_value` live there / in `MemNameCollisionTest`)
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  (fakeSrc syncName renameIn addData addRefl fakeSrcNk)

/-- The same call in the one-output callers' form (`circuit do`, two
registers; `ShippingMachineInstTest.caller`): a machine shape. -/
def plainCD (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let addr ← Signal.reg 0#4
    let acc ← Signal.reg 0#8
    let addrS := (addr : Signal defaultDomain (BitVec 4))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let r2 := fakeSrc wa (accS ^^^ wd) we addrS
    addr <~ addrS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))
    acc <~ r2
    return r2

/-- This file's namespace (its own constants). -/
def nsP : Name := `Sparkle.Tests.Compiler.MemNameCollisionPlainCertTest

run_cmd liftCoreM do
  renameIn ``plainCD ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc syncName (nsP ++ `collPlainCD)

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let env ← getEnv
  let senv := Sparkle.Compiler.Elab.structEnv env
  for p in [`Sparkle.Tests.Compiler.MemNameCollisionTest.plain,
      `Sparkle.Tests.Compiler.MemNameCollisionTest.collPlain] do
    let ci ← getConstInfo p
    let entry := Sparkle.Compiler.Elab.entryConst true false [] ci
      (Sparkle.Compiler.Elab.instancePredicate env) (Sparkle.Compiler.Elab.userInliner env) senv
    unless (Sparkle.Compiler.Elab.machineShape? false [] entry senv).isNone do
      throwError "{p}: now a machine shape — the legacy-route note of this file is stale"
    Lean.logInfo m!"PLAINCERT LEGACY {p}: machineShape? = none (legacy route; NOT covered by a MachineClosesAt certificate)"

/-! ## The data of the parents: LOGGED, then asserted -/

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  -- the control: the form is on the one-output machine route
  let rc ← Tools.ShippingMachineCommand.readMachine ``plainCD
  unless rc.shape.instFields.isEmpty do
    throwError "plainCD: instFields ≠ [] — the general closing, not the one-output one"
  unless rc.shape.insts.length == 1 do
    throwError "plainCD: {rc.shape.insts.length} call entries, expected 1"
  let p := nsP ++ `collPlainCD
  let rf ← Tools.ShippingMachineCommand.readMachine p
  let tagged := rf.shape.instTagged
  Lean.logInfo m!"PLAINCERT DATA {p}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {rf.shape.insts.map (·.1)}, origins {repr rf.shape.instOrigins}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}"
  unless rf.nDecl == 3 do throwError "{p}: nDecl = {rf.nDecl}, the theorem below is written for 3"
  unless !rf.shape.layout.slots.isEmpty do throwError "{p}: no register"
  unless rf.shape.instFields.isEmpty do
    throwError "{p}: instFields ≠ [] — the general closing, not the one-output one"
  unless tagged.length == 1 do
    throwError "{p}: {tagged.length} call entries, expected 1 (the colliding call)"
  unless tagged.all (fun x => x.1 == syncName && x.2 == .ord) do
    throwError "{p}: the entry is not {syncName} of origin .ord: {repr tagged}"
  unless tagged.any (fun x => !Tools.ShippingInstTagged.tagAgrees x.1 x.2) do
    throwError "{p}: TagsAgree holds — not a collision shape"
  addData p (nsP ++ `collPlainCD_D)

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  addRefl (nsP ++ `collPlainCD_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collPlainCD_D = true))
  addRefl (nsP ++ `collPlainCD_body) (← `(collPlainCD_D.shape.body = Tools.ShippingUnifiedSource.quote collPlainCD_D.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collPlainCD_D.shape.binders.length (collPlainCD_D.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collPlainCD_D.shape.binders.length (collPlainCD_D.vpos j))
      collPlainCD_D.packed))

/-! ## The emitted text: one instance of the colliding declaration, no memory -/

/-- The certified route's top module and design (as `MemNameCollisionTest.compileCert`). -/
def compileCert (n : Name) : TermElabM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith
    (fun env e h t n => Sparkle.Compiler.Elab.translateExprToWire env e h t n) n [] false
    (certifiedFrontEnd := true)

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  for (n, c) in [(``plainCD, ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc), (nsP ++ `collPlainCD, syncName)] do
    let (top, D) ← compileCert n
    let insts := top.body.filterMap fun s => match s with | .inst mn _ _ => some mn | _ => none
    let mn := Sparkle.IR.ModuleName.ofDecl c
    unless insts == [mn] do
      throwError "{n}: instances {insts}, expected exactly one of {c} ({mn})"
    let (alone, _) ← compileCert c
    match D.modules.find? (·.name == mn) with
    | some m =>
      if m.body.length != alone.body.length || m.outputs.map (·.ty) != alone.outputs.map (·.ty) ||
          m.inputs.map (·.name) != alone.inputs.map (·.name) then
        throwError "{n}: the child {mn} is not {c} compiled alone"
    | none => throwError "{n}: no module {mn} for {c}"
    if D.modules.any (fun m => (Sparkle.Compiler.MachMemory.memParams? m).isSome) then
      throwError "{n}: the design has a memory module"
    if top.body.any (fun s => match s with | .memory .. => true | _ => false) then
      throwError "{n}: the top has a memory statement"
    Lean.logInfo m!"PLAINCERT TEXT {n}: one instance of {mn}, no memory"

/-! ## The old (name-based) premises do not hold -/

/-- The NAME half of the old `hnomem` is false: the entry is named as a memory. -/
theorem collPlainCD_nomem_false : ¬ (∀ x ∈ collPlainCD_D.shape.instTagged, x.2.child?.isNone = true ∧
    (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true) := by
  first | decide | decide +kernel

theorem collPlainCD_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collPlainCD_D.shape := by
  first | decide | decide +kernel

/-! ## The closing, by origin -/

/-- The callee of every call entry of `collPlainCD` is the colliding declaration. -/
theorem collPlainCD_callee : ∀ c ∈ collPlainCD_D.shape.insts.map (·.1), c = syncName := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collPlainCD`**: one call of `fakeSrc` declared under the
SYNCHRONOUS memory placeholder name (origin `.ord`), no memory — by the
ORIGIN-based one-output closing `machineClosesAt_of_gateKidsO`; from that
declaration's reflection only; no `TagsAgree` (false: `collPlainCD_not_agree`),
no name half of `hnomem` (false: `collPlainCD_nomem_false`). -/
theorem collPlainCD_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collPlainCD collPlainCD_D.shape :=
  Tools.ShippingCallsGate.machineClosesAt_of_gateKidsO (nDecl := 3) collPlainCD_D
    collPlainCD_ok collPlainCD_body
    (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun _ => fakeSrcNk)
    (by first | decide | decide +kernel)
    (by
      intro k hk y hy
      have hn : (collPlainCD_D.shape.insts[k]).1 = syncName :=
        collPlainCD_callee _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)
      rw [hn] at hy ⊢
      exact Tools.ShippingCallsGate.ChildFull.iface
        (Tools.ShippingCallsGate.childFull_of_real hR0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_old Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_peel
          Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_wf (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)) hy))
    (by first | decide | decide +kernel)
    (fun c hc c' hc' _ => (collPlainCD_callee c hc).trans (collPlainCD_callee c' hc').symm)
    (fun c hc => by
      have h1 : c.1 = syncName := collPlainCD_callee _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
      rw [h1]
      exact Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ collPlainCD_D.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) k _)

/-! ## Audit: standard axioms; no `TagsAgree`, no memory-name condition; the `O` closing -/

run_cmd liftTermElabM do
  for n in [``collPlainCD_closes, ``Tools.ShippingCallsGate.machineClosesAt_of_gateKidsO,
      ``Tools.ShippingCallsGate.machineClosesAt_of_gateKids, ``collPlainCD_nomem_false,
      ``collPlainCD_not_agree] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  let some (.thmInfo ti) := (← getEnv).find? ``collPlainCD_closes
    | throwError "collPlainCD_closes is not a theorem"
  let stmtUsed := ti.type.getUsedConstants
  if stmtUsed.contains ``Tools.ShippingInstTagged.TagsAgree then
    throwError "collPlainCD_closes: the statement mentions TagsAgree"
  if stmtUsed.contains ``Sparkle.Compiler.MachMemory.memChild? then
    throwError "collPlainCD_closes: the statement mentions memChild?"
  -- the four contexts (`mctx mref cctx cref`) and the ONE premise `hR0`
  unless ti.type.getForallBinderNames.length == 5 do
    throwError "collPlainCD_closes: expected the contexts and the one premise hR0: {ti.type.getForallBinderNames}"
  let used := ti.value.getUsedConstants
  unless used.contains ``Tools.ShippingCallsGate.machineClosesAt_of_gateKidsO do
    throwError "collPlainCD_closes: its proof does not apply machineClosesAt_of_gateKidsO"
  if used.contains ``Tools.ShippingCallsGate.machineClosesAt_of_gateKids then
    throwError "collPlainCD_closes: its proof applies the theorem WITH the name half of hnomem"
  if used.contains ``Tools.ShippingInstTagged.TagsAgree then
    throwError "collPlainCD_closes: its proof mentions TagsAgree"

#print axioms Tools.ShippingCallsGate.machineClosesAt_of_gateKidsO
#print axioms collPlainCD_closes

end Sparkle.Tests.Compiler.MemNameCollisionPlainCertTest
