import Sparkle
import Tools.ShippingMachineCommand
import Tools.ShippingMemClosesKidsT
import Tools.ShippingModuleName
import Tools.ShippingGateChildCommand
import Tools.ShippingGateChildIfaceP

/-! # Certificate: the closing of the ORIGINAL memory-name collision parents (gate-route colliding declaration; round par/o-gate)

BUILT (par/o-gate, integrator runs gt1 → gt2; fix: the two hand-written `gate_wf` statements used `Term.WF gateTerm …` — `Term.WF` takes `kb kv vw` first, now `gateTerm.WF …` as `gateTheorem` writes it; gt2 built this file, peak 0.86 GB for the run; axioms of every `*_closes`, `*_iface`, `closes_of_gateCollision`, `*_not_agree`: [propext, Classical.choice, Quot.sound]). CLOSING ONLY (`MachineClosesAt`), not design semantics.

`Tests/Compiler/MemNameCollisionTest.lean` (the original reproducer) checks
that the patched compiler compiles parents with a memory AND a call of a
COMBINATIONAL `@[hardware_module]` (`fakeSrc`, `wd + 1`; `fakeN`, `ra + 1`)
declared (by metaprogramming) under a memory's placeholder name
`MachMemory.memChildName cb 4 8`. `Tests/Compiler/MemNameCollisionCertTest.lean`
certifies the closing only for a LEAF REGISTER colliding declaration
(`fakeReg`); it is NOT coverage of the original (gate-route) case. This file
is: the colliding declarations are copies of the original's `fakeSrc` /
`fakeN`, the parents copies of the original's `mixDiff`, `mixArgs`,
`mixSame`, `width` (verbatim; `copyAs` / `renameIn` as there).

## What is stated (kernel-checked once built)

`MachineClosesAt` (the CLOSING premise of the certified machine route: the
run's `closeLets`/`closeInstsG` returns a module) of each collision parent,
by the ORIGIN-based general closing
`Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT`, with

* the memory entry's child interface from `memKidT_iface` (BUILT);
* the colliding gate declaration's child interface from
  `Tools.ShippingGateChildIfaceP.gateChild_ifaceP_of_real` (NEW, NOT BUILT:
  `ChildFull` of the gate child, BUILT `childFull_of_real`, turned into
  `ChildIfaceP`).

Cases (one theorem each):

* `collMixDiff_closes` — COMBINATIONAL-read memory 4/8 and `fakeSrc` under the
  SYNCHRONOUS name `memChildName false 4 8`, the same argument `let`s;
* `collMixArgs_closes` — synchronous memory 4/8 and `fakeSrc` under its name,
  OTHER arguments (`wa` for `ra`);
* `collMixSame_closes` — synchronous memory 4/8 and `fakeSrc` under its name,
  the SAME argument `let`s (the case the unpatched reader merged);
* `collWidth_closes` — combinational memory 4/8 and `fakeN` (4-bit result)
  under that memory's OWN name `memChildName true 4 8`, the same arguments.

The parents are the original's: each already has registers (a `Signal.loop`
over `bundle2` of two `Signal.register`s). NO register was added. The
general closing (`instFields ≠ []`) is ASSERTED per parent by the first
`run_cmd` and is a premise (`hfne`) decided by the kernel.

## Premises (all explicit; nothing added to `RefLaws` or a trusted list)

Per parent theorem, ONE premise: the reflection of the colliding declaration
at the gate's reading of it,
`Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref <placeholder name> <src>.gateValue`
(`<src>.gateValue` the gate's reading of `fakeSrc` / `fakeN`; that the gate
reads the COLLIDING declaration to the same value is kernel-checked:
`syncGate_value`, `comboGate_value`). Everything else is decided by the
kernel on the reader's data (`…_ok`, `…_body`, `callsOk 3`, slot lengths, no
late domain binder, `instFields ≠ []`, the per-entry origin/name table, the
argument counts, the fields, `hfieldsNd`, output heads, parent ≠ callee) or on
the gate's reading (`fakeSrc.gate_peel` / `gate_old` / `gate_wf`, the
`bool_positions` / `bits_positions` checks; the same statements and proofs
`#gate_child` writes, written here because `#gate_child`'s source definitions
are not needed for the interface). There is NO `MachineDefines` premise: the
gate child's interface needs only `EntryDefines`.

## What is NOT covered

* design semantics, the emitted module text, `#sim`: this is the closing
  `MachineClosesAt` only;
* the original's `plain` case (the colliding declaration ALONE, no memory):
  it is tied by the ONE-output closing `closeInsts`, whose theorem
  `Tools.ShippingCallsGate.machineClosesAt_of_gateKids` asks `hnomem`
  (`memChild? x.1 = none` for every entry) — FALSE for an entry named
  `memChildName false 4 8`; no origin-based one-output closing exists;
* the controls (`mixDiff` … under the declaration's own name): not stated
  here (they are not collisions);
* a first-gate (uniform-width) colliding declaration, a multi-output one.

## Doubtful spots (expected build risks)

* `gateDefs` must accept `fakeSrc`/`fakeN` and their copies (the mixed gate,
  not the first gate) — if not, the `run_cmd` throws with the gate's reason;
* the reader must read the `Signal.loop` parents (`readMachine`), with
  `nDecl = 3` (asserted) and two call entries each (asserted);
* the decided premises are `first | decide | decide +kernel`, as in
  `MemNameCollisionCertTest`. -/
namespace Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The memory's interface, not a memory: `wd + 1` (the original's `fakeSrc`). -/
@[hardware_module]
def fakeSrc (_wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8))
    (_we : Signal defaultDomain Bool) (_ra : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  wd + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

/-- The memory's operands, a 4-bit result: `ra + 1` (the original's `fakeN`). -/
@[hardware_module]
def fakeN (_wa : Signal defaultDomain (BitVec 4)) (_wd : Signal defaultDomain (BitVec 8))
    (_we : Signal defaultDomain Bool) (ra : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  ra + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))

def mixDiff (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

def mixArgs (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memory wa wd we addr
    let r2 := fakeSrc wa wd we wa
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

def mixSame (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memory wa wd we addr
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

def width (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := fakeN wa wd we addr
    bundle2 (Signal.register 0#4 (addr + r2))
      (Signal.register 0#8 r1)
  Signal.snd st

/-- `src` copied under `nm`, tagged `@[hardware_module]` (as `MemNameCollisionTest.copyAs`). -/
def copyAs (src nm : Name) : CoreM Unit := do
  let ci ← getConstInfo src
  addDecl (Declaration.defnDecl (mkDefinitionValEx nm [] ci.type ci.value! .abbrev .safe [nm]))
  Sparkle.Compiler.hardwareModuleAttr.setTag nm

/-- `par` with `src` replaced by `nm`, declared as `out` (as `MemNameCollisionTest.renameIn`). -/
def renameIn (par src nm out : Name) : CoreM Unit := do
  let ci ← getConstInfo par
  let v := ci.value!.replace fun e => if e.isConstOf src then some (.const nm []) else none
  addDecl (Declaration.defnDecl (mkDefinitionValEx out [] ci.type v .abbrev .safe [out]))

/-- The synchronous 4/8 memory's placeholder name. -/
def syncName : Name := Sparkle.Compiler.MachMemory.memChildName false 4 8
/-- The combinational-read 4/8 memory's placeholder name. -/
def comboName : Name := Sparkle.Compiler.MachMemory.memChildName true 4 8

def ns : Name := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest

run_cmd liftCoreM do
  copyAs ``fakeSrc syncName
  copyAs ``fakeN comboName
  renameIn ``mixDiff ``fakeSrc syncName (ns ++ `collMixDiff)
  renameIn ``mixArgs ``fakeSrc syncName (ns ++ `collMixArgs)
  renameIn ``mixSame ``fakeSrc syncName (ns ++ `collMixSame)
  renameIn ``width ``fakeN comboName (ns ++ `collWidth)

/-- `name : stmt` with the proof `Eq.refl lhs`, checked by the kernel only. -/
def addRefl (name : Name) (stx : Lean.Term) : TermElabM Unit := do
  let stmt ← Term.elabTerm stx (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let stmt ← instantiateMVars stmt
  if stmt.hasMVar then throwError "{name}: the statement has metavariables"
  let some (α, lhs, _) := stmt.eq? | throwError "{name}: not an equation: {stmt}"
  let u ← getLevel α
  withOptions (fun o => Lean.Elab.async.set o false) do
    addDecl (.thmDecl (mkTheoremValEx name [] stmt (mkApp2 (mkConst ``Eq.refl [u]) α lhs) [name]))

/-- `name : lhs = rhs` (closed constants, type `α`) with the proof `Eq.refl lhs`,
checked by the kernel only (for constants whose names identifiers cannot spell). -/
def addReflE (name : Name) (α lhs rhs : Lean.Expr) : MetaM Unit := do
  let u ← getLevel α
  let stmt := mkApp3 (mkConst ``Eq [u]) α lhs rhs
  withOptions (fun o => Lean.Elab.async.set o false) do
    addDecl (.thmDecl (mkTheoremValEx name [] stmt (mkApp2 (mkConst ``Eq.refl [u]) α lhs) [name]))

/-- The reader's data of `src`, as `base`. -/
def addData (src base : Name) : TermElabM Unit := do
  let r ← Tools.ShippingMachineCommand.readMachine src
  Tools.ShippingMachineCommand.addDef base (mkConst ``Tools.ShippingMachineAuto.MachineData)
    (← Tools.ShippingMachineCommand.dataE r)

/-! ## The gate's reading of the colliding declarations (as `#gate_child` reads them) -/

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  withOptions (fun o => Lean.Elab.async.set o false) do
    Tools.ShippingGateChildCommand.gateDefs ``fakeSrc
    Tools.ShippingGateChildCommand.gateDefs ``fakeN
    -- the COLLIDING declarations themselves (the gate's checks run on them)
    Tools.ShippingGateChildCommand.gateDefs syncName
    Tools.ShippingGateChildCommand.gateDefs comboName
  -- the colliding declaration is read to the same value as its source
  addReflE (ns ++ `syncGate_value) (mkConst ``Lean.Expr) (mkConst (syncName ++ `gateValue))
    (mkConst (``fakeSrc ++ `gateValue))
  addReflE (ns ++ `comboGate_value) (mkConst ``Lean.Expr) (mkConst (comboName ++ `gateValue))
    (mkConst (``fakeN ++ `gateValue))

/-- The statements and proofs `#gate_child` writes (`gateTheorem`), at `fakeSrc`. -/
theorem fakeSrc.gate_peel : Sparkle.Compiler.Elab.mixedGatePeel fakeSrc.gateValue =
    some (fakeSrc.gateBinders,
      Tools.ShippingUnifiedSource.quote fakeSrc.gateDom
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr fakeSrc.gateBinders.length
          (fakeSrc.gateBpos.getD j 0))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr fakeSrc.gateBinders.length
          (fakeSrc.gateVpos.getD j 0))
        fakeSrc.gateTerm) := by rfl

theorem fakeSrc.gate_old : ∀ d : Lean.DefinitionVal, d.value = fakeSrc.gateValue →
    Sparkle.Compiler.Elab.certifiedShape? false [] (.defnInfo d) = none := by
  intro d hd; simp only [Sparkle.Compiler.Elab.certifiedShape?, hd]; rfl

theorem fakeSrc.gate_wf : fakeSrc.gateTerm.WF fakeSrc.gateBpos.length fakeSrc.gateVpos.length
    (fun j => fakeSrc.gateVw.getD j 0) := by
  delta fakeSrc.gateTerm fakeSrc.gateSort fakeSrc.gateBpos fakeSrc.gateVpos fakeSrc.gateVw
  simp (config := { decide := true }) [Tools.ShippingUnifiedSource.Term.WF]

theorem fakeN.gate_peel : Sparkle.Compiler.Elab.mixedGatePeel fakeN.gateValue =
    some (fakeN.gateBinders,
      Tools.ShippingUnifiedSource.quote fakeN.gateDom
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr fakeN.gateBinders.length
          (fakeN.gateBpos.getD j 0))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr fakeN.gateBinders.length
          (fakeN.gateVpos.getD j 0))
        fakeN.gateTerm) := by rfl

theorem fakeN.gate_old : ∀ d : Lean.DefinitionVal, d.value = fakeN.gateValue →
    Sparkle.Compiler.Elab.certifiedShape? false [] (.defnInfo d) = none := by
  intro d hd; simp only [Sparkle.Compiler.Elab.certifiedShape?, hd]; rfl

theorem fakeN.gate_wf : fakeN.gateTerm.WF fakeN.gateBpos.length fakeN.gateVpos.length
    (fun j => fakeN.gateVw.getD j 0) := by
  delta fakeN.gateTerm fakeN.gateSort fakeN.gateBpos fakeN.gateVpos fakeN.gateVw
  simp (config := { decide := true }) [Tools.ShippingUnifiedSource.Term.WF]

/-! ## The data of the parents: LOGGED, then asserted -/

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  -- (parent, memory read kind, colliding declaration's name, same argument lets)
  let cases : List (Name × Bool × Name × Bool) :=
    [ (ns ++ `collMixDiff, true, syncName, true),
      (ns ++ `collMixArgs, false, syncName, false),
      (ns ++ `collMixSame, false, syncName, true),
      (ns ++ `collWidth, true, comboName, true) ]
  for (p, cb, cName, same) in cases do
    let rf ← Tools.ShippingMachineCommand.readMachine p
    let tagged := rf.shape.instTagged
    let memName := Sparkle.Compiler.MachMemory.memChildName cb 4 8
    Lean.logInfo m!"GATECERT DATA {p}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {rf.shape.insts.map (·.1)}, origins {repr rf.shape.instOrigins}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}"
    unless rf.nDecl == 3 do throwError "{p}: nDecl = {rf.nDecl}, the theorems below are written for 3"
    unless !rf.shape.layout.slots.isEmpty do throwError "{p}: no register"
    unless !rf.shape.instFields.isEmpty do
      throwError "{p}: instFields = [] — the one-output closing, not the general one"
    unless tagged.length == 2 do
      throwError "{p}: {tagged.length} call entries, expected 2 (the memory and the colliding call)"
    unless tagged.any (fun x => x.1 == memName && x.2 == .mem cb 4 8) do
      throwError "{p}: no entry {memName} of origin .mem {cb} 4 8: {repr tagged}"
    unless tagged.any (fun x => x.1 == cName && x.2 == .ord) do
      throwError "{p}: no entry {cName} of origin .ord: {repr tagged}"
    unless tagged.any (fun x => !Tools.ShippingInstTagged.tagAgrees x.1 x.2) do
      throwError "{p}: TagsAgree holds — not a collision shape"
    let nArgLets := (rf.shape.insts.map (·.2.1)).eraseDups.length
    unless nArgLets == (if same then 1 else 2) do
      throwError "{p}: the entries' argument lets {rf.shape.insts.map (·.2.1)}, expected {if same then "equal" else "different"}"
  addData (ns ++ `collMixDiff) (ns ++ `collMixDiffD)
  addData (ns ++ `collMixArgs) (ns ++ `collMixArgsD)
  addData (ns ++ `collMixSame) (ns ++ `collMixSameD)
  addData (ns ++ `collWidth) (ns ++ `collWidthD)

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  addRefl (ns ++ `collMixDiff_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collMixDiffD = true))
  addRefl (ns ++ `collMixDiff_body) (← `(collMixDiffD.shape.body = Tools.ShippingUnifiedSource.quote collMixDiffD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collMixDiffD.shape.binders.length (collMixDiffD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collMixDiffD.shape.binders.length (collMixDiffD.vpos j))
      collMixDiffD.packed))
  addRefl (ns ++ `collMixArgs_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collMixArgsD = true))
  addRefl (ns ++ `collMixArgs_body) (← `(collMixArgsD.shape.body = Tools.ShippingUnifiedSource.quote collMixArgsD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collMixArgsD.shape.binders.length (collMixArgsD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collMixArgsD.shape.binders.length (collMixArgsD.vpos j))
      collMixArgsD.packed))
  addRefl (ns ++ `collMixSame_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collMixSameD = true))
  addRefl (ns ++ `collMixSame_body) (← `(collMixSameD.shape.body = Tools.ShippingUnifiedSource.quote collMixSameD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collMixSameD.shape.binders.length (collMixSameD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collMixSameD.shape.binders.length (collMixSameD.vpos j))
      collMixSameD.packed))
  addRefl (ns ++ `collWidth_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collWidthD = true))
  addRefl (ns ++ `collWidth_body) (← `(collWidthD.shape.body = Tools.ShippingUnifiedSource.quote collWidthD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collWidthD.shape.binders.length (collWidthD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collWidthD.shape.binders.length (collWidthD.vpos j))
      collWidthD.packed))

/-! ## The old (name-based) closing does not apply: `TagsAgree` is false -/

theorem collMixDiff_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collMixDiffD.shape := by
  first | decide | decide +kernel

theorem collMixArgs_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collMixArgsD.shape := by
  first | decide | decide +kernel

theorem collMixSame_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collMixSameD.shape := by
  first | decide | decide +kernel

theorem collWidth_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collWidthD.shape := by
  first | decide | decide +kernel

/-! ## The colliding declarations' children: gate-route, by `gateChild_ifaceP_of_real` -/

open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingInstTagged (KidT originAt)
open Tools.ShippingMemCloses (ChildIfaceP)

/-- `fakeSrc`'s number of argument ports (its non-domain gate binders). -/
noncomputable def fakeSrcNk : Nat :=
  (fakeSrc.gateBinders.filter fun x => x.2 != .domain).length

/-- `fakeN`'s number of argument ports. -/
noncomputable def fakeNNk : Nat :=
  (fakeN.gateBinders.filter fun x => x.2 != .domain).length

/-- **A real child of `fakeSrc` copied under `memChildName false 4 8` has the
general closing's interface** — from that declaration's reflection at the
gate's reading of `fakeSrc` (`syncGate_value`: the same value) and the gate
facts. -/
theorem syncFake_iface {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    {y : Tools.ShippingChildInv.Res} (hy : Tools.ShippingChildInv.RealChild mref cref syncName y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl syncName) fakeSrcNk ["out"] [] y.1 y.2 :=
  Tools.ShippingGateChildIfaceP.gateChild_ifaceP_of_real (bs := fakeSrc.gateBinders) hR0
    fakeSrc.gate_old fakeSrc.gate_peel
    fakeSrc.gate_wf (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy

/-- **A real child of `fakeN` copied under `memChildName true 4 8` has the
interface.** -/
theorem comboFake_iface {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue)
    {y : Tools.ShippingChildInv.Res} (hy : Tools.ShippingChildInv.RealChild mref cref comboName y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl comboName) fakeNNk ["out"] [] y.1 y.2 :=
  Tools.ShippingGateChildIfaceP.gateChild_ifaceP_of_real (bs := fakeN.gateBinders) hR0
    fakeN.gate_old fakeN.gate_peel
    fakeN.gate_wf (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy

/-! ## The per-entry tables, keyed by the entry's ORIGIN -/

/-- The child module's name (`cName`: the colliding declaration). -/
def nameO (cName : Name) : InstOrigin → String
  | .mem cb aw dw => (memModule cb aw dw).1.name
  | .ord => Sparkle.IR.ModuleName.ofDecl cName
  | .field _ => Sparkle.IR.ModuleName.ofDecl cName

/-- The child's number of argument ports (`nG`: the gate child's). -/
def nkO (nG : Nat) : InstOrigin → Nat
  | .mem _ _ _ => 4
  | .ord => nG
  | .field _ => nG

/-- The module names of the child's design. -/
def namesO : InstOrigin → List String
  | .mem cb aw dw => [(memModule cb aw dw).1.name]
  | .ord => []
  | .field _ => []

theorem memName_eq (cb : Bool) (aw dw : Nat) :
    (memModule cb aw dw).1.name = Sparkle.IR.ModuleName.ofMem cb aw dw := rfl

/-- No declaration's module is named as a built memory module. -/
theorem decl_ne_mem (c : Name) (cb : Bool) (aw dw : Nat) :
    Sparkle.IR.ModuleName.ofDecl c ≠ (memModule cb aw dw).1.name :=
  fun e => Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw (e.trans (memName_eq cb aw dw))

theorem decl_notin_mem (c : Name) (cb : Bool) (aw dw : Nat) :
    Sparkle.IR.ModuleName.ofDecl c ∉ [(memModule cb aw dw).1.name] :=
  fun h => decl_ne_mem c cb aw dw (List.mem_singleton.mp h)

/-! ## The closing of a gate-collision parent -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt` of a parent whose call entries are a 4/8 memory (read
kind `cb`) and calls of a GATE declaration `cName`** (whatever its name — a
memory placeholder name included) — by the origin-based closing, from the
gate child's interface (`hiface`). The data conditions are premises here,
decided per parent below. -/
theorem closes_of_gateCollision {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {declName : Name}
    (cb : Bool) (cName : Name) (nG : Nat)
    (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (hent : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (originAt d.shape k = .mem cb 4 8 ∧
          (d.shape.insts[k]).1 = Sparkle.Compiler.MachMemory.memChildName cb 4 8) ∨
        (originAt d.shape k = .ord ∧ (d.shape.insts[k]).1 = cName))
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nkO nG (originAt d.shape k) = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ (["out"] : List String))
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      Tools.ShippingMemCloses.memKey (originAt d.shape k) =
        Tools.ShippingMemCloses.memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (houtHead : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i')
    (hpar : Sparkle.IR.ModuleName.ofDecl cName ≠ Sparkle.IR.ModuleName.ofDecl declName)
    (hiface : ∀ y : Tools.ShippingChildInv.Res, Tools.ShippingChildInv.RealChild mref cref cName y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl cName) nG ["out"] [] y.1 y.2) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName d.shape := by
  have hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      KidT mref cref (originAt d.shape k) (d.shape.insts[k]).1 y →
      ChildIfaceP (nameO cName (originAt d.shape k)) (nkO nG (originAt d.shape k))
        (["out"] : List String) (namesO (originAt d.shape k)) y.1 y.2 := by
    intro k hk y hy
    rcases hent k hk with ⟨ho, _⟩ | ⟨ho, hn⟩
    · rw [ho] at hy ⊢
      exact Tools.ShippingMemCloses.memKidT_iface (Tools.ShippingInstTagged.child?_mem cb 4 8) hy
    · rw [ho] at hy ⊢
      have hre := Tools.ShippingInstTagged.KidT.real hy rfl
      rw [hn] at hre
      exact hiface y hre
  have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      nameO cName (originAt d.shape k) = nameO cName (originAt d.shape k') →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (originAt d.shape k) =
          Tools.ShippingMemCloses.memKey (originAt d.shape k') := by
    intro k hk k' hk' he
    rcases hent k hk with ⟨ho, hn⟩ | ⟨ho, hn⟩ <;>
      rcases hent k' hk' with ⟨ho', hn'⟩ | ⟨ho', hn'⟩
    · exact ⟨hn.trans hn'.symm, by rw [ho, ho']⟩
    · rw [ho, ho'] at he
      exact absurd he.symm (decl_ne_mem cName cb 4 8)
    · rw [ho, ho'] at he
      exact absurd he (decl_ne_mem cName cb 4 8)
    · exact ⟨hn.trans hn'.symm, by rw [ho, ho']⟩
  have hparent : ∀ (k : Nat), k < d.shape.insts.length →
      nameO cName (originAt d.shape k) ≠ Sparkle.IR.ModuleName.ofDecl declName := by
    intro k hk
    rcases hent k hk with ⟨ho, _⟩ | ⟨ho, _⟩
    · rw [ho]
      exact fun e => decl_ne_mem declName cb 4 8 e.symm
    · rw [ho]
      exact hpar
  have hparentD : ∀ (k : Nat), k < d.shape.insts.length →
      Sparkle.IR.ModuleName.ofDecl declName ∉ namesO (originAt d.shape k) := by
    intro k hk
    rcases hent k hk with ⟨ho, _⟩ | ⟨ho, _⟩
    · rw [ho]
      exact decl_notin_mem declName cb 4 8
    · rw [ho]
      show Sparkle.IR.ModuleName.ofDecl declName ∉ ([] : List String)
      exact fun hx => nomatch hx
  have hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (originAt d.shape k) =
          Tools.ShippingMemCloses.memKey (originAt d.shape k')) →
      nameO cName (originAt d.shape k) ∉ namesO (originAt d.shape k') ∧
        ∀ x ∈ namesO (originAt d.shape k), x ∉ namesO (originAt d.shape k') := by
    intro k hk k' hk' hne
    rcases hent k hk with ⟨ho, hn⟩ | ⟨ho, hn⟩ <;>
      rcases hent k' hk' with ⟨ho', hn'⟩ | ⟨ho', hn'⟩
    · exact (hne ⟨hn.trans hn'.symm, by rw [ho, ho']⟩).elim
    · rw [ho, ho']
      show (memModule cb 4 8).1.name ∉ ([] : List String) ∧
        ∀ x ∈ [(memModule cb 4 8).1.name], x ∉ ([] : List String)
      exact ⟨fun hx => (nomatch hx), fun _ _ hx => nomatch hx⟩
    · rw [ho, ho']
      show Sparkle.IR.ModuleName.ofDecl cName ∉ [(memModule cb 4 8).1.name] ∧
        ∀ x ∈ ([] : List String), x ∉ [(memModule cb 4 8).1.name]
      exact ⟨decl_notin_mem cName cb 4 8, fun _ hx => nomatch hx⟩
    · exact (hne ⟨hn.trans hn'.symm, by rw [ho, ho']⟩).elim
  intro tenv
  exact Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT d ok hbody halias hC hslots hdomB hfne
    (fun k => nameO cName (originAt d.shape k)) (fun k => nkO nG (originAt d.shape k))
    (fun _ => (["out"] : List String)) (fun k => namesO (originAt d.shape k))
    hkid hargsN hfieldOut hfieldsNd hsep hparent
    (fun gi _ _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (houtHead o ho) gi _)
    hparentD hdisjD

/-! ## The four collision parents of the original reproducer -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collMixDiff`**: a COMBINATIONAL-read 4/8 memory and the
call of `fakeSrc` declared under the SYNCHRONOUS placeholder name, the same
argument `let`s; from that declaration's reflection only; no `TagsAgree`
(false: `collMixDiff_not_agree`). -/
theorem collMixDiff_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixDiff collMixDiffD.shape :=
  closes_of_gateCollision (declName := ``collMixDiff) (nDecl := 3) true syncName fakeSrcNk
    collMixDiffD collMixDiff_ok collMixDiff_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
    (fun _ hy => syncFake_iface hR0 hy)

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collMixArgs`**: a synchronous 4/8 memory and the
colliding `fakeSrc` call on OTHER argument `let`s. -/
theorem collMixArgs_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixArgs collMixArgsD.shape :=
  closes_of_gateCollision (declName := ``collMixArgs) (nDecl := 3) false syncName fakeSrcNk
    collMixArgsD collMixArgs_ok collMixArgs_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
    (fun _ hy => syncFake_iface hR0 hy)

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collMixSame`**: a synchronous 4/8 memory and the
colliding `fakeSrc` call on the SAME argument `let`s — two calls (origins
`.mem false 4 8` / `.ord`), the case the unpatched reader merged. -/
theorem collMixSame_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixSame collMixSameD.shape :=
  closes_of_gateCollision (declName := ``collMixSame) (nDecl := 3) false syncName fakeSrcNk
    collMixSameD collMixSame_ok collMixSame_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
    (fun _ hy => syncFake_iface hR0 hy)

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collWidth`**: a combinational-read 4/8 memory and the
call of `fakeN` (4-bit result) declared under that memory's OWN placeholder
name, the same arguments. -/
theorem collWidth_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collWidth collWidthD.shape :=
  closes_of_gateCollision (declName := ``collWidth) (nDecl := 3) true comboName fakeNNk
    collWidthD collWidth_ok collWidth_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
    (fun _ hy => comboFake_iface hR0 hy)

#print axioms Tools.ShippingGateChildIfaceP.gateChild_ifaceP_of_real
#print axioms Tools.ShippingGateChildIfaceP.gateKidT_iface
#print axioms syncFake_iface
#print axioms comboFake_iface
#print axioms closes_of_gateCollision
#print axioms collMixDiff_closes
#print axioms collMixArgs_closes
#print axioms collMixSame_closes
#print axioms collWidth_closes
#print axioms collMixSame_not_agree

end Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
