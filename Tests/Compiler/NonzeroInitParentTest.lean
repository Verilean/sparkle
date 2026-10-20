import Tests.Compiler.MemNameCollisionSatSTest
-- BUILT by the integrator: ni1 exit 1 (`collMixSame5_entry` lost its proof line in the copy; `addSat` is root-level, not namespaced), ni2 exit 0 (676 jobs; audit passed, axioms standard; slot inits [5, 7]) (round par/nz, base 2d98c233).
-- TARGET-ONLY; not registered in Tests.AllTests (integrator decides).
-- Writing-time guesses:
--   (n1) `renameIn ``mixSame5 ``fakeSrc syncName …` resolves `fakeSrc` / `syncName` / `renameIn`
--        to `MemNameCollisionGateCertTest`'s (opened); the colliding declaration `syncName` is the
--        GLOBAL constant `MemNameCollisionTest` declares (not re-created here);
--   (n2) the reader / `#machine_endpoint` / `#machine_composedTRG` / `#machine_design_svRG0`
--        accept the nonzero register inits `5#4` / `7#8` exactly as `0#4` / `0#8` (the
--        compiler's register init is data; nothing in the chain is known to require 0);
--   (n3) `collMixSame5_closesR` applies `closes_of_gateCollision` directly at the endpoint's
--        `collMixSame5.machineData` / `machine_ok` / `machine_body` (the collision parents go
--        through a separate `addData` constant `collMixSameD` and then restate; same data);
--   (n4) every per-parent lemma below is the `collMixSame` one with the name changed (proofs
--        identical, all `decide` on the data); the data shape (nDecl = 3, two entries, one
--        `SparkleMem.sync.4.8`/.mem false 4 8 and one `.ord`) is asserted by the run_cmd below;
--   (n5) `hinitW` by `decide` (inits 5 < 2^4, 7 < 2^8).

/-! # One NONZERO-init instance parent end to end on the TBS route (round par/nz)

`collMixSame5` is `collMixSame` (`MemNameCollisionGateCertTest`) with the register inits
`5#4` / `7#8` in place of `0#4` / `0#8`: a register loop, a synchronous 4/8 memory, and a call of
`fakeSrc` declared under the memory's placeholder name `SparkleMem.sync.4.8` (the collision).
Route: HAND-WRITTEN per-parent run lemmas (copied from the `collMixSame` chain with the name
changed), `generateTopW` with the head `machine_design_noPortsTBS` (`collMixSame5_designClosedBS`),
then `Tools.ShippingSatAssemblyS.sat_of_designClosedBS` (`collMixSame5_satS`). The certificate
route (`satOfCert`) is NOT used here (it fixes inits 0).

`collMixSame5_initNZ` (kernel `decide`) asserts that the reader's slots carry a nonzero reset
value, so the test exercises the nonzero start state `stOf b regs slots`.

Premises of `collMixSame5_satS` (as for `collMixSame_satS`): the full-entry run `hr`,
`MachineDefines collMixSame5`, the gate child's reflection `EntryDefines syncName
fakeSrc.gateValue`, `ChildBnd`. -/

namespace Sparkle.Tests.Compiler.NonzeroInitParentTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingInstTagged (KidT originAt)
open Tools.ShippingMemKid (KidFactsTC memOuts memIns gateOuts gateIns)

/-- `mixSame` with NONZERO register inits (`5#4`, `7#8`). -/
def mixSame5 (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memory wa wd we addr
    let r2 := fakeSrc wa wd we addr
    bundle2 (Signal.register 5#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 7#8 (r1 ^^^ r2))
  Signal.snd st

def ns5 : Name := `Sparkle.Tests.Compiler.NonzeroInitParentTest

-- (writing-time guess n1) the colliding declaration `syncName` exists already (global, from
-- `MemNameCollisionTest`); only the parent is created here.
run_cmd liftCoreM do
  renameIn ``mixSame5 ``fakeSrc syncName (ns5 ++ `collMixSame5)

/-! ## The data: LOGGED, then asserted (shape as `collMixSame`'s, inits nonzero) -/

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let p := ns5 ++ `collMixSame5
  let rf ← Tools.ShippingMachineCommand.readMachine p
  let tagged := rf.shape.instTagged
  let inits := rf.shape.layout.slots.map (·.init)
  Lean.logInfo m!"NZ DATA {p}: nDecl={rf.nDecl}, call entries {rf.shape.insts.map (·.1)}, origins {repr rf.shape.instOrigins}, slots={rf.shape.layout.slots.length}, inits={inits}, widths={rf.shape.layout.slots.map (·.width)}"
  unless rf.nDecl == 3 do throwError "{p}: nDecl = {rf.nDecl}, expected 3"
  unless !rf.shape.instFields.isEmpty do throwError "{p}: instFields = []"
  unless tagged.length == 2 do throwError "{p}: {tagged.length} call entries, expected 2"
  unless tagged.any (fun x => x.1 == syncName && x.2 == .mem false 4 8) do
    throwError "{p}: no memory entry: {repr tagged}"
  unless tagged.any (fun x => x.1 == syncName && x.2 == .ord) do
    throwError "{p}: no colliding .ord entry: {repr tagged}"
  unless inits.any (· != 0) do throwError "{p}: every slot init is 0: {inits}"
  unless inits.contains 5 && inits.contains 7 do throwError "{p}: inits {inits}, expected 5 and 7"

/-! ## The endpoints (generator; the kernel checks the results) -/

#machine_endpoint collMixSame5

#machine_composedTRG collMixSame5

#machine_design_svRG0 collMixSame5

/-- **The test exercises a nonzero start state**: some slot of the endpoint's data has a nonzero
reset value (kernel-decided on `collMixSame5.machineData`). -/
theorem collMixSame5_initNZ :
    ((collMixSame5.machineData).shape.layout.slots.map (·.init)).any (· != 0) = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collMixSame5`** at the endpoint's data (`closes_of_gateCollision`, as
`collMixSame_closes`). (writing-time guess n3) -/
theorem collMixSame5_closesR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape :=
  closes_of_gateCollision (declName := ``collMixSame5) (nDecl := 3) false syncName fakeSrcNk
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel))
    (fun _ hy => syncFake_iface hR0 hy)

/-! ## The per-parent run lemmas (the `collMixSame` ones, name changed; writing-time guess n4) -/

/-- Every entry is named `SparkleMem.sync.4.8`, of origin the memory or `.ord` (decided). -/
theorem collMixSame5_entry : ∀ (k : Nat) (hk : k < (collMixSame5.machineData).shape.insts.length),
    ((collMixSame5.machineData).shape.insts[k]).1 = syncName ∧
      (originAt (collMixSame5.machineData).shape k = .mem false 4 8 ∨
        originAt (collMixSame5.machineData).shape k = .ord) := by
  first | decide | decide +kernel

/-- **`KidFactsTC` of every call entry of `collMixSame5`, by ORIGIN**, at depth 0: the memory
origin by `memKidT_facts`, the `.ord` entry (named as the memory!) by `gateKidT_factsC` at
`fakeSrc`'s gate reading, through the colliding declaration's reflection `hR0`. -/
theorem collMixSame5_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixSame5.machineData).shape.insts.length),
      KidFactsTC mref cref (originAt (collMixSame5.machineData).shape k)
        ((collMixSame5.machineData).shape.insts[k]).1
        (outsG (originAt (collMixSame5.machineData).shape k))
        (insG (originAt (collMixSame5.machineData).shape k)) 0 := by
  intro k hk
  obtain ⟨hn, ho⟩ := collMixSame5_entry k hk
  rcases ho with ho | ho
  · rw [ho]
    exact (Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem false 4 8)).toC
  · rw [ho, hn]
    exact Tools.ShippingMemKid.gateKidT_factsC (o := InstOrigin.ord) (c := syncName)
      (bs := fakeSrc.gateBinders) rfl hR0
      fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width 0

theorem collMixSame5_callWidths : Tools.ShippingCallWidths.callWidthsOk collMixSame5.machineData 3
    (fun k => outsG (originAt (collMixSame5.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixSame5_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk collMixSame5.machineData 3
    (fun k => insG (originAt (collMixSame5.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixSame5_outChars :
    ∀ o ∈ (collMixSame5.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `collMixSame5`'s full-entry module** (`kidsC_runFactsT`); the closing
from `hR0`. -/
theorem collMixSame5_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemKid.kidsC_runFactsT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame5.machineData).shape k))
    (fun k => insG (originAt (collMixSame5.machineData).shape k)) 0
    (collMixSame5_kids hR0) collMixSame5_callWidths
    hB hcore hpost entry (collMixSame5_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 0 under the statement-kind gate** (`kidsC_outsCheckT`). -/
theorem collMixSame5_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_outsCheckT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame5.machineData).shape k))
    (fun k => insG (originAt (collMixSame5.machineData).shape k)) 0
    (collMixSame5_kids hR0)
    hB hcore hpost entry (collMixSame5_closesR hR0) hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsC_designCheckT`). -/
theorem collMixSame5_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_designCheckT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame5.machineData).shape k))
    (fun k => insG (originAt (collMixSame5.machineData).shape k)) 0
    (collMixSame5_kids hR0) collMixSame5_callWidths collMixSame5_callArgs
    hB hcore hpost entry (collMixSame5_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame5_outChars o ho))
    (by first | decide | decide +kernel)

/-- Per kid, by origin: the memory entry is `FlatOk`, the `.ord` entry (the gate child) is
`KidTyped`. -/
theorem collMixSame5_kidTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixSame5.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixSame5.machineData).shape k)
        ((collMixSame5.machineData).shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  intro k hk y hy
  obtain ⟨hn, ho⟩ := collMixSame5_entry k hk
  rcases ho with ho | ho
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem false 4 8)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (Tools.ShippingKidsTyped.kidTyped_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl)))

set_option maxHeartbeats 4000000 in
/-- **The typed children bound of `collMixSame5`'s full-entry module** (`core_typedRunMT`), from
the core run, the reflection `hR0` and the boundary. -/
theorem collMixSame5_typedRun {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsTyped.TypedRun (Tools.ShippingMachineLinked.childMap D.modules) b
      Tools.ShippingMachineShipsHier.mixInv :=
  Tools.ShippingKidsTyped.core_typedRunMT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixSame5.machineData).shape k))
    (fun k => insG (originAt (collMixSame5.machineData).shape k)) 0
    (collMixSame5_kids hR0) collMixSame5_callArgs (collMixSame5_kidTyped hR0)
    hB hcore hpost entry (collMixSame5_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame5_outChars o ho))
    (by first | decide | decide +kernel)

set_option maxHeartbeats 4000000 in
/-- **The name facts of `collMixSame5`'s full-entry module, from the core run** (`wireNames_runMT`). -/
theorem collMixSame5_names {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  Tools.ShippingWireNamesRun.wireNames_runMT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixSame5_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame5_outChars o ho))
    (by first | decide | decide +kernel)

set_option maxHeartbeats 4000000 in
/-- `hierGate` of `collMixSame5`'s full-entry module, from the core run (`core_hierGateMT`). -/
theorem collMixSame5_gate {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Sparkle.IR.RefineCheck.hierGate b = true :=
  Tools.ShippingMemKid.core_hierGateMT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    hB hcore hpost entry (collMixSame5_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- No input of `collMixSame5`'s full-entry module has an output's (sanitized) name (`TypedIn.oi`). -/
theorem collMixSame5_oi {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name :=
  (Tools.ShippingMemKid.core_closed_typedInMT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixSame5_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame5_outChars o ho))
    (by first | decide | decide +kernel)).oi

set_option maxHeartbeats 4000000 in
/-- The inputs of `collMixSame5`'s full-entry module (not `clk` / `rst`, positive width) are wires
(`inputWires_runMT`). -/
theorem collMixSame5_inputWires {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires :=
  Tools.ShippingInputWiresRun.inputWires_runMT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixSame5_closesR hR0)

/-- Per kid, by origin: the memory entry is the built memory module, the `.ord` entry a gate
child; neither has a register statement. -/
theorem collMixSame5_kidNoRegs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixSame5.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixSame5.machineData).shape k)
        ((collMixSame5.machineData).shape.insts[k]).1 y →
      Tools.ShippingKidsResetSat.NoRegs y.1 := by
  intro k hk y hy
  obtain ⟨hn, ho⟩ := collMixSame5_entry k hk
  rcases ho with ho | ho
  · rw [ho] at hy
    rw [Tools.ShippingInstTagged.KidT.mem hy (Tools.ShippingInstTagged.child?_mem false 4 8)]
    exact Tools.ShippingKidsResetSat.memModule_noRegs false 4 8
  · rw [ho, hn] at hy
    exact Tools.ShippingKidsResetSat.noRegs_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl))

set_option maxHeartbeats 4000000 in
/-- **`collMixSame5`: the head's `Reset1` and depth-0 children bound hold together** for one explicit
`kids` (`kidsZero`), from the core run (any `raw` `D` it returns) and the outer premises. -/
theorem collMixSame5_kidsSat {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame5 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame5
      (collMixSame5.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∃ kids : String → Tools.ShippingHierStateG.KT 0,
      Tools.ShippingMachineShipsHier.Reset1 raw D kids ∧
      ∀ mn iname conns gc gcwe,
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
        Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) →
        Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) 0 gc
          (kids iname) :=
  Tools.ShippingKidsResetSat.core_kidsSatMT (nDecl := 3)
    collMixSame5.machineData collMixSame5.machine_ok collMixSame5.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (collMixSame5_kidNoRegs hR0) hB hcore hpost entry (collMixSame5_closesR hR0)

/-! ## The TBS-headed endpoint, by the generator (as `MemNameCollisionSatSTest`) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let gn := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let me := `Sparkle.Tests.Compiler.NonzeroInitParentTest
  let p := `collMixSame5
  let n ← Tools.ShippingGateTypedCommandW.generateTopW
    { parent := me ++ p, name := me ++ p.appendAfter "_designClosedBS",
      childConst := gn ++ `syncName, gateValue := gn ++ `fakeSrc ++ `gateValue,
      valueEq? := some (gn ++ `syncGate_value),
      runFacts := me ++ p.appendAfter "_runFacts", outsG0 := me ++ p.appendAfter "_outsG0",
      typedRun := me ++ p.appendAfter "_typedRun", designP0 := me ++ p.appendAfter "_designP0",
      closesR := me ++ p.appendAfter "_closesR",
      head := ``Tools.ShippingNoPortsTyped.machine_design_noPortsTBS,
      names? := some (me ++ p.appendAfter "_names") }
  Lean.logInfo m!"NZ [{n}]: head machine_design_noPortsTBS"

/-! ## The satisfaction theorem (one elaborated term; the statement is its type) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  addSat
    `Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_satS (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5
        (Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssemblyS.sat_of_designClosedBS
      (Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_designClosedBS hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_kidsSat hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_designP0 hcore hpost entry hR0 hB)
      (fun hcore => Tools.ShippingSlotRegsRun.slotRegs_runMT (nDecl := 3)
        Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machineData
        Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machine_ok
        Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machine_body
        (by first | decide | decide +kernel) (by first | decide | decide +kernel)
        (by first | decide | decide +kernel)
        hB hcore entry (Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_closesR hR0))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      -- (writing-time guess n5) hinitW at inits 5 / 7
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)))

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let me := `Sparkle.Tests.Compiler.NonzeroInitParentTest
  for suf in ["_initNZ", "_closesR", "_designClosedBS", "_satS"] do
    Tests.Compiler.NoPortsTest.stdAxioms (me ++ (`collMixSame5).appendAfter suf)
  let t := (← Lean.getConstInfo (me ++ `collMixSame5_satS)).type
  for k in [``Tools.ShippingDesignSVBounds.InvN, ``Tools.ShippingMachineShipsHier.Reset1,
      ``Tools.ShippingSeqOptSoundness.seedIn] do
    let prem ← Lean.Meta.forallTelescope t fun xs _ => do
      let mut found := false
      for x in xs do
        if ((← Lean.Meta.inferType x).find? (·.isConstOf k)).isSome then found := true
      pure found
    if prem then throwError "collMixSame5_satS: a premise mentions {k}"
  -- the start state of the conclusion is `stOf b regs slots` (the slots' reset values)
  unless (t.find? (·.isConstOf ``Tools.ShippingSatAssemblyS.stOf)).isSome do
    throwError "collMixSame5_satS: the conclusion does not mention stOf"
  Lean.logInfo m!"NZ collMixSame5_satS: {t}"

#print axioms Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_satS

end Sparkle.Tests.Compiler.NonzeroInitParentTest
