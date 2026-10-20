import Sparkle
import Tools.ShippingMachineMemCommand
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingHierSVRun
import Tests.Compiler.ShippingMachineFuseTest
import Tools.ShippingPremiseEval

/-! A hand-written `Signal.loop` reading combinational-read memories,
composed with its memory children: `#machine_composedT` proves that the
stateful linked run of the emitted module — every memory instance stepping
its own memory module from zero — shows the source. -/
namespace Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A write port from the inputs, a read at a counter. -/
def memCounter (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 rd)
  Signal.snd st

/-- Two memories (one read at a constant address), sharing operands. -/
def twoMems (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := Signal.memoryComboRead addr wd we (Signal.pure 0#4)
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 + r2))
  Signal.snd st

/-- A combinational and a synchronous read. -/
def mixedMems (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let r1 := Signal.memoryComboRead wa wd we addr
    let r2 := Signal.memory wa (Signal.snd st) we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (r1 ^^^ r2))
  Signal.snd st

#machine_endpoint memCounter
#machine_composedT memCounter
#machine_endpoint twoMems
#machine_composedT twoMems
#machine_endpoint mixedMems
#machine_composedT mixedMems
-- a fused nested loop with a memory and a dead memory (its endpoint is for
-- the fused value, transported back to the declaration)
#machine_composedT Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory

-- to the shipped module: the optimizer checked on the extracted interface
#machine_ships_hier memCounter
#machine_ships_hier twoMems
#machine_ships_hier mixedMems

-- its module premises, on the real modules (the memory children's output bound included)
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``memCounter, ``twoMems, ``mixedMems] do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Sparkle.IR.RefineCheck.hierBinds b do throwError "{n}: the optimizer check does not bind"
    unless Tools.ShippingHierOpen.linkedWF C b.body && Tools.ShippingHierOpen.linkedWF C o.body do
      throwError "{n}: not linked-well-formed"
    unless Tools.ShippingMachineShipsHier.kidsMem C b.body do
      throwError "{n}: a child is not a memory module (the output bound)"
    unless Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body do
      throwError "{n}: instance-output widths"
    -- `linked_sv_of_run` on the shipped module
    let wofO := Tools.SVParser.RoundtripProof.moduleWof o
    unless Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth o) o.body do
      throwError "{n}: shipped instance-output widths"
    unless (Tools.ShippingHierOpen.bodyInstOuts C o.body).all (fun w =>
        ((Sparkle.IR.HierCheck.openIns o).map (·.name)).contains w &&
        decide (Sparkle.IR.RegDedup.declWidth o w ≤ Tools.SVParser.EmitSem.weOf wofO w)) do
      throwError "{n}: a shipped instance-driven wire is not extracted or is wider than emitted"
    unless Tools.ShippingMachineShipsHier.kidsMem C o.body do throwError "{n}: the shipped module's children bound"
    unless o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI &&
        Tools.SVParser.EmitSem.seqCheck wofO (Tools.SVParser.EmitSem.weOf wofO) o.body &&
        (Tools.ShippingSeqSVSoundness.seqNames o.body).all (fun x =>
          Sparkle.IR.RegDedup.declWidth o x == Tools.SVParser.EmitSem.weOf wofO x) do
      throwError "{n}: the emitted-Verilog premises of the shipped module"
  Lean.logInfo m!"MEMORY PARENTS SHIP: module premises hold"

run_cmd do
  if (← get).messages.hasErrors then throwError "memory composition regression failed"
  for name in [``memCounter.machine_ships_hier, ``mixedMems.machine_ships_hier,
      ``Tools.ShippingMachineShipsHier.composedG_of_Tmem, ``memCounter.machine_composedT, ``twoMems.machine_composedT, ``mixedMems.machine_composedT,
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_composedT,
      ``Tools.ShippingMachineMemLinked.machine_linkedT_mem] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MEMORY COMPOSITION: loops reading memories (combinational and synchronous reads), composed with their memory instances (stateful run from zeroed memories), kernel-checked"

/-! ## The shipping theorems' premises, evaluated (`Tools.ShippingPremiseEval`)

Every premise each generated theorem states is evaluated on the real compile
with the checker it names, its run boundaries traced; generation alone is not
counted. -/
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, items) in ([(``memCounter, evalShipsHierSeq ``memCounter none), (``twoMems, evalShipsHierSeq ``twoMems none), (``mixedMems, evalShipsHierSeq ``mixedMems none)] : List (Lean.Name × Lean.Meta.MetaM Verdict)) do
    let v ← items
    unless v.applies && v.svTag == "SV:PARENT" do
      throwError "{n}: {v.tag}\n{v.report}"
  Lean.logInfo m!"MEM PARENTS: every module premise holds or is a traced boundary; the shipped module's emitted-Verilog premises hold"

end Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest
