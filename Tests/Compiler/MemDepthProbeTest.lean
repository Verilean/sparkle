import Lean.Elab.Command
import Sparkle
import Tools.ShippingMachineCommand
import Tools.ShippingMachineMemCommand
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineSeqCommandR
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingNoPortsMemCommand
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingNoPortsDeepCommand
import Tests.Compiler.ShippingMachineSeqTest

/-! # A parent whose CHILD has a memory: the smallest declarations, and which command stops (round par/b-38)

WRITTEN, NOT BUILT. TARGET-ONLY. A MEASUREMENT: every command below is
wrapped in `#mem_depth_try "label" in …` (the built wrapper `#drc_try` of
`Tests/Compiler/DepthRegsChildTest.lean`, copied): a thrown or logged error
becomes ONE information line, the environment and the message log are put
back, and the file goes on. Nothing is asserted; the file is an error in no
case. The PREDICTED outcome of each step is in
`docs/parallel/B-mem-depth.md` §3.

## The declarations (new; no built file has them)

* `memCounterH`: `memCounter` of `Tests/Compiler/ShippingMachineMemLinkedTest.lean`
  17 (a hand-written loop with two registers and a combinational-read
  memory), TAGGED `@[hardware_module]` so that a caller instantiates it —
  the untagged `memCounter` would be inlined into its caller. One `BitVec 8`
  output.
* `memParent1`: a register parent whose ONLY call is `memCounterH`. By
  reading (`Sparkle/Compiler/Elab.lean`, the reader's `instStruct`; the note
  in `DepthRegsChildTest.lean` 79–86) a parent whose only calls are
  one-output is read under the ONE-OUTPUT closing (`instFields = []`).
* `memParent`: the same parent with a second call, of the structure-result
  child `cnt` (`ShippingMachineSeqTest` 20) — the device of `regsParent`
  that puts the parent under the GENERAL closing, where the depth generators
  work. This is the smallest shape of the class "a register parent, general
  closing, one callee with a memory".
* `memGrand`: a register parent of `memParent` (tagged) and `cnt`: the
  two-level variant.

## The steps

For `memCounterH` as an ENTRY (the memory parent at depth 0; the built chain
of `memCounter`): `#machine_endpoint`, `#machine_composedT`,
`#machine_ships_hier`, `#machine_design_svR0`, `#machine_no_ports_mem`.

For each parent: `#machine_endpoint`, `#machine_design_svNR f n` (the grouped
depth generator: `f.machine_ships_hierNR{n}` and `f.machine_design_svNR{n}`),
`#machine_closes_at`, then the check-free depth generators
`#machine_no_ports_kids f 1` and `#machine_no_ports_deep f 2`.

A line `MEMDEPTH <label>: OK` means that command ran without an error in
this environment; `FAILED` carries the command's own message. Neither is a
statement about an endpoint's content. -/
namespace Sparkle.Tests.Compiler.MemDepthProbeTest
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Sparkle.Tests.Compiler.ShippingMachineSeqTest (cnt CntOut)

/-- A write port from the inputs, a read at a counter: a machine with two
registers and one memory, as a hardware module. -/
@[hardware_module]
def memCounterH (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 rd)
  Signal.snd st

/-- A register parent whose only call is the memory-using child. -/
def memParent1 (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := memCounterH we wa wd
    acc <~ accS + y
    return accS

/-- A register parent of the memory-using child and of a structure-result
sequential child (the general closing). -/
@[hardware_module]
def memParent (en we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let y := memCounterH we wa wd
    acc <~ Signal.mux k.hit y accS
    return accS

/-- Two levels: a register parent of `memParent` and of `cnt`. -/
def memGrand (en we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let y := memParent en we wa wd
    acc <~ Signal.mux k.hit y accS
    return accS

end Sparkle.Tests.Compiler.MemDepthProbeTest

namespace Tests.Compiler.MemDepthProbeTest
open Lean Elab Command

/-- `#mem_depth_try "label" in cmd`: a command as a LOG-ONLY step (the built
`#drc_try` of `Tests/Compiler/DepthRegsChildTest.lean`): a thrown or logged
error is reported in ONE information line, the environment and the message
log are put back, and the file goes on. Never silent. -/
elab "#mem_depth_try " tag:str " in " c:command : command => do
  IO.eprintln s!"MEMDEPTH START {tag.getString}"
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let t0 ← IO.monoMsNow
  let res : Option String ← try
      elabCommand c
      pure none
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (some msg)
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match res with
    | some msg => some msg
    | none => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  let ms := (← IO.monoMsNow) - t0
  match failure with
  | some msg =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"MEMDEPTH {tag.getString}: FAILED (log only, the environment put back; {ms} ms) — {msg}"
  | none =>
    logInfo m!"MEMDEPTH {tag.getString}: OK ({ms} ms)"

end Tests.Compiler.MemDepthProbeTest

/-! ## `memCounterH` as an entry: the memory parent at depth 0 -/

#mem_depth_try "C1 #machine_endpoint memCounterH" in
  #machine_endpoint Sparkle.Tests.Compiler.MemDepthProbeTest.memCounterH
#mem_depth_try "C2 #machine_composedT memCounterH" in
  #machine_composedT Sparkle.Tests.Compiler.MemDepthProbeTest.memCounterH
#mem_depth_try "C3 #machine_ships_hier memCounterH" in
  #machine_ships_hier Sparkle.Tests.Compiler.MemDepthProbeTest.memCounterH
#mem_depth_try "C4 #machine_design_svR0 memCounterH" in
  #machine_design_svR0 Sparkle.Tests.Compiler.MemDepthProbeTest.memCounterH
#mem_depth_try "C5 #machine_no_ports_mem memCounterH" in
  #machine_no_ports_mem Sparkle.Tests.Compiler.MemDepthProbeTest.memCounterH

/-! ## `memParent1`: the only call is the memory-using child -/

#mem_depth_try "P1.1 #machine_endpoint memParent1" in
  #machine_endpoint Sparkle.Tests.Compiler.MemDepthProbeTest.memParent1
#mem_depth_try "P1.2 #machine_design_svNR memParent1 1" in
  #machine_design_svNR Sparkle.Tests.Compiler.MemDepthProbeTest.memParent1 1
#mem_depth_try "P1.3 #machine_closes_at memParent1" in
  #machine_closes_at Sparkle.Tests.Compiler.MemDepthProbeTest.memParent1
#mem_depth_try "P1.4 #machine_no_ports_kids memParent1 1" in
  #machine_no_ports_kids Sparkle.Tests.Compiler.MemDepthProbeTest.memParent1 1

/-! ## `memParent`: the general closing, one callee with a memory -/

#mem_depth_try "P2.1 #machine_endpoint memParent" in
  #machine_endpoint Sparkle.Tests.Compiler.MemDepthProbeTest.memParent
#mem_depth_try "P2.2 #machine_design_svNR memParent 1" in
  #machine_design_svNR Sparkle.Tests.Compiler.MemDepthProbeTest.memParent 1
#mem_depth_try "P2.3 #machine_closes_at memParent" in
  #machine_closes_at Sparkle.Tests.Compiler.MemDepthProbeTest.memParent
#mem_depth_try "P2.4 #machine_no_ports_kids memParent 1" in
  #machine_no_ports_kids Sparkle.Tests.Compiler.MemDepthProbeTest.memParent 1
#mem_depth_try "P2.5 #machine_no_ports_deep memParent 2" in
  #machine_no_ports_deep Sparkle.Tests.Compiler.MemDepthProbeTest.memParent 2

/-! ## `memGrand`: two levels -/

#mem_depth_try "G.1 #machine_endpoint memGrand" in
  #machine_endpoint Sparkle.Tests.Compiler.MemDepthProbeTest.memGrand
#mem_depth_try "G.2 #machine_design_svNR memGrand 2" in
  #machine_design_svNR Sparkle.Tests.Compiler.MemDepthProbeTest.memGrand 2
#mem_depth_try "G.3 #machine_closes_at memGrand" in
  #machine_closes_at Sparkle.Tests.Compiler.MemDepthProbeTest.memGrand
#mem_depth_try "G.4 #machine_no_ports_deep memGrand 2" in
  #machine_no_ports_deep Sparkle.Tests.Compiler.MemDepthProbeTest.memGrand 2
