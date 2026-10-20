import Sparkle
import Tools.ShippingMachineCommand

/-! Nested hand-written `Signal.loop`s on the machine route.

A loop whose body reads other loops (a helper with its own state, inlined)
is read by the compiler as ONE machine: the outer loop's registers, then each
inner loop's, in reading order. The endpoint fuses the loops first
(`Tools.ShippingMachineFuseGen`, on `Tools.ShippingLoopFusion`): the value is
rewritten — by a kernel-checked equation — to one loop over the tree of all
the states, and that loop is proved like a single hand-written loop. The
calls (memories) are read in the order the compiler read them, a dead
memory included (an unused memory is still an instance). -/
namespace Sparkle.Tests.Compiler.ShippingMachineFuseTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A counter that runs while `go`: a helper with its own loop. -/
def innerCnt (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let s := Signal.loop fun (s : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (Signal.mux go (s + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) s)
  s

/-- One inner loop, read from the outer state. -/
def outer (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let a := Signal.fst st
    let c := innerCnt (a === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)))
    bundle2 (Signal.register 0#8 (Signal.mux en (a + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) a))
      (Signal.register 0#8 c)
  Signal.snd st

/-- Two inner loops, the second reading the first (siblings in order). -/
def siblings (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8)) =>
    let c1 := innerCnt en
    let c2 := innerCnt (c1 === (Signal.pure 3#8 : Signal defaultDomain (BitVec 8)))
    Signal.register 0#8 (st + c1 + c2)
  st

/-- A memory inside the inner loop, another one dead (never read). -/
def withMemory (we : Signal defaultDomain Bool) (wd : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead addr wd we addr
    let _dead := Signal.memoryComboRead addr wd we (Signal.pure 0#4)
    let c := innerCnt (rd === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)))
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 (rd + c))
  Signal.snd st

#synthesizeVerilog outer
#synthesizeVerilog siblings
#synthesizeVerilog withMemory

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  for n in [``outer, ``siblings, ``withMemory] do
    discard <| Tools.ShippingMachineCommand.generate n (checkCloses := false)

run_cmd do
  if (← get).messages.hasErrors then throwError "machine loop fusion regression failed"
  for name in [``outer.machine_sound, ``siblings.machine_sound, ``withMemory.machine_sound,
      ``Tools.ShippingLoopFusion.loop_nest, ``Tools.ShippingLoopFusion.loop_chain] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE LOOP FUSION: nested hand-written loops (siblings, a memory, a dead memory), each with its kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineFuseTest
