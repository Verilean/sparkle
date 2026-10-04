import Sparkle
import Tools.ShippingMachineLinkedCommand

/-! A machine composed with its child, in the linked semantics.

`pickByteH` is a combinational child on the machine route (shared `let`s,
no slots); `callerL` is a state machine calling it. `#machine_child`
proves that the child's full-entry module computes the child's source
function on its ports; `#machine_linked` proves that the LINKED run of the
caller's module — the instance evaluated by the module its name resolves to
in the design — shows the caller, given that its children compute their
source functions. -/
namespace Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A byte selected from a word by a counter, with shared `let`s. -/
@[hardware_module]
def pickByteH (w : Signal defaultDomain (BitVec 16)) (sel : Signal defaultDomain (BitVec 2)) :
    Signal defaultDomain (BitVec 8) :=
  let hi := w.map (BitVec.extractLsb' 8 8 ·)
  let lo := w.map (BitVec.extractLsb' 0 8 ·)
  let x := hi ^^^ lo
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) hi
    (Signal.mux (sel === (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) lo
      (Signal.mux (sel === (Signal.pure 2#2 : Signal defaultDomain (BitVec 2))) x (x + x)))

/-- A counter selecting the bytes of the input word through the child. -/
def callerL (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let y := pickByteH w selS
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    return y

#machine_endpoint pickByteH
#machine_child pickByteH
#machine_endpoint callerL
#machine_linked callerL

run_cmd do
  if (← get).messages.hasErrors then throwError "machine linked regression failed"
  for name in [``pickByteH.machine_child, ``callerL.machine_linked,
      ``Tools.ShippingMachineCompose.machine_linked_calls,
      ``Tools.ShippingMachineAuto.machine_traceL_of_data_ext,
      ``Tools.ShippingMachineChild.child_full] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE LINKED: a state machine and its combinational child, composed in the linked semantics, checked by the kernel"

end Sparkle.Tests.Compiler.ShippingMachineLinkedTest
