import Sparkle
import Sparkle.Core.StateMacro
import Tools.ShippingMachineCommand
import IP.YOLOv8.Blocks.Bottleneck
import IP.RV32.Divider

/-! Hand-written `Signal.loop` state machines on the machine route.

Many IP modules are written without `circuit do`: the state is a tuple of
registers (often declared with `declare_signal_state`), the body reads it
through `Signal.fst`/`Signal.snd` and returns `bundleAll! [Signal.register
init next, …]`, and the result is the loop's state read through the same
projections — often a TUPLE, which the module carries as one port `out`
(components packed, the first in the high bits, a Bool as one bit: the
legacy lowering's interface). The machine route reads such a declaration as
the same machine a `circuit do` is; `#machine_endpoint` proves it through
`Tools.ShippingMachineLoop.machine_trace_of_loop` (the loop's state stream,
`loop_stream`) with the same per-declaration `rfl`s. -/
namespace Sparkle.Tests.Compiler.ShippingMachineLoopTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-! ## Declarations -/

declare_signal_state CntState
  | cnt  : BitVec 8 := 0#8
  | flag : Bool     := false

/-- A counter with a wrap flag, the result a tuple. -/
def counterLoop (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let s := Signal.loop fun state =>
    let c := CntState.cnt state
    let f := CntState.flag state
    let next := Signal.mux en (c + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) c
    let wrap := c === (Signal.pure 255#8 : Signal defaultDomain (BitVec 8))
    bundleAll! [Signal.register 0#8 next, Signal.register false (Signal.mux en wrap f)]
  bundle2 (CntState.cnt s) (CntState.flag s)

/-- One register, a single Signal result. -/
def accLoop (x : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  let s := Signal.loop fun (acc : Signal defaultDomain (BitVec 16)) =>
    Signal.register 0#16 (acc + x)
  s

/-! ## The route -/

run_cmd liftTermElabM do
  let env ← getEnv
  let senv := structEnv env
  for (n, slots) in [(``counterLoop, 2), (``accLoop, 1),
      (``Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController, 4),
      (``Sparkle.IP.RV32.Divider.dividerSignal, 8)] do
    let ci ← getConstInfo n
    let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
    let some shape := machineShape? false [] entry senv | throwError "{n}: not on the machine route"
    unless shape.loops.length == 1 && shape.layout.slots.length == slots do
      throwError "{n}: loops {shape.loops}, slots {shape.layout.slots.length}"
    let (m, _) ← synthesizeCombinational n
    let regs := m.body.filter fun st => match st with | .register .. => true | _ => false
    unless regs.length == slots do throwError "{n}: {regs.length} registers emitted"
    unless m.outputs.map (·.name) == ["out"] do throwError "{n}: output ports {m.outputs.map (·.name)}"

/-! ## The endpoints -/

/-- A loop as the WHOLE value (no `let`): read as `let s := loop; s`. -/
def wholeLoop : Signal defaultDomain (BitVec 8) :=
  Signal.loop fun (self : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (self + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)))

/-- A Bool loop register as the whole value, in any domain. -/
def wholeToggle {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool :=
  Signal.loop fun (s : Signal dom Bool) =>
    Signal.register false (Signal.mux en (~~~s) s)

#machine_endpoint wholeLoop
#machine_endpoint wholeToggle
#machine_endpoint counterLoop
#machine_endpoint accLoop
#machine_endpoint Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController
#machine_endpoint Sparkle.IP.RV32.Divider.dividerSignal

run_cmd do
  if (← get).messages.hasErrors then throwError "machine loop regression failed"
  for name in [``counterLoop.machine_sound, ``accLoop.machine_sound,
      ``Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController.machine_sound,
      ``Sparkle.IP.RV32.Divider.dividerSignal.machine_sound,
      ``Tools.ShippingMachineLoop.machine_trace_of_loop,
      ``Tools.ShippingMachineLoop.loop_stream] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE LOOPS: hand-written Signal.loop state machines (two IP modules among them), each with its kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineLoopTest
