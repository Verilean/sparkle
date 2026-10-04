import Sparkle.Core.CircuitDo
import Sparkle.Compiler.InlineAttr
import Tools.ShippingMachineCommand
import Tools.ShippingMachineChild

/-! `@[hardware_module]` calls inside a `circuit do`, on the machine route.

A combinational hardware module called in the body is emitted as an
INSTANCE (hierarchy is kept); the transition reads its output as an input
— the open-module view, in which an instance's outputs are free inputs —
and `closeInsts` ties that input to the instance. The endpoint
(`machine_trace_of_data_ext`) states the trace with the inputs at the
calls' positions given by the calls themselves, over the machine's state
loop; the kernel checks that each call is pointwise in the state
(`machine_inst_k`). What the endpoint does NOT cover: that the instance's
wire carries the call's value — the child module's own theorem and the
linked semantics (S6) give that; see the TrustBase. -/
namespace Sparkle.Tests.Compiler.ShippingMachineInstTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

/-! ## Declarations -/

/-- A combinational child: a byte selected by a 2-bit index. -/
@[hardware_module]
def pick (sel : Signal defaultDomain (BitVec 2)) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) x
    (Signal.mux (sel === (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)))
      (x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)))
      (x ^^^ (Signal.pure 0xFF#8 : Signal defaultDomain (BitVec 8))))

/-- A machine calling the child on its register and an input; the call's
output is the next value and the result. -/
def caller (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := pick selS (accS + x)
    sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
    acc <~ y
    return y

/-- The same call twice (`circuit do` copies its `let`s): one instance. -/
def callerTwice (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let selS := (sel : Signal defaultDomain (BitVec 2))
    let y := pick selS x
    sel <~ Signal.mux (y === (Signal.pure 7#8 : Signal defaultDomain (BitVec 8))) selS
      (selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)))
    return y

/-- A sub-machine's result as a call argument. -/
def counter2 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 2) :=
  circuit do
    let c ← Signal.reg 0#2
    let cS := (c : Signal defaultDomain (BitVec 2))
    c <~ Signal.mux en (cS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) cS
    return cS

def callerNested (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let s := counter2 en
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    acc <~ pick s (accS + x)
    return accS

/-- A combinational child polymorphic in the domain. -/
@[hardware_module]
def pickD {dom : DomainConfig} (sel : Signal dom (BitVec 2)) (x : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  Signal.mux (sel === (Signal.pure 0#2 : Signal dom (BitVec 2))) x
    (x ^^^ (Signal.pure 0xFF#8 : Signal dom (BitVec 8)))

/-- A domain-polymorphic machine calling it: the domain binder has no port,
so the call's output and argument wires are found by PORT position (a
regression: counting binders connected the instance to the wrong wires). -/
def callerD {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let sel ← Signal.reg 0#2
    let acc ← Signal.reg 0#8
    let selS := (sel : Signal dom (BitVec 2))
    let accS := (acc : Signal dom (BitVec 8))
    let y := pickD selS (accS + x)
    sel <~ selS + (Signal.pure 1#2 : Signal dom (BitVec 2))
    acc <~ y
    return y

/-! ## The route -/

run_cmd liftTermElabM do
  let env ← getEnv
  let senv := structEnv env
  for (n, insts, child) in [(``caller, 1, ``pick), (``callerTwice, 1, ``pick),
      (``callerNested, 1, ``pick), (``callerD, 1, ``pickD)] do
    let ci ← getConstInfo n
    let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
    let some shape := machineShape? false [] entry senv | throwError "{n}: not on the machine route"
    unless shape.insts.length == insts do
      throwError "{n}: {shape.insts.length} calls read, expected {insts}"
    let (m, d) ← synthesizeCombinational n
    let emitted := m.body.filter fun st => match st with | .inst .. => true | _ => false
    unless emitted.length == insts do throwError "{n}: {emitted.length} instances emitted"
    unless d.modules.any (·.name == toString child) do throwError "{n}: the child is not in the design"
    -- the instance's output is a wire, not an input port
    unless m.inputs.all (fun p => !p.name.startsWith "_gen_inst") do
      throwError "{n}: an instance output is still an input port"
    -- the instance drives the call's output wire and reads the argument
    -- wires (never a register's output or next-value wire)
    for st in emitted do
      match st with
      | .inst _ _ conns =>
        let outW := conns.getLast?.map (·.2)
        unless outW == some (.ref "_gen_inst0") do
          throwError "{n}: the instance drives {repr outW}, not the call's output wire"
        for (_, e) in conns.dropLast do
          match e with
          | .ref w =>
            unless w.startsWith "_gen_inst0_arg" do
              throwError "{n}: the instance reads {w}, not an argument wire"
          | _ => throwError "{n}: a non-wire connection"
      | _ => pure ()

/-! ## The endpoints -/

#machine_endpoint caller
#machine_endpoint callerTwice
#machine_endpoint callerNested
#machine_endpoint callerD

run_cmd do
  if (← get).messages.hasErrors then throwError "machine instance regression failed"
  for name in [``caller.machine_sound, ``callerTwice.machine_sound, ``callerNested.machine_sound,
      ``caller.machine_inst_0, ``Tools.ShippingMachineAuto.machine_trace_of_data_ext,
      ``Tools.ShippingMachineNest.machine_trace_of_nested_ext,
      ``Tools.ShippingMachineInst.runModule_of_closeInsts, ``callerD.machine_sound,
      ``Tools.ShippingMachineInst.closeInsts_calls,
      ``Tools.ShippingMachineCompose.runModuleH_of_seeded,
      ``Tools.ShippingMachineCompose.childComputes_of_call,
      ``Tools.ShippingMachineCompose.runModuleH_of_run,
      ``Tools.ShippingMachineCompose.sourceInputs_extend,
      ``Tools.ShippingMachineCompose.machine_linked,
      ``Tools.ShippingMachineChild.childFn_of_trace,
      ``Tools.ShippingMachineChild.child_full,
      ``Tools.ShippingMachineChild.machine_traceL_of_comb,
      ``Tools.ShippingMachineInst.closeInsts_insts,
      ``Tools.ShippingMachineEntry.synthesizeMachineCertified_sound] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE INSTANCES: four declarations calling a hardware module, each an instance in the emitted module with its kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineInstTest
