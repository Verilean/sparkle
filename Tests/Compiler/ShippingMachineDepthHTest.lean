import Tests.Compiler.ShippingMachineSeqTest
import Tools.ShippingMachineDepthCommand
import Tools.ShippingGateChildCommand

/-! A sequential child whose own calls are COMBINATIONAL (`wKeccakF`'s shape:
the permutation engine calls the round-constant table). `midH`'s composed
theorem is the combinational linked run (`#machine_composed`); at depth 0 it
is the stateful `flatKS` run (`composedN0_of_H`: its child is assignments
only, local, every input wired), under the boundary `BndH` (the calls'
premise without the wiring — `midH` calls one child). `grandH` consumes it at
depth 1. -/
namespace Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Lean
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest (CntOut)

/-- A combinational table. -/
@[hardware_module]
def rcH {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux (x === (Signal.pure 0#8 : Signal dom (BitVec 8)))
    (Signal.pure 1#8 : Signal dom (BitVec 8)) (x + x)

/-- A sequential child calling the table. -/
@[hardware_module]
def midH {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let y := rcH rs
    r <~ Signal.mux en y rs
    return ({ n := rs, hit := rs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : CntOut dom)

/-- Its parent. -/
def grandH (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := midH en
    r <~ Signal.mux m.hit (rs + m.n) rs
    return rs

set_option maxHeartbeats 0 in
#machine_endpoint midH
set_option maxHeartbeats 0 in
#machine_linked midH
set_option maxHeartbeats 0 in
#machine_composed midH
set_option maxHeartbeats 0 in
#machine_endpoint grandH
set_option maxHeartbeats 0 in
#machine_composedN grandH 1
set_option maxHeartbeats 0 in
#machine_ships_hierN grandH 1

-- `midH`'s boundary facts that are decidable, on its real core module
open Tools.ShippingHierOpen in
run_cmd Lean.Elab.Command.liftTermElabM do
  let (m, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore ``midH [] false
  unless Tools.ShippingMachineDepthH.kidsComb D.modules m.body do
    throwError "midH's child is not assignments-only / local / wired"
  unless linkedWF (Tools.ShippingMachineLinked.childMap D.modules) m.body do
    throwError "midH is not linked-well-formed"
  Lean.logInfo m!"DEPTH H: midH's decidable boundary facts hold"

run_cmd do
  if (← get).messages.hasErrors then throwError "depth with combinational grandchildren regression failed"
  for name in [``grandH.machine_composedN1, ``grandH.machine_ships_hierN1, ``midH.machine_composedN0, ``midH.seq_child_runN_of0,
      ``Tools.ShippingMachineDepthH.composedN0_of_H, ``Tools.ShippingMachineDepthH.runModuleTG_flat_of_H] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"

end Sparkle.Tests.Compiler.ShippingMachineDepthHTest
