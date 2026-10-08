import Tests.Compiler.ShippingMachineSeqTest
import Tools.ShippingMachineDepthCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingPremiseEval

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

/-! ## Every premise of `grandH.machine_ships_hierN1`, on the real compile

The theorem is conditional; its premises are evaluated here with the
checkers it names (`shipsHierCheck`, `kidsMaskedN`; at the boundary
`extendsAwayB`, `noInstOfB`, `kidsComb`) and its run boundaries traced
(`midH`'s instance module is the post-processing of a core run of `midH`;
`rcH`'s instance module in `midH`'s design is `rcH`'s full-entry run). The
reflection boundary and the run's input / initial-state premises are listed,
not evaluated. -/
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  let v ← evalShipsHierSeq ``grandH (some 1)
  Lean.logInfo m!"{v.report}"
  unless v.tag == "MOD:PREM|TRACE:MATCHED|SV:PARENT|SVCHILD:CHECKED" && v.applies do
    throwError "grandH: {v.tag}"
  -- both run boundaries were traced (measured), and each decidable boundary fact checked
  unless v.traces.length == 2 && v.boundaryChecks.length == 3 do
    throwError "grandH: {v.traces.length} traces, {v.boundaryChecks.length} boundary checks"

/-! ## A rejected premise is reported as not applying

`grand` (`ShippingMachineSeqTest`, whose child `mid` has a child of its
own) has no depth-0 theorem: generation fails, and its premises evaluated
with the depth-0 boundary are rejected (`MOD:NOPREM`), never counted. -/
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  let v ← evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand (some 0)
  unless v.moduleTag.startsWith "MOD:NOPREM:" && !v.applies do
    throwError "grand at depth 0: a rejected premise was not reported: {v.tag}"
  let gen ← try
      discard <| Tools.ShippingMachineDepthCommand.generateShipsN
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 0
      pure true
    catch _ => pure false
  if gen then throwError "grand at depth 0: generated, but its boundary cannot hold"
  Lean.logInfo m!"DEPTH H: rejected premises are reported, not counted: {v.tag}"

run_cmd do
  if (← get).messages.hasErrors then throwError "depth with combinational grandchildren regression failed"
  for name in [``grandH.machine_composedN1, ``grandH.machine_ships_hierN1, ``midH.machine_composedN0, ``midH.seq_child_runN_of0,
      ``Tools.ShippingMachineDepthH.composedN0_of_H, ``Tools.ShippingMachineDepthH.runModuleTG_flat_of_H,
      ``Tools.ShippingMachineDepthH.BoundH_of_each, ``Tools.ShippingHierPremisesBase.shipsHierCheck_sound,
      ``Tools.ShippingHierPremisesBase.extendsAwayB_sound, ``Tools.ShippingHierPremisesBase.noInstOfB_sound,
      ``Tools.ShippingMachineShipsHier.machine_ships_hier,
      ``Tools.ShippingMachineShipsHierH.machine_ships_hierH, ``Tools.ShippingHierPremises.shipsHierHCheck_sound,
      ``Tools.ShippingHierShipsSV.shipped_sv, ``Tools.ShippingHierShipsSV.checkedOptimize_inputs,
      ``Tools.ShippingMachineDepthRun.seqChildRunN_of_composed, ``Tools.ShippingMachineDepthChild.calls_ports] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"AXIOMS: standard only (propext, Classical.choice, Quot.sound)"

end Sparkle.Tests.Compiler.ShippingMachineDepthHTest
