import Tools.ShippingFGCircuitS1lReader
set_option autoImplicit false
namespace S1nProbe
open Lean Meta Elab Command Term Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingFGCircuitRoots Tools.ShippingGen5DataOf Sparkle.Tests.SignalLoopTest Tools.ShippingGen2 Tools.ShippingFGCircuitS1lReader

def probe (nm : Name) (ty val : Lean.Expr) (dd : Tools.ShippingMachineAuto.MachineData) : MetaM Unit := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? nm | throwError "no {nm}"
  logInfo m!"{nm}: type==ty {d.type == ty} value==val {d.value == val} lps {d.levelParams}"
  let se := structEnv env
  let ip := instancePredicate env
  let ui := userInliner env
  logInfo m!"{nm}: ui val {ui val == val} ui ty {ui ty == ty} ip val {ip val} projLoop {(se.proj ``Sparkle.Core.Signal.Signal.loop).isNone}"
  let E := EntryOfDecl d ip ui se
  logInfo m!"{nm}: certified none {(certifiedShape? false [] E).isNone} mixed none {(mixedCertifiedShape? false [] E ip).isNone}"
  let tin := Sparkle.Compiler.MachTupleIn.packTupleInputs val
  logInfo m!"{nm}: pack fixed {tin == val} rootFloat fixed {Sparkle.Compiler.MachRawSurface.rootFloat val == val} find none {(val.find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8)).isNone}"
  logInfo m!"{nm}: gatePeel {(mixedGatePeel val).map (fun p => p.1.length)} peeled==val {(mixedGatePeel val).map (fun p => p.2 == val)}"
  let r := machRoot se.proj val []
  logInfo m!"{nm}: machRoot spine {r.1.length} run? {r.2.1.isSome} {r.2.2.1.isSome} body==val {r.2.2.2 == val}"
  logInfo m!"{nm}: srcDomOf {(srcDomOf se ty val)}"
  let s := machineShape? false [] E se
  logInfo m!"{nm}: machineShape? some {s.isSome} eq {s.map (fun s => s == dd.shape)}"
  logInfo m!"{nm}: shape binders {dd.shape.binders.length} insts {dd.shape.insts.length} slots {dd.shape.layout.slots.length} lets {dd.shape.layout.lets}"
  let a := dataOfAt (fun _ => 1000000) E se dd.shape
  logInfo m!"{nm}: dataOfAt some {a.isSome}"

run_cmd liftTermElabM do
  probe ``shift4Loop shift4LoopType shift4LoopValue shift4Loop.machineData
  probe ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoop.machineData
  probe ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
end S1nProbe
