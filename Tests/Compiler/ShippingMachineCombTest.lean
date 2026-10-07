import Sparkle
import Tools.ShippingMachineCommand
import IP.Net.IPv4
import IP.Net.HTTP

/-! Combinational declarations with `let`s on the machine route.

A combinational module written with shared `let`s — the byte generators and
checksums of the network IP, used as `@[hardware_module]` children — is a
machine without slots: no register, no clock. The machine route compiles it
with its `let`s shared (one wire each) and without `clk`/`rst` (the
interface of the combinational module), and `#machine_endpoint` proves it
through `Tools.ShippingMachineLoop.machine_trace_of_comb`. These are the
children the instance unit's theorems take as hypotheses; their own
theorems are the first half of discharging them. -/
namespace Sparkle.Tests.Compiler.ShippingMachineCombTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A byte selected from a word by a counter, with shared `let`s. -/
def pickByte (w : Signal defaultDomain (BitVec 16)) (sel : Signal defaultDomain (BitVec 2)) :
    Signal defaultDomain (BitVec 8) :=
  let hi := w.map (BitVec.extractLsb' 8 8 ·)
  let lo := w.map (BitVec.extractLsb' 0 8 ·)
  let x := hi ^^^ lo
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) hi
    (Signal.mux (sel === (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))) lo
      (Signal.mux (sel === (Signal.pure 2#2 : Signal defaultDomain (BitVec 2))) x (x + x)))

run_cmd liftTermElabM do
  let env ← getEnv
  let senv := structEnv env
  for n in [``pickByte, ``Sparkle.IP.Net.IPv4.ipv4HeaderByte,
      ``Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig, ``Sparkle.IP.Net.HTTP.httpGetByte] do
    let ci ← getConstInfo n
    let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
    let some shape := machineShape? false [] entry senv | throwError "{n}: not on the machine route"
    unless shape.layout.slots.isEmpty do throwError "{n}: has slots"
    let (m, _) ← synthesizeCombinational n
    unless m.inputs.all (fun p => p.name != "clk" && p.name != "rst") do
      throwError "{n}: a combinational module got a clock"
    unless m.body.all (fun st => match st with | .register .. => false | _ => true) do
      throwError "{n}: registers"

#machine_endpoint pickByte
#machine_endpoint Sparkle.IP.Net.IPv4.ipv4HeaderByte
#machine_endpoint Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig
#machine_endpoint Sparkle.IP.Net.HTTP.httpGetByte

run_cmd do
  if (← get).messages.hasErrors then throwError "machine comb regression failed"
  for name in [``pickByte.machine_sound, ``Sparkle.IP.Net.IPv4.ipv4HeaderByte.machine_sound,
      ``Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig.machine_sound,
      ``Sparkle.IP.Net.HTTP.httpGetByte.machine_sound,
      ``Tools.ShippingMachineLoop.machine_trace_of_comb] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE COMB: combinational declarations with lets (three IP children among them), each with its kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineCombTest
