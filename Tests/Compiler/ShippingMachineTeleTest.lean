import Tools.ShippingMachineLinkedCommand
import IP.Net.HFTStrategy
import Tests.Compiler.ShippingMachineCombTest
import IP.Control.DividerQ

/-! Chains of sub-machines on the machine route.

A sub-machine bound by `let` may read an EARLIER sub-machine's result — a
parser feeding an emitter (`hftStrategy`). The compiler flattens the chain
into one machine (the emitter's transition reads the parser's slots); the
endpoint reads the sub-machines as a telescope (`TeleT`, each body over the
earlier results) through `machine_trace_of_tele_ext`
(Tools/ShippingMachineTeleNest.lean, on `fused_state` for a chain in
Tools/ShippingMachineTele.lean). -/
namespace Sparkle.Tests.Compiler.ShippingMachineTeleTest
open Sparkle.Core.Domain Sparkle.Core.Signal

structure PulseOut (dom : DomainConfig) where
  hit : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PulseOut dom) dom := ⟨⟩

structure CountOut (dom : DomainConfig) where
  n : Signal dom (BitVec 8)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (CountOut dom) dom := ⟨⟩

/-- A detector: pulses when the input byte is 7. -/
def detect {dom : DomainConfig} (x : Signal dom (BitVec 8)) : PulseOut dom :=
  circuit do
    let h ← Signal.reg false
    h <~ (x === (Signal.pure 7#8 : Signal dom (BitVec 8)))
    return ({ hit := (h : Signal dom Bool) } : PulseOut dom)

/-- A counter driven by an enable. -/
def countOn {dom : DomainConfig} (en : Signal dom Bool) : CountOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs } : CountOut dom)

/-- The chain: the counter reads the detector's result. -/
def chain2 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let d := detect x
  let k := countOn d.hit
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    r <~ k.n + rs
    return rs

/-- A three-long chain, the last sub-machine reading both earlier ones. -/
def chain3 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let d := detect x
  let k := countOn d.hit
  let k2 := countOn (d.hit &&& (k.n === (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))))
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    r <~ k2.n ^^^ rs
    return rs

open Sparkle.IP.Net.HFTStrategy in
/-- The HFT strategy's byte output: the parser → emitter chain, the emitter
calling the `@[hardware_module]` byte table inside its body. -/
def hftByte (inByte : Signal defaultDomain (BitVec 8)) (inValid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (hftStrategy inByte inValid).outByte

/-- A hand-written `Signal.loop` engine (the Q7.8 divider, `@[reducible]`)
inside a `circuit do`: a sub-machine of the telescope (`TeleT.loop`), its
arguments read from the enclosing registers. -/
def divInLoop (n d : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let go ← Signal.reg false
    let acc ← Signal.reg (0#16)
    let goS := (go : Signal defaultDomain Bool)
    let e := Sparkle.IP.Control.DividerQ.dividerQ7_8 n d goS
    go <~ ~~~goS
    acc <~ Signal.mux (Signal.snd e) (Signal.fst e) (acc : Signal defaultDomain (BitVec 16))
    return acc

#machine_endpoint divInLoop
#machine_endpoint chain2
#machine_endpoint chain3
-- the byte table's endpoint is ShippingMachineCombTest's
#machine_child Sparkle.IP.Net.HTTP.httpGetByte
#machine_endpoint hftByte
#machine_linked hftByte

run_cmd do
  if (← get).messages.hasErrors then throwError "machine chain regression failed"
  for name in [``divInLoop.machine_sound, ``chain2.machine_sound, ``chain3.machine_sound, ``hftByte.machine_sound,
      ``hftByte.machine_linked,
      ``Tools.ShippingMachineTele.fused_state, ``Tools.ShippingMachineTele.loops_rec,
      ``Tools.ShippingMachineTeleNest.machine_trace_of_tele_ext,
      ``Tools.ShippingMachineTeleNest.machine_traceL_of_tele_ext] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"MACHINE CHAINS: sub-machines reading earlier ones' results, kernel-checked endpoints"

end Sparkle.Tests.Compiler.ShippingMachineTeleTest
