/-
  The GENERATOR's cone-sharing route (`set_option sparkle.deepShare true`,
  also `SPARKLE_DEEP_SHARE=1`): `#verify_elab_deep` reifies into a `CdoW`
  whose wire slots are the multiply-read wires, and proves the trace
  theorem with the linear recipe.  These circuits FAIL on the default
  (inlined) route from n=4 (heartbeat timeouts, see the TODO's baseline
  table); here they prove in seconds.  v1 scope: memory-free,
  single-port, no nested loops; the replay half is stage 2.

  Expected output: one "PROVEN via CdoW.elab_general" line per circuit.
-/
import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.DeepElab
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
namespace Sparkle.Tests.ConeSharingGen

def shareX4 (i : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    let w0 := a + i
    let w1 := (w0 + w0) ^^^ i
    let w2 := (w1 + w1) ^^^ i
    let w3 := (w2 + w2) ^^^ i
    let w4 := (w3 + w3) ^^^ i
    r <~ w4 + w3
    return w4

def shareX8 (i : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    let w0 := a + i
    let w1 := (w0 + w0) ^^^ i
    let w2 := (w1 + w1) ^^^ i
    let w3 := (w2 + w2) ^^^ i
    let w4 := (w3 + w3) ^^^ i
    let w5 := (w4 + w4) ^^^ i
    let w6 := (w5 + w5) ^^^ i
    let w7 := (w6 + w6) ^^^ i
    let w8 := (w7 + w7) ^^^ i
    r <~ w8 + w7
    return w8

set_option sparkle.deepShare true in
#verify_elab_deep shareX4

set_option sparkle.deepShare true in
#verify_elab_deep shareX8

end Sparkle.Tests.ConeSharingGen
