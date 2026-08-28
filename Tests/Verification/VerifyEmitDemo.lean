/-
  `#verify_emit` demo — kernel-checked roundtrip verification:
  the SystemVerilog Sparkle emits for these circuits is parsed back and
  proven (per-register next-state cone, per-output cone; bv_decide)
  equivalent to the IR it was emitted from.

  Run interactively / via `lake env lean` (bv_decide + KnownIssues #2):

      lake env lean Tests/Verification/VerifyEmitDemo.lean
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab
import Tools.SVParser.VerifyEmit

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.VerifyEmitDemo

/-- Counter with enable: register + adder + mux. -/
def demoAcc (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc + d) acc
    return acc

#verify_emit demoAcc

/-- Plain 8-bit counter (the tutorial shape). -/
def demoCounter : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    cnt <~ cnt + 1#8
    return cnt

#verify_emit demoCounter

end Sparkle.Tests.VerifyEmitDemo
