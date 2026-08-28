/-
  `#verify_dsl_roundtrip` demo — the lean₄ → IR → lean₄ loop.

  `#verify_emit` proves  lean₄ → IR → Verilog → IR  equivalent.
  This one proves       lean₄ → IR → circuit-DSL SOURCE → IR
  equivalent: the IR is decompiled back to a `Signal.circuit do`
  definition, that definition is elaborated and re-synthesized, and the
  two designs' register/output cones are proven equal with `bv_decide`.

  Run interactively / via `lake env lean` (bv_decide + KnownIssues #2):

      lake env lean Tests/Verification/DslRoundtripDemo.lean
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab
import Tools.SVParser.DslEmit

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.DslRoundtripDemo

/-- Enable-gated accumulator: register + adder + mux. -/
def accEn (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc + d) acc
    return acc

#verify_dsl_roundtrip accEn

/-- Plain counter. -/
def cnt8 : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

#verify_dsl_roundtrip cnt8

/-- Two registers + bitwise ops + a slice: exercises more of the
    decompiler's operator subset. -/
def mix (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let x ← Signal.reg 0#8
    let y ← Signal.reg 0#8
    x <~ (a ^^^ b)
    y <~ ((x &&& b) ||| a)
    return (x + y)

#verify_dsl_roundtrip mix

end Sparkle.Tests.DslRoundtripDemo
