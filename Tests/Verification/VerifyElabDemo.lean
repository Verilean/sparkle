/-
  `#verify_elab` demo — the Signal↔IR link, generated and proven.

  For each circuit below the command elaborates it, inlines the
  register's next-state cone, and generates a kernel-checked theorem

      <name>_elab_trace : <name>_irTrace inputs t
        = ((<name> inputs).val t).toNat

  where `<name>_irTrace` is the recurrence the PROVEN IR semantics
  (`Sparkle.IR.Semantics.evalExpr`) induces on the elaborated module.
  Combined with `#verify_emit` (IR → Verilog → IR) this gives, per
  instance, that a theorem proven about the Signal program constrains
  the emitted SystemVerilog.

  The command checks the generated theorem's AXIOMS and fails if a
  recovered tactic smuggled in `sorryAx` — which happened once, on the
  first `sub` circuit, when the step recipe did not yet unfold
  `HSub.hSub`.

  Run: `lake env lean Tests/Verification/VerifyElabDemo.lean`
  (same interactive-run caveat as the other verifier demos).
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.VerifyElab

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

namespace Sparkle.Tests.VerifyElabDemo

/-- Enable-gated accumulator: register + mux + adder + compare. -/
def accEn (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc + d) acc
    return acc

#verify_elab accEn

/-- Plain free-running counter (no inputs). -/
def cnt8 : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

#verify_elab cnt8

/-- Subtracting accumulator with a nonzero initial value — the shape
    whose failed proof motivated the axiom check. -/
def subEn (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 9#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc - d) acc
    return acc

#verify_elab subEn

#print axioms accEn_elab_trace
#print axioms cnt8_elab_trace
#print axioms subEn_elab_trace

end Sparkle.Tests.VerifyElabDemo
