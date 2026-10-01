/-
  Property checking of Signal-DSL circuits with z3: `#bmc`, `#kinduction`
  and `#writeSvaChecker`.

  A property is a monitor circuit returning `Signal dom Bool`.  The
  commands below run at build time: a `#bmc` / `#kinduction` whose verdict
  differs from the stated expectation fails `lake build`.  Without z3 they
  only warn (the query is still generated), so this file builds anywhere;
  `lake exe smt-bmc-test` is the layer that requires z3 in CI.

    1. a bounded check that holds, and its k-induction proof;
    2. a true property that is NOT inductive (unreachable-state trace);
    3. a wrong property: the counterexample trace from reset;
    4. a monitor with its own state (an assumption about the past);
    5. the monitors synthesize to Verilog and as SVA checkers.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitDo

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.BmcDslTest

/-- Design under test: a mod-10 counter with enable. -/
def counter10 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  Signal.loop fun c =>
    let next := Signal.mux (c === Signal.pure 9#4) (Signal.pure 0#4) (c + 1#4)
    Signal.register 0#4 (Signal.mux en next c)

/-! ### 1. The count stays below 10 — holds, and is 1-inductive. -/

def countBelow10 (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  Signal.ultC (counter10 en) 10#4

#bmc countBelow10 20
#kinduction countBelow10 1

/-! ### 2. The count is never 12 — true, but not inductive.

    From reset the counter only visits 0..9, so BMC finds nothing.  The
    inductive step starts from ANY state: 11 satisfies "not 12" and steps
    to 12.  No k helps (the counter can hold at 10 or 11 for as long as
    `en` is low), so the property must be strengthened — `countBelow10`
    is the strengthening. -/

def countNot12 (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  Signal.mux (counter10 en === Signal.pure 12#4) (Signal.pure false) (Signal.pure true)

#bmc countNot12 20
#kinduction countNot12 3 expect failure

/-! ### 3. A wrong property: the count stays below 9.

    First violated in cycle 9, with `en` high in cycles 0..8; `#bmc`
    reports the shortest counterexample. -/

def countBelow9 (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  Signal.ultC (counter10 en) 9#4

#bmc countBelow9 20 expect violation

/-! ### 4. A monitor with state: an assumption about the inputs.

    "If `en` has never been high, the count is still 0."  The monitor
    keeps one register, `seen` (was `en` ever high before this cycle?),
    next to the design — ordinary DSL code. -/

def zeroUntilEnabled (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  let seen : Signal defaultDomain Bool :=
    Signal.loop fun s => Signal.register false (Signal.mux en (Signal.pure true) s)
  let isZero := counter10 en === Signal.pure 0#4
  -- seen ∨ isZero
  Signal.mux seen (Signal.pure true) isZero

#bmc zeroUntilEnabled 12
#kinduction zeroUntilEnabled 1

section SynthesisChecks
#synthesizeVerilog counter10
#synthesizeVerilog countBelow10
#synthesizeVerilog zeroUntilEnabled
#writeSvaChecker countBelow10 ".lake/build/gen/smt/countBelow10_sva.sv"
end SynthesisChecks

end Sparkle.Tests.BmcDslTest
