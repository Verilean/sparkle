/-
  Tutorial Step 1: a single-output counter (anonymous output).

  This is the same starting point as Tutorial.md Step 1: a single
  Signal goes in, a single Signal comes out. No modules, no record,
  no need to "unbind" anything.

  The wire generated for the counter's register is named after the
  let-binding `count` (becomes `_gen_count` in Verilog).
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step1

def counter8 {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  Signal.loop fun count =>
    let next := Signal.mux en (count + 1#8) count
    Signal.register 0#8 next

/-- Run a demo that prints 10 cycles of the counter output. -/
def runDemo : IO Unit := do
  let values := (counter8 (dom := defaultDomain) (Signal.pure true)).sample 10
  IO.println s!"Step 1 counter: {values}"

end TutorialExtended.Step1
