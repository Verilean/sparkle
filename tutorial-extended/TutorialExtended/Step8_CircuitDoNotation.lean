/-
  Tutorial Step 8: imperative-style hardware with `circuit do`.

  `circuit do` is a macro that desugars to the v2 `runCircuit{N}`
  helpers (`Sparkle.Core.CircuitMonad`).  It lets you write
  registered logic in an imperative style:

    - `let x ← Signal.reg init` declares a registered signal `x`
    - `x <~ rhs`                 sets `x`'s next-state value to `rhs`
    - `let y := rhs`             local combinational binding
    - `return expr`              the value the block returns

  Same circuit as `Signal.loop` underneath; just easier to read for
  pipelines with several registers.
-/

import Sparkle
import Sparkle.Core.CircuitDo

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step8

/-! ## Example A: simple counter

  Compare with the explicit `Signal.loop` version from Step 1:

  ```
  Signal.loop fun count =>
    let next := count + 1#8
    Signal.register 0#8 next
  ```

  The `circuit do` version drops the explicit `loop` /
  `register` boilerplate and reads top-down. -/

def counter8 {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8;
    count <~ count + 1#8;
    return count

/-! ## Example B: up/down counter — multiplexed next-state

  A second counter that increments or decrements based on `up`. -/

def upDown {dom : DomainConfig} (up : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8;
    count <~ Signal.mux up (count + 1#8) (count - 1#8);
    return count

/-! ## Example C: 3-stage pipeline (register chain)

  Three registers in a row. Each register's next-state is the
  previous one's current value, so a value entering `s0` shows up
  at `s2` three cycles later. The `let` lines compute combinational
  next-state expressions; the `<~` lines wire them into the
  `Signal.reg`-declared registers. -/

def shiftPipeline {dom : DomainConfig}
    (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let s0 ← Signal.reg 0#8;
    let s1 ← Signal.reg 0#8;
    let s2 ← Signal.reg 0#8;
    s0 <~ input;
    s1 <~ s0;
    s2 <~ s1;
    return s2

/-! ## Example D: counter with enable — combinational `let` + register

  Mixes registered state with combinational `let` bindings. The
  next-state is computed once via a `let`, then assigned. Demonstrates
  that `let x := …` (combinational binding) and `x <~ …` (registered
  next-state) coexist in the same `do` block. -/

def enabledCounter {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8;
    let incremented := count + 1#8;
    count <~ Signal.mux en incremented count;
    return count

/-! ## Demo -/

def runDemo : IO Unit := do
  -- Example A: counter increments every cycle
  let trace_a := (counter8 (dom := defaultDomain)).sample 6
  IO.println s!"counter8       : {trace_a}"

  -- Example B: up/down (always up here)
  let trace_b := (upDown (dom := defaultDomain) (Signal.pure true)).sample 6
  IO.println s!"upDown (up)    : {trace_b}"

  -- Example C: a 0xAA value entered at cycle 1 reaches s2 at cycle 4
  let trace_c := (shiftPipeline (dom := defaultDomain)
    ⟨fun t => if t == 1 then 0xAA#8 else 0#8⟩).sample 6
  IO.println s!"shiftPipeline  : {trace_c}"

  -- Example D: enabled counter — increments only when en is true.
  -- We feed `en = (cycle % 2 == 0)`, so the counter increments
  -- every other cycle.
  let trace_d := (enabledCounter (dom := defaultDomain)
    ⟨fun t => t % 2 == 0⟩).sample 8
  IO.println s!"enabled (alt)  : {trace_d}"

end TutorialExtended.Step8
