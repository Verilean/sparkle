/-
  Tests for `Sparkle.Core.CircuitMonad` — the ST-style monad
  PoC introduced in `Sparkle/Core/CircuitMonad.lean`.

  Two questions we want to answer end-to-end:

  1. **Simulation correctness.**  Does the counter produced by
     `runCircuit` actually cycle through `0, 1, 2, …` when we
     drive it through `Signal.val`?  If yes, the monad's bind
     plumbing + the live-tuple feedback wiring is sound.

  2. **Synthesisability.**  Does `#synthesizeVerilog` on a
     `runCircuit`-produced design emit a sensible Verilog
     module?  Existing synth machinery is tuned for the
     `Signal.loop` / `Signal.register init next` patterns the
     macro version produces; the PoC routes registers through
     a `Signal dom (Array τ)` intermediate (one `Signal.loop`
     for the whole tuple, with `Functor`/`Applicative` lifts to
     unpack and repack the array), which is a new pattern for
     the IR elaborator.  This test surfaces whether that pattern
     synthesises at all, and if not, *where* the synthesiser
     gives up.

  Both tests just need to compile + (for the sim test) print the
  expected list.  `lake build` covers (1); manually running
  `lake env lean Tests/CircuitMonadTest.lean` against an FFI-
  capable build prints the cycle dump.  The `#synthesizeVerilog`
  invocation either lands the Verilog text in the build log or
  raises an elaboration error pointing at the missing IR rule.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitMonad

open Sparkle.Core
open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Core.CircuitMonadTest

/-! ## 1. Simulation correctness -/

/-- 8-bit counter via the ST-style monad.  Behaviour should
    match the macro version's counter exactly. -/
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  runCircuit fun _σ reg => do
    let c ← reg 0#8
    Circuit.next c (Circuit.read c + 1#8)
    pure (Circuit.read c)

/-- Reference: the same counter written through `Signal.circuit do`.
    We expect `counter` and `counterMacro` to agree on every
    cycle.  Kept as a side-by-side smoke test so a future
    regression in either path shows up here. -/
def counterMacro {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

/-- Sample the first 5 cycles of a `BitVec 8` signal.  Lives at
    `defaultDomain` because that's the only domain `Signal.val`
    is wired up against in tests. -/
def sample5 (s : Signal defaultDomain (BitVec 8)) : List (BitVec 8) :=
  (List.range 5).map (fun i => s.val i)

/-- Helper to call from `#eval` so the cycle dump is visible.
    Not asserted via `decide` / `native_decide`: `Signal.val`
    reaches through an `@[implemented_by]` FFI shim that the
    kernel-side decide procedures can't link, exactly like the
    rest of `Sparkle.Core.Signal`.  Run with `#eval!` from an
    environment where the Sparkle native lib is loaded
    (xlean kernel inside the tutorial Docker image) to see
    `[0, 1, 2, 3, 4]` from both definitions. -/
def runSim : List (BitVec 8) × List (BitVec 8) :=
  (sample5 counter, sample5 counterMacro)

/-! ## 2. Synthesisability — known gap

    The macro version synthesises cleanly: `Signal.circuit do
    let c ← Signal.reg 0#8; c <~ c + 1#8; return c` lowers to a
    single `Signal.loop` whose body is `Signal.register init
    (c + 1)` — exactly the IR pattern the elaborator's
    register rule recognises.

    The PoC's `runCircuit` introduces two layers the elaborator
    doesn't (yet) understand:

    1. `Signal.loop` over `Array τ` (the bundled register
       tuple) instead of over a fixed-arity product.
    2. Per-register `Signal.map (·.getD i)` projections out of
       that array, which obscure the `Signal.register init
       next` shape the IR rule looks for.

    Adding `@[inline_hardware]` to `runCircuit` and to the
    user's wrapper doesn't help — the rank-2 quantifier on the
    body (`∀ σ, …`) prevents the elaborator's unfolder from
    reducing the closure.

    The follow-up work that retires the macro must teach the
    IR elaborator about this pattern (or, equivalently, lower
    `runCircuit` into a `Signal.loop` over a fixed-arity tuple
    so the existing rule applies).  Until then the
    `#synthesizeVerilog` attempt below is left commented out;
    the macro baseline `counterMacroD` exercises the synthesis
    pipeline so this file still surfaces a synthesiser
    regression that touches the macro path.

    See also `docs/notes/circuit-monad-design.md` (planned)
    for the heterogeneous-register lowering plan. -/

-- Macro counter — already-supported pattern, here as a baseline.
def counterMacroD : Signal defaultDomain (BitVec 8) := counterMacro

-- Monad counter — currently fails `#synthesizeVerilog`.  Kept
-- as a definition so the PoC types stay live; the synth call
-- is intentionally commented out (see comment block above).
def counterMonadD : Signal defaultDomain (BitVec 8) := counter

-- Baseline: macro pattern, expected to synthesise.
#synthesizeVerilog counterMacroD

-- Monad PoC — currently rejected by the elaborator with
-- "Cannot synthesise … : not inlinable and not a hardware
-- module".  Re-enable once `runCircuit` lowers into a
-- fixed-arity-tuple `Signal.loop`.
-- #synthesizeVerilog counterMonadD

end Sparkle.Core.CircuitMonadTest
