/-
  Sim + synth round-trip tests for `Signal.loop` written
  directly (no `Signal.circuit do` sugar).

  Why this file exists.  The `Signal.circuit do` macro
  (`Sparkle/Core/Signal.lean`) and the ST-style monad PoC
  (`Sparkle/Core/CircuitMonad.lean`) are well covered by
  `Tests/CircuitIfTest.lean` and `Tests/CircuitMonadSmoke.lean`
  respectively.  But the most primitive form — the user
  writing `Signal.loop` and `Signal.register` calls by hand,
  the way most existing IP code (`IP/RV32/SoC.lean` and
  friends) is written — only had ad-hoc coverage scattered
  across `Tests/SynthesisTests.lean` and the tutorial
  smoke tests.  This file gives it a single, named home that
  exercises the same three properties the higher-level forms
  are tested for:

    1. simulation correctness (cycle-by-cycle Signal.val
       sampling matches the obvious reference output)
    2. Verilog synthesis (the `#synthesizeVerilog` call
       produces a module the IR elaborator accepts)
    3. equivalence to the `Signal.circuit do` macro form for
       circuits where both forms can express the same logic

  Run sim: `lake exe signal-loop-test`
  Run synth: covered by `lake build Tests.SignalLoopTest`
  (the `#synthesizeVerilog` invocations error out the build
  if any module no longer synthesises).
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.SignalLoopTest

/-! ### 1. Plain counter — single-register `Signal.loop` -/

/-- `Signal.loop`'s callback gets the previous-cycle output as
    its argument; here we feed `count + 1` into a register
    initialised at 0.  Equivalent to `Signal.circuit do { let
    c ← Signal.reg 0#8; c <~ c + 1#8; return c }`. -/
def counterLoop : Signal defaultDomain (BitVec 8) :=
  Signal.loop fun count =>
    Signal.register 0#8 (count + 1#8)

/-- Same circuit through the macro DSL, for the equivalence
    check. -/
def counterDSL : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

/-! ### 2. Counter with enable — `Signal.mux` inside `loop` -/

/-- Increment only when `en` is high; otherwise hold. -/
def counterEnableLoop (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.loop fun count =>
    Signal.register 0#8 (Signal.mux en (count + 1#8) count)

def counterEnableDSL (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let c ← Signal.reg 0#8
    c <~ Signal.mux en (c + 1#8) c
    return c

/-! ### Duplicate-assignment detection

    The macro raises an error if the user writes the same
    register's `<~` more than once at the same statement
    level — earlier writes used to vanish silently into the
    loop body because the macro's per-register scan stopped
    at the first match.  We verify the error path via
    `#guard_msgs`; uncommenting the macro invocation should
    surface the duplicate-assignment message.

      Signal.circuit do
        let c ← Signal.reg 0#8
        c <~ 0#8              -- shadowed by the next line
        c <~ c + 1#8
        return c

    Don't uncomment — the macro `Macro.throwError` is a hard
    error, so this block would fail `lake build`.  Re-enable
    via `#guard_msgs` once the macro evolves to emit a
    softer `Macro.throwWarning` form. -/

/-! ### 3. Shift register — chained `Signal.register` (no
       feedback, but the same Signal.loop shape) -/

/-- 4-stage byte-wide shift register driven by `input`.  Each
    register output feeds the next; the loop reads cycle-N
    outputs from the previous stage. -/
def shift4Loop (input : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 (Signal.register 0#8
    (Signal.register 0#8 (Signal.register 0#8 input)))

/-! ### Verilog synthesis smoke

    Build-time check that each `Signal.loop`-direct form goes
    through the IR elaborator's wire translation cleanly.  The
    output Verilog lands in the build log; CI only needs the
    build to succeed. -/
end Sparkle.Tests.SignalLoopTest

section SynthesisChecks
open Sparkle.Tests.SignalLoopTest

#synthesizeVerilog counterLoop
#synthesizeVerilog counterDSL
#synthesizeVerilog counterEnableLoop
#synthesizeVerilog counterEnableDSL
#synthesizeVerilog shift4Loop

end SynthesisChecks

namespace Sparkle.Tests.SignalLoopTest

/-! ### Runtime drivers -/

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def pulseAt (cycles : List Nat) : Signal defaultDomain Bool :=
  ⟨fun t => cycles.contains t⟩

def runTest (name : String) (got expected : List String) : IO Bool := do
  IO.println s!"--- {name} ---"
  IO.println s!"  got      = {got}"
  IO.println s!"  expected = {expected}"
  if got = expected then
    IO.println "  PASS"
    return true
  else do
    IO.println "  FAIL"
    return false

def main : IO Unit := do
  let mut ok := true

  -- 1. counterLoop: 0, 1, 2, …
  let r1 := sampleN counterLoop 6 |>.map toString
  ok := (← runTest "counterLoop"
          r1 ["0x00#8", "0x01#8", "0x02#8", "0x03#8", "0x04#8", "0x05#8"]) && ok

  -- 1b. counterDSL must agree with counterLoop.
  let r1b := sampleN counterDSL 6 |>.map toString
  ok := (← runTest "counterDSL ≡ counterLoop"
          r1b ["0x00#8", "0x01#8", "0x02#8", "0x03#8", "0x04#8", "0x05#8"]) && ok

  -- 2. counterEnable: enable=high only on odd cycles.
  let oddEn : Signal defaultDomain Bool := ⟨fun t => t % 2 == 1⟩
  --  cycle 0: count=0, en=0 → next=count=0,    register at cycle 1 reads 0
  --  cycle 1: count=0, en=1 → next=1,          register at cycle 2 reads 1
  --  cycle 2: count=1, en=0 → next=count=1,    register at cycle 3 reads 1
  --  cycle 3: count=1, en=1 → next=2,          register at cycle 4 reads 2
  --  cycle 4: count=2, en=0 → next=2,          register at cycle 5 reads 2
  --  cycle 5: count=2, en=1 → next=3,          register at cycle 6 reads 3
  let r2 := sampleN (counterEnableLoop oddEn) 6 |>.map toString
  ok := (← runTest "counterEnableLoop"
          r2 ["0x00#8", "0x00#8", "0x01#8", "0x01#8", "0x02#8", "0x02#8"]) && ok

  -- 2b. DSL must agree.
  let r2b := sampleN (counterEnableDSL oddEn) 6 |>.map toString
  ok := (← runTest "counterEnableDSL ≡ counterEnableLoop"
          r2b ["0x00#8", "0x00#8", "0x01#8", "0x01#8", "0x02#8", "0x02#8"]) && ok

  -- 3. shift4: input arriving at cycle 0 takes 4 cycles to
  --    reach the output.  Drive `input = cycle`, sample early.
  --    cycle 0: out=0 (regs all 0)
  --    cycle 1: out=0 (stage-4 still 0; stage-1 got cycle 0)
  --    cycle 2: out=0
  --    cycle 3: out=0
  --    cycle 4: out=0 (cycle 0 reaches the last register)
  --    cycle 5: out=1
  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => (t.toUInt8.toBitVec)⟩
  let r3 := sampleN (shift4Loop input) 6 |>.map toString
  ok := (← runTest "shift4Loop"
          r3 ["0x00#8", "0x00#8", "0x00#8", "0x00#8", "0x00#8", "0x01#8"]) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.SignalLoopTest

def main : IO Unit := Sparkle.Tests.SignalLoopTest.main
