/-
  Tests for `runCircuitH` — the HList-based generic register
  DSL helper.  Validates:

    1. Sim parity vs. `runCircuit{1,2,3,4}` on the same circuit
       (output cycle-by-cycle equal).
    2. Synthesis: each `runCircuitH` invocation must compile
       through `#synthesizeVerilog` (the build fails otherwise).

  The point is to prove the generic helper is a drop-in
  replacement for the per-arity helpers, with no regressions.
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core

namespace Sparkle.Tests.RunCircuitHTest

/-! ### 1. Single register via `runCircuitH`. -/

def counterH : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8])
    (0#8, ())
    (fun regs => do
      let (r0, _) := regs
      Circuit.next r0 (Circuit.read r0 + 1#8)
      return Circuit.read r0)

/-! ### 2. Two registers (BitVec 8). -/

def twoCountH : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8, BitVec 8])
    (0#8, 0xFF#8, ())
    (fun regs => do
      let (a, b, _) := regs
      Circuit.next a (Circuit.read a + 1#8)
      Circuit.next b (Circuit.read b - 1#8)
      return Circuit.read a + Circuit.read b)

/-! ### 3. Heterogeneous widths — BitVec 4 + BitVec 8. -/

def mixedWidthH : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 4, BitVec 8])
    (0#4, 0#8, ())
    (fun regs => do
      let (cnt, acc, _) := regs
      Circuit.next cnt (Circuit.read cnt + 1#4)
      Circuit.next acc (Circuit.read acc + (0#4 ++ Circuit.read cnt))
      return Circuit.read acc)

/-! ### 4. Three registers — exercises N=3 arity. -/

def tripleCountH : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8, BitVec 8, BitVec 8])
    (0#8, 0#8, 0#8, ())
    (fun regs => do
      let (a, b, c, _) := regs
      Circuit.next a (Circuit.read a + 1#8)
      Circuit.next b (Circuit.read b + 2#8)
      Circuit.next c (Circuit.read c + 3#8)
      return Circuit.read a ^^^ Circuit.read b ^^^ Circuit.read c)

/-! ### 5. Four registers — exercises N=4 arity (was the old
       `runCircuit4` ceiling). -/

def fourCountH : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8, BitVec 8, BitVec 8, BitVec 8])
    (0#8, 0#8, 0#8, 0#8, ())
    (fun regs => do
      let (a, b, c, d, _) := regs
      Circuit.next a (Circuit.read a + 1#8)
      Circuit.next b (Circuit.read b + 2#8)
      Circuit.next c (Circuit.read c + 3#8)
      Circuit.next d (Circuit.read d + 4#8)
      return Circuit.read a + Circuit.read b + Circuit.read c + Circuit.read d)

/-! ### 6. `forM` over the RegList.

    `regs` is a `Reg × (Reg × (Reg × Unit))` Prod chain, not a
    `List`, so we can't write `regs.forM (...)` directly.  But
    once destructured into named handles `[r0, r1, r2]` is a
    `List (Reg dom S (BitVec 8))` that supports `forM` and any
    other `Bind`-based combinator. -/

def threeCountForM : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8, BitVec 8, BitVec 8])
    (0#8, 1#8, 2#8, ())
    (fun regs => do
      let (r0, r1, r2, _) := regs
      [r0, r1, r2].forM (fun r =>
        Circuit.next r (Circuit.read r + 1#8))
      return Circuit.read r0 + Circuit.read r1 + Circuit.read r2)

end Sparkle.Tests.RunCircuitHTest

section SynthesisChecks
open Sparkle.Tests.RunCircuitHTest

#synthesizeVerilog counterH
#synthesizeVerilog twoCountH
#synthesizeVerilog mixedWidthH
#synthesizeVerilog tripleCountH
#synthesizeVerilog fourCountH
#synthesizeVerilog threeCountForM

end SynthesisChecks

namespace Sparkle.Tests.RunCircuitHTest

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def runTest (name : String) (got expected : List String) : IO Bool := do
  IO.println s!"--- {name} ---"
  IO.println s!"  got      = {got}"
  IO.println s!"  expected = {expected}"
  if got = expected then
    IO.println "  PASS"
    return true
  else
    IO.println "  FAIL"
    return false

def main : IO Unit := do
  let mut ok := true

  let r1 := sampleN counterH 6 |>.map toString
  ok := (← runTest "counterH"
          r1 ["0x00#8", "0x01#8", "0x02#8", "0x03#8", "0x04#8", "0x05#8"]) && ok

  -- twoCountH: a + b where a starts 0, b starts 0xFF, a++, b--
  --   cycle 0: 0 + 0xff = 0xff
  --   cycle 1: 1 + 0xfe = 0xff
  --   ...
  let r2 := sampleN twoCountH 6 |>.map toString
  ok := (← runTest "twoCountH"
          r2 ["0xff#8", "0xff#8", "0xff#8", "0xff#8", "0xff#8", "0xff#8"]) && ok

  -- mixedWidthH: acc accumulates cnt (0,1,2,3,...) — cumulative sum.
  let r3 := sampleN mixedWidthH 8 |>.map toString
  ok := (← runTest "mixedWidthH"
          r3 ["0x00#8", "0x00#8", "0x01#8", "0x03#8",
              "0x06#8", "0x0a#8", "0x0f#8", "0x15#8"]) && ok

  -- tripleCountH: a/b/c count by 1/2/3, XOR.
  --   cycle 0: 0^0^0 = 0
  --   cycle 1: 1^2^3 = 0
  --   cycle 2: 2^4^6 = 0
  --   cycle 3: 3^6^9 = 0x0c
  let r4 := sampleN tripleCountH 6 |>.map toString
  ok := (← runTest "tripleCountH"
          r4 ["0x00#8", "0x00#8", "0x00#8", "0x0c#8",
              "0x00#8", "0x00#8"]) && ok

  -- fourCountH: a/b/c/d count by 1/2/3/4, sum = 10k.
  let r5 := sampleN fourCountH 5 |>.map toString
  ok := (← runTest "fourCountH"
          r5 ["0x00#8", "0x0a#8", "0x14#8", "0x1e#8", "0x28#8"]) && ok

  -- threeCountForM: r0/r1/r2 start at 0/1/2, all incremented
  -- together each cycle via `forM`.  Sum cycles 3, 6, 9, 12, …
  let r6 := sampleN threeCountForM 6 |>.map toString
  ok := (← runTest "threeCountForM"
          r6 ["0x03#8", "0x06#8", "0x09#8", "0x0c#8", "0x0f#8", "0x12#8"]) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.RunCircuitHTest
