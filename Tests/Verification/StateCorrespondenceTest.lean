/-
  State correspondence and duplication-freedom, on the circuits the
  certified chain already proves.

  The trace theorems are invariant under duplicated hardware: two copies
  of one register hold the same value at every cycle, so the emitted
  module still computes the right thing while using twice the area.
  That is why the three duplication bugs on this branch were found by
  eye rather than by a theorem.  These checks close that hole, and the
  negative section below pins that they are non-vacuous — each one fails
  on the shape of an actual historical bug.
-/
import Tests.Verification.DeepElabRealIP
import Sparkle.IR.StateCorrespondence

open Sparkle.Tests.DeepElabRealIP Sparkle.IR.StateCorrespondence Sparkle.IR.AST

set_option maxRecDepth 100000

namespace Sparkle.Tests.StateCorrespondenceTest

/-! ### The shipping circuits the deep route proves

State counts are checked against the DSL definitions by hand here (the
generator does not yet emit the DSL-side slot list — that is the next
step); duplication-freedom is checked outright. -/

section Shipping

-- crc32Engine: 1 DSL register
example : regCount crc32Engine_deep_body = 1 := by decide
example : memCount crc32Engine_deep_body = 0 := by decide
#guard noDuplicateDefs crc32Engine_deep_body = true

-- uartTxHW: 4 DSL registers (10/4/16-bit + Bool busy)
example : regCount uartTxHW_deep_body = 4 := by decide
example : memCount uartTxHW_deep_body = 0 := by decide
#guard noDuplicateDefs uartTxHW_deep_body = true

-- regFile: 2 DSL registers + 1 Signal.memory.  This is the circuit the
-- memory-duplication bug would have hit: one DSL memory, one BRAM.
example : regCount regFile_deep_body = 2 := by decide
example : memCount regFile_deep_body = 1 := by decide
#guard noDuplicateDefs regFile_deep_body = true

-- spiMasterHW: 7 DSL registers — the widest state chain on the route
example : regCount spiMasterHW_deep_body = 7 := by decide
example : memCount spiMasterHW_deep_body = 0 := by decide
#guard noDuplicateDefs spiMasterHW_deep_body = true

-- transferIdTrackerHW: 3 DSL registers
example : regCount transferIdTrackerHW_deep_body = 3 := by decide
#guard noDuplicateDefs transferIdTrackerHW_deep_body = true

-- frameAccumulatorHW: 4 DSL registers
example : regCount frameAccumulatorHW_deep_body = 4 := by decide
#guard noDuplicateDefs frameAccumulatorHW_deep_body = true

end Shipping

/-! ### Non-vacuity: the checks reject the historical bug shapes

Without this section a passing check proves nothing — a checker that
accepts everything would look identical above. -/

section Negative

private def wOf : String → Nat := fun n => if n == "a" || n == "b" then 8 else 4

-- BUG SHAPE 1 (nested `circuit do`): one DSL register block emitted
-- TWICE.  `closedLoopCircuit` had five registers for its three.
private def dupReg : List Stmt :=
  [ .register "a" "clk" ("rst", .synchronous) (.ref "w") 0,
    .register "b" "clk" ("rst", .synchronous) (.ref "w") 0 ]

#guard noDuplicateDefs dupReg = false
#guard stateCorrespondence wOf [Slot.reg 8 0] dupReg = false
-- two DSL registers legitimately emitting two: accepted
#guard stateCorrespondence wOf [Slot.reg 8 0, Slot.reg 8 0] dupReg = true

-- BUG SHAPE 2 (`Signal.memory` in a `circuit do`): one DSL memory
-- emitted as two BRAMs.
private def dupMem : List Stmt :=
  [ .memory "m1" 4 8 "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "r1" false [] [],
    .memory "m2" 4 8 "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "r2" false [] [] ]

#guard noDuplicateDefs dupMem = false
#guard stateCorrespondence wOf [Slot.mem 4 8] dupMem = false

-- The opposite failure — emitted state MISSING — is caught too.
#guard stateCorrespondence wOf [Slot.reg 8 0, Slot.reg 8 0]
  [Stmt.register "a" "clk" ("rst", .synchronous) (.ref "w") 0] = false

-- Distinct logic is not duplication; repeated logic is.
#guard noDuplicateDefs
  [ Stmt.assign "x" (.op .add [.ref "p", .ref "q"]),
    Stmt.assign "y" (.op .sub [.ref "p", .ref "q"]) ] = true
#guard noDuplicateDefs
  [ Stmt.assign "x" (.op .add [.ref "p", .ref "q"]),
    Stmt.assign "y" (.op .add [.ref "p", .ref "q"]) ] = false

-- A plain alias is NOT duplicated hardware (measured: `crc32Engine`
-- carries one wire under eight names; the optimizer's copy propagation
-- collapses them).  Counting aliases would make every circuit fail.
#guard noDuplicateDefs
  [ Stmt.assign "x" (.ref "w"), Stmt.assign "y" (.ref "w"),
    Stmt.assign "z" (.ref "w") ] = true

end Negative

def main : IO Unit :=
  IO.println "state correspondence: 6 shipping circuits, duplication-free (build-time)"

end Sparkle.Tests.StateCorrespondenceTest
