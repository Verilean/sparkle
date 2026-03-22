/-
  Compiler Improvement Tests

  ① ~~~sig (bitwise complement) for Signal dom (BitVec n)
  ② Complex lambda with constants: (fun d => (0#24 ++ d)) <$> sig
  ③ hw_let tuple destructuring macro
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Tests.CompilerTests

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- Test ①: Bitwise complement ~~~ for BitVec signals
-- ============================================================================

/-- ~~~sig should synthesize for BitVec 8 signals -/
def testComplement8 {dom : DomainConfig}
    (a : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  ~~~a

#synthesizeVerilog testComplement8

/-- ~~~sig should synthesize for BitVec 32 signals -/
def testComplement32 {dom : DomainConfig}
    (a : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  ~~~a

#synthesizeVerilog testComplement32

-- ============================================================================
-- Test ②: Complex lambda with constants
-- ============================================================================

/-- Zero-extend 8-bit to 32-bit via lambda with constant concat -/
def testLambdaConcat {dom : DomainConfig}
    (sig : Signal dom (BitVec 8))
    : Signal dom (BitVec 32) :=
  (fun d => (0#24 ++ d : BitVec 32)) <$> sig

#synthesizeVerilog testLambdaConcat

/-- Add constant in lambda -/
def testLambdaAddConst {dom : DomainConfig}
    (sig : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  (fun x => x + 1#8) <$> sig

#synthesizeVerilog testLambdaAddConst

-- ============================================================================
-- Test ③: hw_let tuple destructuring
-- ============================================================================

/-- hw_let with 2-tuple -/
def testHwLet2 {dom : DomainConfig}
    (sig : Signal dom (BitVec 8 × BitVec 16))
    : Signal dom (BitVec 8) :=
  hw_let (a, _b) := sig;
  a

#synthesizeVerilog testHwLet2

/-- hw_let with 3-tuple -/
def testHwLet3 {dom : DomainConfig}
    (sig : Signal dom (BitVec 8 × (BitVec 16 × BitVec 32)))
    : Signal dom (BitVec 16) :=
  hw_let (_a, b, _c) := sig;
  b

#synthesizeVerilog testHwLet3

end Tests.CompilerTests
