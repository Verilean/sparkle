import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Verilog Generation Unit Tests

Tests that verify the generated Verilog code by synthesizing modules
and checking the output contains expected patterns.

Run tests: `lake env lean Tests/VerifyVerilog.lean 2>&1 | grep "✓"`
-/

-- Test definitions

-- Combinational circuits (no registers, no state)
def test_add (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + ·) <$> a <*> b

def test_sub (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· - ·) <$> a <*> b

def test_and (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· &&& ·) <$> a <*> b

def test_mux (sel : Signal Domain Bool) (a b : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  Signal.mux sel a b

def test_hierarchical_alu (op : Signal Domain Bool) (a b : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  let addResult := test_add a b
  let subResult := test_sub a b
  Signal.mux op subResult addResult

-- Sequential circuits (with flip-flops/registers)
def test_flipflop (input : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  Signal.register (0 : BitVec 16) input

def test_enabled_register (enable : Signal Domain Bool) (input : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  let next := Signal.mux enable input current
  let current := Signal.register (0 : BitVec 16) next
  current

-- ============================================================================
-- Test 1: Combinational Circuit - Addition
-- ============================================================================

#synthesizeVerilog test_add

/-!
Expected in output:
  ✓ module test_add
  ✓ endmodule
  ✓ output
  ✓ assign (combinational logic)
  ✗ NOT "always" (no sequential logic)
  ✗ NOT "posedge" (no clock)
-/

-- ============================================================================
-- Test 2: Combinational Circuit - AND Gate
-- ============================================================================

#synthesizeVerilog test_and

/-!
Expected in output:
  ✓ module test_and
  ✓ assign
  ✓ & (AND operation)
  ✗ NOT "reg" (no registers)
-/

-- ============================================================================
-- Test 3: Combinational Circuit - Multiplexer
-- ============================================================================

#synthesizeVerilog test_mux

/-!
Expected in output:
  ✓ module test_mux
  ✓ assign
  ✓ ? (ternary operator for mux)
-/

-- ============================================================================
-- Test 4: Hierarchical Combinational Circuit
-- ============================================================================

#synthesizeVerilogDesign test_hierarchical_alu

/-!
Expected in output:
  ✓ module test_hierarchical_alu
  ✓ test_add inst_test_add (module instantiation)
  ✓ test_sub inst_test_sub (module instantiation)
  ✓ _gen_addResult_ (signal routing)
  ✓ _gen_subResult_ (signal routing)
  ✓ .out( (port connections)
  ✗ NOT "always" (still combinational)
-/

-- ============================================================================
-- Test 5: Sequential Circuit - Simple Flip-Flop
-- ============================================================================

#synthesizeVerilog test_flipflop

/-!
Expected in output:
  ✓ module test_flipflop
  ✓ input logic clk (clock port)
  ✓ input logic rst (reset port)
  ✓ always @(posedge clk) (sequential logic)
  ✓ if (rst) (reset logic)
  ✓ reg (register declaration)
-/

-- ============================================================================
-- Test 6: Sequential Circuit - Enabled Register
-- ============================================================================

-- Note: This test may fail due to feedback loop limitation
-- #synthesizeVerilog test_enabled_register

/-!
If working, expected in output:
  ✓ module test_enabled_register
  ✓ always @(posedge clk)
  ✓ Multiple register stages
-/

/-!
## How to Run Tests

```bash
# Run all tests and save output
lake env lean Tests/VerifyVerilog.lean 2>&1 > test_output.txt

# Verify combinational circuits (no "always" or "reg")
echo "=== Combinational Circuit Tests ==="
grep -q "module test_add" test_output.txt && echo "✅ Test 1: Addition module" || echo "❌ FAIL"
grep -q "module test_and" test_output.txt && echo "✅ Test 2: AND gate module" || echo "❌ FAIL"
grep -q "module test_mux" test_output.txt && echo "✅ Test 3: Multiplexer module" || echo "❌ FAIL"
! grep "always" test_output.txt && echo "✅ No sequential logic in combinational tests" || echo "⚠️ Warning: 'always' found"

# Verify hierarchical instantiation
echo "=== Hierarchical Tests ==="
grep -q "test_add inst_test_add" test_output.txt && echo "✅ Test 4.1: Hierarchical instantiation" || echo "❌ FAIL"
grep -q "test_sub inst_test_sub" test_output.txt && echo "✅ Test 4.2: Sub-module instantiation" || echo "❌ FAIL"
grep -q "_gen_addResult_" test_output.txt && echo "✅ Test 4.3: Signal routing" || echo "❌ FAIL"

# Verify sequential circuits (must have "always" and clock)
echo "=== Sequential Circuit Tests ==="
grep -q "module test_flipflop" test_output.txt && echo "✅ Test 5.1: Flip-flop module" || echo "❌ FAIL"
grep -q "input logic clk" test_output.txt && echo "✅ Test 5.2: Has clock port" || echo "❌ FAIL"
grep -q "input logic rst" test_output.txt && echo "✅ Test 5.3: Has reset port" || echo "❌ FAIL"
grep -q "always @(posedge clk)" test_output.txt && echo "✅ Test 5.4: Sequential logic block" || echo "❌ FAIL"
grep -q "if (rst)" test_output.txt && echo "✅ Test 5.5: Reset logic" || echo "❌ FAIL"
```

Or use the automated test script: `./Tests/run_tests.sh`
-/
