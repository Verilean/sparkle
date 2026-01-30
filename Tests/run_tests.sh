#!/bin/bash
# Automated Verilog generation test runner
# Tests both combinational and sequential circuits

set -e

echo "╔════════════════════════════════════════╗"
echo "║  Verilog Generation Unit Tests        ║"
echo "╚════════════════════════════════════════╝"
echo

# Run synthesis and capture output
echo "Running synthesis tests..."
lake env lean Tests/VerifyVerilog.lean 2>&1 > /tmp/verilog_test_output.txt

# Verify expected patterns
PASSED=0
FAILED=0

check() {
    local name="$1"
    local pattern="$2"

    if grep -q "$pattern" /tmp/verilog_test_output.txt; then
        echo "✅ PASS: $name"
        ((PASSED++))
    else
        echo "❌ FAIL: $name - missing '$pattern'"
        ((FAILED++))
    fi
}

check_not() {
    local name="$1"
    local pattern="$2"

    if grep -q "$pattern" /tmp/verilog_test_output.txt; then
        echo "❌ FAIL: $name - should NOT contain '$pattern'"
        ((FAILED++))
    else
        echo "✅ PASS: $name"
        ((PASSED++))
    fi
}

echo "═══════════════════════════════════════════════════════"
echo "COMBINATIONAL CIRCUIT TESTS"
echo "═══════════════════════════════════════════════════════"
echo

echo "Test 1: Addition (Combinational)"
echo "────────────────────────────────────────"
check "Module declared" "module test_add"
check "Has assign statement" "assign"
check "Has addition operation" " + "
echo

echo "Test 2: AND Gate (Combinational)"
echo "────────────────────────────────────────"
check "Module declared" "module test_and"
check "Has AND operation" " & "
echo

echo "Test 3: Multiplexer (Combinational)"
echo "────────────────────────────────────────"
check "Module declared" "module test_mux"
check "Has ternary operator" " ? "
echo

echo "Test 4: Hierarchical Combinational"
echo "────────────────────────────────────────"
check "Top module" "module test_hierarchical_alu"
check "Instantiates test_add" "test_add inst_test_add"
check "Instantiates test_sub" "test_sub inst_test_sub"
check "Signal routing" "_gen_addResult_"
echo

echo "═══════════════════════════════════════════════════════"
echo "SEQUENTIAL CIRCUIT TESTS (Flip-Flops)"
echo "═══════════════════════════════════════════════════════"
echo

echo "Test 5: Flip-Flop (Sequential)"
echo "────────────────────────────────────────"
check "Module declared" "module test_flipflop"
check "Has clock port" "input logic clk"
check "Has reset port" "input logic rst"
check "Sequential block" "always @(posedge clk)"
check "Reset condition" "if (rst)"
echo

echo "═══════════════════════════════════════════════════════"
echo "NEGATIVE TESTS (Verify Differences)"
echo "═══════════════════════════════════════════════════════"
echo

echo "Test 6: Combinational Should NOT Have Sequential Logic"
echo "────────────────────────────────────────"
# Extract just the test_add module
awk '/^module test_add/,/^endmodule/' /tmp/verilog_test_output.txt > /tmp/test_add_module.txt
if grep -q "always" /tmp/test_add_module.txt; then
    echo "❌ FAIL: test_add should NOT contain 'always' block"
    ((FAILED++))
else
    echo "✅ PASS: test_add has no sequential logic"
    ((PASSED++))
fi

if grep -q "clk" /tmp/test_add_module.txt; then
    echo "❌ FAIL: test_add should NOT have clock signal"
    ((FAILED++))
else
    echo "✅ PASS: test_add has no clock"
    ((PASSED++))
fi
echo

echo "╔════════════════════════════════════════╗"
echo "║  Results: $PASSED passed, $FAILED failed          "
echo "╚════════════════════════════════════════╝"

if [ $FAILED -eq 0 ]; then
    echo "✅ ALL TESTS PASSED!"
    exit 0
else
    echo "❌ SOME TESTS FAILED"
    echo "Full output saved to: /tmp/verilog_test_output.txt"
    exit 1
fi
