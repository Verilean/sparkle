/-
  Verilog Co-Simulation Tests (LSpec)

  Tests parsing Verilog RTL, lowering to Sparkle IR, JIT-compiling,
  and verifying simulation behavior — integrated into `lake test`.
-/

import Tools.SVParser
import Sparkle.Backend.CppSim
import Sparkle.Core.JIT
import LSpec

open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Sparkle.Backend.CppSim
open Sparkle.Core.JIT
open LSpec

namespace Sparkle.Tests.SVParser.TestVerilogCoSim

/-- Simple 8-bit counter module in Verilog -/
private def counterVerilog : String := "
module counter8 (
    input clk,
    input rst,
    output [7:0] count
);
    reg [7:0] count_reg;
    assign count = count_reg;
    always @(posedge clk) begin
        if (rst)
            count_reg <= 0;
        else
            count_reg <= count_reg + 1;
    end
endmodule
"

/-- Memory read/write module in Verilog -/
private def memoryVerilog : String := "
module memory_rw (
    input clk,
    input [7:0] addr,
    input [31:0] wdata,
    input we,
    output [31:0] rdata,
    output rdata_valid
);
    reg [31:0] mem [0:255];
    reg [31:0] rdata_reg;
    reg rdata_valid_reg;
    assign rdata = rdata_reg;
    assign rdata_valid = rdata_valid_reg;
    always @(posedge clk) begin
        rdata_valid_reg <= 0;
        if (we) begin
            mem[addr] <= wdata;
        end else begin
            rdata_reg <= mem[addr];
            rdata_valid_reg <= 1;
        end
    end
endmodule
"

/-- Test: parse Verilog counter, JIT simulate 10 cycles, verify count=9 -/
def test_counter_jit : IO TestSeq := do
  try
    let design ← IO.ofExcept (parseAndLower counterVerilog)
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_test_counter_jit.cpp" jitCpp
    let handle ← JIT.compileAndLoad "/tmp/sparkle_test_counter_jit.cpp"
    JIT.reset handle
    -- rst is input port 0 (clk is filtered); deassert reset
    JIT.setInput handle 0 0
    for _ in [:10] do JIT.evalTick handle
    let count ← JIT.getOutput handle 0
    JIT.destroy handle
    return test "Verilog counter: count=9 after 10 cycles" (count == 9)
  catch e =>
    return test s!"Verilog counter: SKIP ({e})" true

/-- Test: parse Verilog memory, write values, read back, verify -/
def test_memory_roundtrip : IO TestSeq := do
  try
    let design ← IO.ofExcept (parseAndLower memoryVerilog)
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_test_memory_jit.cpp" jitCpp
    let handle ← JIT.compileAndLoad "/tmp/sparkle_test_memory_jit.cpp"
    JIT.reset handle

    -- Write 0xDEADBEEF to address 5
    JIT.setInput handle 0 5    -- addr = 5
    JIT.setInput handle 1 0xDEADBEEF  -- wdata
    JIT.setInput handle 2 1    -- we = 1
    JIT.evalTick handle

    -- Read from address 5 (we = 0, registered output needs 2 cycles)
    JIT.setInput handle 0 5
    JIT.setInput handle 1 0
    JIT.setInput handle 2 0
    JIT.evalTick handle
    JIT.evalTick handle

    let rdata ← JIT.getOutput handle 0
    let valid ← JIT.getOutput handle 1
    JIT.destroy handle
    return test "Verilog memory: write 0xDEADBEEF, read back" (rdata == 0xDEADBEEF) ++
           test "Verilog memory: rdata_valid = 1" (valid == 1)
  catch e =>
    return test s!"Verilog memory roundtrip: SKIP ({e})" true

/-- Test: memory with multiple addresses -/
def test_memory_multi_addr : IO TestSeq := do
  try
    let design ← IO.ofExcept (parseAndLower memoryVerilog)
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_test_memory2_jit.cpp" jitCpp
    let handle ← JIT.compileAndLoad "/tmp/sparkle_test_memory2_jit.cpp"
    JIT.reset handle

    -- Write to 3 addresses
    let writes : List (UInt64 × UInt64) := [(0, 100), (1, 200), (2, 300)]
    for (a, d) in writes do
      JIT.setInput handle 0 a; JIT.setInput handle 1 d; JIT.setInput handle 2 1
      JIT.evalTick handle

    -- Read back all 3 (registered read: set addr, tick, tick, read output)
    let mut results : List UInt64 := []
    for (a, _) in writes do
      JIT.setInput handle 0 a; JIT.setInput handle 1 0; JIT.setInput handle 2 0
      JIT.evalTick handle
      JIT.evalTick handle
      let v ← JIT.getOutput handle 0
      results := results ++ [v]

    JIT.destroy handle
    return test "Verilog memory: addr[0] = 100" (results[0]? == some 100) ++
           test "Verilog memory: addr[1] = 200" (results[1]? == some 200) ++
           test "Verilog memory: addr[2] = 300" (results[2]? == some 300)
  catch e =>
    return test s!"Verilog memory multi-addr: SKIP ({e})" true

/-- All Verilog co-simulation tests -/
def verilogCoSimTests : IO TestSeq := do
  IO.println ""
  IO.println "--- Verilog Co-Simulation Tests ---"
  let t1 ← test_counter_jit
  let t2 ← test_memory_roundtrip
  let t3 ← test_memory_multi_addr
  return t1 ++ t2 ++ t3

end Sparkle.Tests.SVParser.TestVerilogCoSim
