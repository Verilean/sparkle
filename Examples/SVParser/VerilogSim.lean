/-
  Verilog Co-Simulation Example

  Demonstrates parsing a Verilog memory module and simulating it via
  Sparkle's JIT pipeline:

    Verilog RTL → [SV Parser] → Sparkle IR → [CppSim] → C++ → [JIT] → Simulation

  The Verilog module is a simple read/write memory with:
  - 256 x 32-bit words
  - Synchronous write (posedge clk, write enable)
  - Combinational read
  - UART-style output port (active for 1 cycle after read)

  From Lean, we:
  1. Parse the Verilog string
  2. Lower to Sparkle IR
  3. Generate C++ and JIT-compile
  4. Write values into memory
  5. Read them back and verify
-/

import Tools.SVParser
import Sparkle.Backend.CppSim
import Sparkle.Core.JIT

open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Sparkle.Backend.CppSim
open Sparkle.Core.JIT

/-- A simple Verilog memory module with read/write ports -/
def verilogMemoryModule : String := "
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

/-- Parse Verilog, JIT-compile, write/read memory, verify round-trip -/
def main : IO UInt32 := do
  IO.println "=== Verilog Memory Co-Simulation Example ==="

  -- Step 1: Parse and lower
  IO.print "  Parsing Verilog... "
  let design ← IO.ofExcept (parseAndLower verilogMemoryModule)
  IO.println "OK"

  -- Step 2: Generate C++ and JIT-compile
  IO.print "  JIT compiling... "
  let jitCpp := toCppSimJIT design
  let jitPath := "/tmp/sparkle_memory_rw_jit.cpp"
  IO.FS.writeFile jitPath jitCpp
  let handle ← JIT.compileAndLoad jitPath
  IO.println "OK"

  -- Step 3: Reset
  JIT.reset handle

  -- Step 4: Write test values into memory via the write port
  IO.print "  Writing 4 values... "
  let testData : List (UInt32 × UInt32) := [
    (0, 0xDEADBEEF), (1, 0xCAFEBABE), (10, 42), (255, 0x12345678)
  ]
  for (addr, data) in testData do
    -- Set inputs: addr, wdata, we=1
    JIT.setInput handle 0 addr.toUInt64   -- addr
    JIT.setInput handle 1 data.toUInt64   -- wdata
    JIT.setInput handle 2 1               -- we = 1
    JIT.evalTick handle
  IO.println "OK"

  -- Step 5: Read back and verify
  -- The memory read is registered: set addr+we=0, tick, then read output
  IO.print "  Reading back... "
  let mut passed := true
  for (addr, expected) in testData do
    -- Set inputs: addr, we=0 (read mode)
    JIT.setInput handle 0 addr.toUInt64
    JIT.setInput handle 1 0
    JIT.setInput handle 2 0   -- we = 0
    JIT.evalTick handle        -- latch read address
    JIT.evalTick handle        -- output valid
    let rdata ← JIT.getOutput handle 0       -- rdata
    let valid ← JIT.getOutput handle 1        -- rdata_valid
    if rdata.toUInt32 != expected || valid != 1 then
      IO.println s!"\n    MISMATCH at addr {addr}: got 0x{Nat.toDigits 16 rdata.toNat |> String.ofList}, expected 0x{Nat.toDigits 16 expected.toNat |> String.ofList}"
      passed := false

  JIT.destroy handle

  if passed then
    IO.println "ALL MATCH"
    IO.println "\n  Result: PASS — Verilog memory round-trip verified via JIT"
    return 0
  else
    IO.println "\n  Result: FAIL"
    return 1
