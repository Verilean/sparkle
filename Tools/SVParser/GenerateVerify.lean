/-
  Verilog → Lean Verification File Generator

  Parses Verilog source, extracts a semantic model, and writes
  a Lean file to `Sparkle/Verification/Generated/` that can be
  imported by proof files.
-/

import Tools.SVParser
import Tools.SVParser.Verify

open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Tools.SVParser.Verify

/-- Counter with enable — the Verilog to verify -/
def counter8EnVerilog : String := "
module counter8_en (
    input clk,
    input rst,
    input en,
    output [7:0] count
);
    reg [7:0] count_reg;
    assign count = count_reg;
    always @(posedge clk) begin
        if (rst)
            count_reg <= 0;
        else if (en)
            count_reg <= count_reg + 1;
    end
endmodule
"

def main : IO UInt32 := do
  let design ← IO.ofExcept (parseAndLower counter8EnVerilog)
  match design.modules.head? with
  | none =>
    IO.eprintln "ERROR: no modules found"
    return 1
  | some m =>
    let leanSrc := moduleToLean m
    let outPath := "Sparkle/Verification/Generated/Counter8.lean"
    IO.FS.createDirAll "Sparkle/Verification/Generated"
    IO.FS.writeFile outPath leanSrc
    IO.println s!"Generated: {outPath}"
    return 0
