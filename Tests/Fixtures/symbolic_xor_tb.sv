`ifndef TEST_WIDTH
`define TEST_WIDTH 3
`endif

module tb;
  localparam integer WIDTH = `TEST_WIDTH;

  logic [WIDTH-1:0] lhs;
  logic [WIDTH-1:0] rhs;
  wire [WIDTH-1:0] out;

  symbolicXor #(.W(WIDTH)) dut (
    ._gen_lhs(lhs),
    ._gen_rhs(rhs),
    .out(out)
  );

  initial begin
    lhs = {WIDTH{1'b1}};
    rhs = {{(WIDTH-1){1'b0}}, 1'b1};
    #1;
    if (out !== (lhs ^ rhs)) begin
      $display("FAIL symbolicXor width=%0d lhs=%h rhs=%h out=%h", WIDTH, lhs, rhs, out);
      $fatal(1);
    end
    $display("PASS symbolicXor width=%0d out=%h", WIDTH, out);
    $finish;
  end
endmodule
