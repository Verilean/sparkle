module symbolic_parameter_behavior_tb;
  logic [2:0] concat_hi;
  logic [4:0] concat_lo;
  wire [7:0] concat_out;

  logic [17:0] slice_in;
  wire [16:0] slice_out;

  logic [64:0] zext_in;
  wire [65:0] zext_out;

  symbolicConcat #(.HI(3), .LO(5)) concat_dut (
    ._gen_hi(concat_hi),
    ._gen_lo(concat_lo),
    .out(concat_out)
  );

  symbolicSliceLow #(.W(17)) slice_dut (
    ._gen_x(slice_in),
    .out(slice_out)
  );

  symbolicZeroExtend #(.W(65)) zext_dut (
    ._gen_x(zext_in),
    .out(zext_out)
  );

  initial begin
    concat_hi = 3'b101;
    concat_lo = 5'b10011;
    slice_in = {1'b1, 17'h1a55a};
    zext_in = {1'b1, 64'h0123456789abcdef};
    #1;

    if (concat_out !== {concat_hi, concat_lo})
      $fatal(1, "symbolic concat override failed");
    if (slice_out !== 17'h1a55a)
      $fatal(1, "symbolic slice override failed");
    if (zext_out !== {1'b0, zext_in})
      $fatal(1, "symbolic zero extension override failed");

    $display("SYMBOLIC_PARAMETER_BEHAVIOR_PASS");
    $finish;
  end
endmodule
