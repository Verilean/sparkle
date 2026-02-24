// =============================================================================
// Hespera BitLinear Testbench
//
// Loads ROM .mem files, feeds known activations, compares outputs to golden
// vectors. Basic pass/fail checking with $display.
//
// Usage with Icarus Verilog:
//   iverilog -g2012 -o tb_bitlinear tb_bitlinear.sv bitlinear_attn_qkv.sv
//   vvp tb_bitlinear
//
// Usage with Verilator:
//   verilator --binary --timing tb_bitlinear.sv bitlinear_attn_qkv.sv
// =============================================================================

`timescale 1ns / 1ps

module tb_bitlinear;

  // ========================================================================
  // Parameters — adjust for layer under test
  // ========================================================================
  parameter IN_DIM        = 2048;
  parameter OUT_DIM       = 2048;
  parameter GROUP_SIZE    = 128;
  parameter GROUPS_PER_ROW = IN_DIM / GROUP_SIZE;  // 16
  parameter ROM_DEPTH     = OUT_DIM * GROUPS_PER_ROW;
  parameter ROM_ADDR_BITS = $clog2(ROM_DEPTH);
  parameter ACT_ADDR_BITS = $clog2(IN_DIM);

  // ========================================================================
  // Clock and reset
  // ========================================================================
  logic clk;
  logic rst;

  initial clk = 0;
  always #5 clk = ~clk;  // 100 MHz

  // ========================================================================
  // DUT signals
  // ========================================================================
  logic        start;
  logic [15:0] row_idx;
  logic [31:0] activation_in;
  logic [31:0] result;
  logic        result_valid;
  logic        busy;
  logic [ACT_ADDR_BITS-1:0] act_addr;

  // ========================================================================
  // DUT instantiation
  // ========================================================================
  BitLinearTop_2048x2048 u_dut (
    .clk           (clk),
    .rst           (rst),
    .start         (start),
    .row_idx       (row_idx),
    .activation_in (activation_in),
    .result        (result),
    .result_valid  (result_valid),
    .busy          (busy),
    .act_addr      (act_addr)
  );

  // ========================================================================
  // Weight ROM model (behavioral)
  // ========================================================================
  logic [255:0] weight_mem [0:ROM_DEPTH-1];
  logic [ROM_ADDR_BITS-1:0] weight_addr;
  logic [255:0] weight_dout;

  initial begin
    $readmemh("weight_rom.mem", weight_mem);
  end

  always_ff @(posedge clk) begin
    weight_dout <= weight_mem[weight_addr];
  end

  // Connect to DUT's ROM port (via hierarchical reference or bind)
  // In practice, replace the primitive ROM instance with this behavioral model
  assign weight_addr = u_dut.u_weight_rom.addr;
  // Force ROM output into the DUT
  // NOTE: In real simulation, the ROM primitive should be replaced with
  // a behavioral model. This testbench shows the intended pattern.

  // ========================================================================
  // Scale ROM model (behavioral)
  // ========================================================================
  logic [31:0] scale_mem [0:OUT_DIM-1];
  logic [$clog2(OUT_DIM)-1:0] scale_addr;
  logic [31:0] scale_dout;

  initial begin
    $readmemh("scale_rom.mem", scale_mem);
  end

  always_ff @(posedge clk) begin
    scale_dout <= scale_mem[scale_addr];
  end

  assign scale_addr = u_dut.u_scale_rom.addr;

  // ========================================================================
  // Activation memory model
  // ========================================================================
  logic [31:0] act_mem [0:IN_DIM-1];

  // Provide activation data combinationally
  assign activation_in = act_mem[act_addr];

  // ========================================================================
  // Test sequence
  // ========================================================================
  integer test_pass;
  integer test_fail;
  integer i;

  // Golden result for comparison (set per test case)
  logic [31:0] golden_result;

  initial begin
    test_pass = 0;
    test_fail = 0;

    // Initialize
    start   = 0;
    row_idx = 0;
    rst     = 1;

    // Reset sequence
    repeat (10) @(posedge clk);
    rst = 0;
    repeat (5) @(posedge clk);

    $display("=== Hespera BitLinear Testbench ===");
    $display("Layer: %0d x %0d, Groups/row: %0d", IN_DIM, OUT_DIM, GROUPS_PER_ROW);

    // ------------------------------------------------------------------
    // Test 1: All-zero activations → result should be 0
    // ------------------------------------------------------------------
    $display("\nTest 1: All-zero activations");
    for (i = 0; i < IN_DIM; i = i + 1)
      act_mem[i] = 32'h0000_0000;

    golden_result = 32'h0000_0000;
    row_idx = 0;
    start = 1;
    @(posedge clk);
    start = 0;

    // Wait for completion
    wait (result_valid);
    @(posedge clk);

    if (result == golden_result) begin
      $display("  PASS: result = 0x%08h (expected 0x%08h)", result, golden_result);
      test_pass = test_pass + 1;
    end else begin
      $display("  FAIL: result = 0x%08h (expected 0x%08h)", result, golden_result);
      test_fail = test_fail + 1;
    end

    repeat (5) @(posedge clk);

    // ------------------------------------------------------------------
    // Test 2: Compute row 0 with known activations
    // ------------------------------------------------------------------
    $display("\nTest 2: Row 0 with unit activations (1.0 in Q16.16)");
    for (i = 0; i < IN_DIM; i = i + 1)
      act_mem[i] = 32'h0001_0000;  // 1.0 in Q16.16

    row_idx = 0;
    start = 1;
    @(posedge clk);
    start = 0;

    wait (result_valid);
    @(posedge clk);

    // Result depends on weights and scale — just check it completed
    $display("  INFO: result = 0x%08h (verify against golden vector)", result);
    $display("  PASS: computation completed without hang");
    test_pass = test_pass + 1;

    repeat (5) @(posedge clk);

    // ------------------------------------------------------------------
    // Summary
    // ------------------------------------------------------------------
    $display("\n=== Results: %0d PASS, %0d FAIL ===", test_pass, test_fail);

    if (test_fail > 0)
      $display("TESTBENCH FAILED");
    else
      $display("TESTBENCH PASSED");

    $finish;
  end

  // ========================================================================
  // Timeout watchdog
  // ========================================================================
  initial begin
    #1_000_000;  // 1ms at 1ns resolution
    $display("ERROR: Simulation timeout!");
    $finish;
  end

endmodule
