`timescale 1ns / 1ps

// =============================================================================
// Hespera RTL ↔ Lean Spec Co-Validation Testbench
//
// Tests the BitNet_SoC_TM_2L_4d (2 layers, dim=4, time-multiplexed) against
// expected values computed from the Lean spec.
//
// The SoC is a SCALAR model: it broadcasts a single Q16.16 input x to all 4
// weight positions. So the dot product becomes: sum(weights) * x.
//
// Weight summary (from Lean Tests/TestSoC.lean):
//   Layer 0: gate=[+1,-1,0,+1] up=[-1,+1,+1,0] down=[+1,0,-1,+1]
//            all scales = 1.0 (Q8.24 = 0x01000000)
//   Layer 1: gate=[0,+1,-1,-1] up=[+1,0,0,+1] down=[-1,+1,+1,0]
//            gateScale=0.5, upScale=1.0, downScale=0.75
//
// Usage:
//   iverilog -g2012 -o tb_soc tb_soc_2L_4d.sv bitnet_soc_tm_2L_4d.sv \
//     dynamic_bitlinear_4.sv scale_multiply.sv relusq.sv elem_mul.sv residual_add.sv
//   vvp tb_soc
// =============================================================================

module tb_soc_2L_4d;

  logic clk, rst, start;
  logic [31:0] x_in;
  logic [31:0] y_out;
  logic done;

  // DUT
  BitNet_SoC_TM_2L_4d u_soc (
    .clk(clk), .rst(rst), .start(start),
    .x_in(x_in), .y_out(y_out), .done(done)
  );

  // Clock: 100 MHz
  initial clk = 0;
  always #5 clk = ~clk;

  // Test infrastructure
  integer test_pass, test_fail;

  task automatic run_soc(
    input [31:0] input_val,
    output [31:0] output_val
  );
    begin
      x_in = input_val;
      start = 1;
      @(posedge clk);
      start = 0;

      // Wait for done
      @(posedge done);
      @(posedge clk);
      output_val = y_out;

      // Let state machine return to IDLE
      repeat (3) @(posedge clk);
    end
  endtask

  // Helper: convert Q16.16 to display format
  function automatic real q16_to_real(input [31:0] val);
    if (val[31])
      q16_to_real = -($itor(~val + 1) / 65536.0);
    else
      q16_to_real = $itor(val) / 65536.0;
  endfunction

  // Test vectors
  logic [31:0] result;
  real result_f, expected_f;

  initial begin
    test_pass = 0;
    test_fail = 0;
    start = 0;
    x_in = 0;
    rst = 1;

    repeat (10) @(posedge clk);
    rst = 0;
    repeat (5) @(posedge clk);

    $display("================================================================");
    $display("  Hespera RTL Co-Validation: BitNet_SoC_TM_2L_4d");
    $display("  Architecture: TimeMultiplexed, 2 layers, dim=4 (scalar)");
    $display("================================================================");
    $display("");

    // ===================================================================
    // Test 1: x = 2.0 (Q16.16 = 0x00020000)
    //
    // Layer 0 (all scales=1.0, broadcast):
    //   gate_sum=1*x=2.0 → relu²=4.0, up_sum=1*x=2.0
    //   mixed=4.0*2.0=8.0, down_sum=1*8.0=8.0
    //   resid=2.0+8.0=10.0
    // Layer 1 (gate_scale=0.5):
    //   gate_sum=-1*10.0=-10.0 → scaled=-5.0 → relu²=0 (negative!)
    //   → gate-kill → resid=10.0+0=10.0
    // Expected: 10.0 = 0x000A0000
    // ===================================================================
    $display("--- Test 1: x = 2.0 ---");
    run_soc(32'h0002_0000, result);
    result_f = q16_to_real(result);
    expected_f = 10.0;

    $display("  Input:    0x%08h (%.4f)", 32'h0002_0000, 2.0);
    $display("  Output:   0x%08h (%.4f)", result, result_f);
    $display("  Expected: 0x%08h (%.4f)", 32'h000A_0000, expected_f);

    if (result == 32'h000A_0000) begin
      $display("  [PASS] Exact match");
      test_pass = test_pass + 1;
    end else begin
      $display("  [FAIL] Mismatch!");
      test_fail = test_fail + 1;
    end
    $display("");

    // ===================================================================
    // Test 2: x = 0.5 (Q16.16 = 0x00008000)
    //
    // Layer 0:
    //   gate=0.5 → relu²=0.25, up=0.5
    //   mixed=0.25*0.5=0.125, down=0.125
    //   resid=0.5+0.125=0.625
    // Layer 1:
    //   gate=-1*0.625*0.5=-0.3125 → relu²=0 (negative!)
    //   → gate-kill → resid=0.625+0=0.625
    // Expected: 0.625 = 0x0000A000
    // ===================================================================
    $display("--- Test 2: x = 0.5 ---");
    run_soc(32'h0000_8000, result);
    result_f = q16_to_real(result);
    expected_f = 0.625;

    $display("  Input:    0x%08h (%.4f)", 32'h0000_8000, 0.5);
    $display("  Output:   0x%08h (%.4f)", result, result_f);
    $display("  Expected: 0x%08h (%.4f)", 32'h0000_A000, expected_f);

    if (result == 32'h0000_A000) begin
      $display("  [PASS] Exact match");
      test_pass = test_pass + 1;
    end else begin
      $display("  [FAIL] Mismatch!");
      test_fail = test_fail + 1;
    end
    $display("");

    // ===================================================================
    // Test 3: x = -1.0 (Q16.16 = 0xFFFF0000)
    //
    // Layer 0:
    //   gate=1*(-1.0)=-1.0 → relu²=0 (negative!)
    //   → gate-kill → resid=-1.0+0=-1.0
    // Layer 1:
    //   gate=-1*(-1.0)=1.0 → scaled=0.5 → relu²=0.25
    //   up=2*(-1.0)=-2.0 → scaled=-2.0
    //   mixed=0.25*(-2.0)=-0.5
    //   down=1*(-0.5)=-0.5 → scaled=-0.5*0.75=-0.375
    //   resid=-1.0+(-0.375)=-1.375
    // Expected: -1.375 = -(1.375 * 65536) = -90112 = 0xFFFF_A000
    //   Actually: -1.375 in Q16.16:
    //   1.375 = 0x16000, so -1.375 = -0x16000 = 0xFFFE_A000
    // ===================================================================
    $display("--- Test 3: x = -1.0 ---");
    run_soc(32'hFFFF_0000, result);
    result_f = q16_to_real(result);
    expected_f = -1.375;

    $display("  Input:    0x%08h (%.4f)", 32'hFFFF_0000, -1.0);
    $display("  Output:   0x%08h (%.4f)", result, result_f);
    $display("  Expected: 0xFFFE_A000 (%.4f)", expected_f);

    if (result == 32'hFFFE_A000) begin
      $display("  [PASS] Exact match");
      test_pass = test_pass + 1;
    end else begin
      $display("  [FAIL] Mismatch!");
      test_fail = test_fail + 1;
    end
    $display("");

    // ===================================================================
    // Test 4: x = 1.0 (Q16.16 = 0x00010000)
    //
    // Layer 0:
    //   gate=1.0 → relu²=1.0, up=1.0
    //   mixed=1.0*1.0=1.0, down=1.0
    //   resid=1.0+1.0=2.0
    // Layer 1:
    //   gate=-1*2.0=-2.0 → scaled=-1.0 → relu²=0 (negative!)
    //   → gate-kill → resid=2.0+0=2.0
    // Expected: 2.0 = 0x00020000
    // ===================================================================
    $display("--- Test 4: x = 1.0 ---");
    run_soc(32'h0001_0000, result);
    result_f = q16_to_real(result);
    expected_f = 2.0;

    $display("  Input:    0x%08h (%.4f)", 32'h0001_0000, 1.0);
    $display("  Output:   0x%08h (%.4f)", result, result_f);
    $display("  Expected: 0x%08h (%.4f)", 32'h0002_0000, expected_f);

    if (result == 32'h0002_0000) begin
      $display("  [PASS] Exact match");
      test_pass = test_pass + 1;
    end else begin
      $display("  [FAIL] Mismatch!");
      test_fail = test_fail + 1;
    end
    $display("");

    // ===================================================================
    // Test 5: x = 0 (Q16.16 = 0x00000000)
    //
    // Everything is zero → resid = 0 + 0 = 0 through both layers
    // Expected: 0
    // ===================================================================
    $display("--- Test 5: x = 0.0 ---");
    run_soc(32'h0000_0000, result);
    result_f = q16_to_real(result);
    expected_f = 0.0;

    $display("  Input:    0x%08h (%.4f)", 32'h0000_0000, 0.0);
    $display("  Output:   0x%08h (%.4f)", result, result_f);
    $display("  Expected: 0x%08h (%.4f)", 32'h0000_0000, expected_f);

    if (result == 32'h0000_0000) begin
      $display("  [PASS] Exact match");
      test_pass = test_pass + 1;
    end else begin
      $display("  [FAIL] Mismatch!");
      test_fail = test_fail + 1;
    end
    $display("");

    // ===================================================================
    // Bonus: Feed "hello" characters (ASCII as Q16.16)
    // These will overflow the toy model but show the SoC processes data
    // ===================================================================
    $display("--- Bonus: \"hello\" (ASCII as Q16.16, expect overflow) ---");
    begin
      logic [31:0] hello_chars [0:4];
      integer i;
      hello_chars[0] = 32'h0068_0000;  // 'h' = 104.0
      hello_chars[1] = 32'h0065_0000;  // 'e' = 101.0
      hello_chars[2] = 32'h006C_0000;  // 'l' = 108.0
      hello_chars[3] = 32'h006C_0000;  // 'l' = 108.0
      hello_chars[4] = 32'h006F_0000;  // 'o' = 111.0

      for (i = 0; i < 5; i = i + 1) begin
        run_soc(hello_chars[i], result);
        $display("  '%c' (%.1f) -> y_out=0x%08h (%.4f)",
                 hello_chars[i][23:16],
                 $itor(hello_chars[i]) / 65536.0,
                 result, q16_to_real(result));
      end
    end
    $display("");

    // ===================================================================
    // Summary
    // ===================================================================
    $display("================================================================");
    $display("  Results: %0d PASS, %0d FAIL", test_pass, test_fail);
    if (test_fail == 0)
      $display("  ALL TESTS PASSED — RTL matches Lean spec!");
    else
      $display("  SOME TESTS FAILED");
    $display("================================================================");

    $finish;
  end

  // Timeout watchdog
  initial begin
    #500_000;
    $display("ERROR: Simulation timeout!");
    $finish;
  end

endmodule
