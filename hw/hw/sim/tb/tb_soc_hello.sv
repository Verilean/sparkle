`timescale 1ns / 1ps

module tb_soc_hello;

  // Clock/reset
  logic clk, rst;
  initial clk = 0;
  always #5 clk = ~clk;  // 100 MHz

  // DUT signals
  logic        start;
  logic [31:0] x_in;
  logic [31:0] y_out;
  logic        done;

  // DUT
  BitNet_SoC_TM_12L_64d u_soc (
    .clk(clk), .rst(rst), .start(start),
    .x_in(x_in), .y_out(y_out), .done(done)
  );

  // "hello" encoded as Q16.16 (ASCII << 16)
  logic [31:0] hello_chars [0:4];
  initial begin
    hello_chars[0] = 32'h00680000;  // 'h' = 0x68 = 104
    hello_chars[1] = 32'h00650000;  // 'e' = 0x65 = 101
    hello_chars[2] = 32'h006C0000;  // 'l' = 0x6C = 108
    hello_chars[3] = 32'h006C0000;  // 'l' = 0x6C = 108
    hello_chars[4] = 32'h006F0000;  // 'o' = 0x6F = 111
  end

  // Test sequence
  integer i;
  initial begin
    start = 0; x_in = 0; rst = 1;
    repeat (5) @(posedge clk);
    rst = 0;
    repeat (3) @(posedge clk);

    $display("=== Hespera End-to-End RTL Simulation ===");
    $display("Input: \"hello\" (5 chars as Q16.16)");
    $display("Architecture: TimeMultiplexed, 12 layers, dim=64");
    $display("");

    for (i = 0; i < 5; i = i + 1) begin
      // Feed character
      x_in = hello_chars[i];
      start = 1;
      @(posedge clk);
      start = 0;

      // Wait for done
      wait (done);
      @(posedge clk);

      $display("  Char[%0d] '%c': x_in=0x%08h -> y_out=0x%08h (Q16.16: %0d.%0d)",
               i, hello_chars[i][23:16],
               hello_chars[i], y_out,
               $signed(y_out) >>> 16,
               (y_out[15:0] * 1000) >> 16);

      repeat (3) @(posedge clk);
    end

    $display("");
    $display("=== Simulation Complete ===");
    $finish;
  end

  // Timeout watchdog
  initial begin
    #100_000;
    $display("ERROR: Simulation timeout!");
    $finish;
  end

endmodule
