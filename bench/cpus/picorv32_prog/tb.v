// Program-level check: PicoRV32 (default parameters) with a 4 KiB RAM
// running fw.hex.  Prints one line per completed bus transaction; the
// original and the round-tripped core must print the same trace.
`timescale 1ns/1ps
module prog_tb;
  reg clk = 0;
  reg resetn = 0;
  wire trap, mem_valid, mem_instr;
  reg mem_ready = 0;
  wire [31:0] mem_addr, mem_wdata;
  wire [3:0] mem_wstrb;
  reg [31:0] mem_rdata = 0;
  picorv32 dut (.clk(clk), .resetn(resetn), .trap(trap),
    .mem_valid(mem_valid), .mem_instr(mem_instr), .mem_ready(mem_ready),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_wstrb(mem_wstrb),
    .mem_rdata(mem_rdata),
    .pcpi_wr(1'b0), .pcpi_rd(32'b0), .pcpi_wait(1'b0), .pcpi_ready(1'b0),
    .irq(32'b0));
  reg [31:0] memory [0:1023];
  wire [9:0] idx = mem_addr[11:2];
  integer i, cycles = 0;
  initial begin
    for (i = 0; i < 1024; i = i + 1) memory[i] = 32'h0;
    $readmemh("fw.hex", memory);
    repeat (4) @(posedge clk);
    resetn <= 1;
  end
  always #5 clk = ~clk;
  always @(posedge clk) begin
    cycles <= cycles + 1;
    mem_ready <= 0;
    if (resetn && mem_valid && !mem_ready) begin
      mem_ready <= 1;
      mem_rdata <= memory[idx];
      if (mem_wstrb[0]) memory[idx][7:0]   <= mem_wdata[7:0];
      if (mem_wstrb[1]) memory[idx][15:8]  <= mem_wdata[15:8];
      if (mem_wstrb[2]) memory[idx][23:16] <= mem_wdata[23:16];
      if (mem_wstrb[3]) memory[idx][31:24] <= mem_wdata[31:24];
      if (mem_wstrb != 0)
        $display("W %0d %h %b %h", cycles, mem_addr, mem_wstrb, mem_wdata);
      else
        $display("R %0d %h %b %h", cycles, mem_addr, mem_instr, memory[idx]);
    end
    if (resetn && trap) begin
      $display("TRAP %0d", cycles);
      $finish;
    end
    if (cycles > 20000) begin
      $display("TIMEOUT");
      $finish;
    end
  end
endmodule
