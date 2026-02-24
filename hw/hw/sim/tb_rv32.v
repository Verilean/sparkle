// ============================================================================
// Verilog Testbench for the Sparkle-generated RV32I SoC
//
// - Loads firmware via $readmemh into instruction memory
// - Clocks the SoC and monitors execution
// - Detects UART writes (store to 0x10000000) and prints values
// - Detects halt (PC stuck in a tight loop) and terminates
//
// Usage:
//   iverilog -g2012 -o tb_rv32 tb_rv32.v ../gen/rv32i_soc.sv ../gen/rv32i_core.sv
//   vvp tb_rv32 +firmware=../../firmware/firmware.hex
// ============================================================================

`timescale 1ns / 1ps

module tb_rv32;

    // -----------------------------------------------------------------------
    // Parameters
    // -----------------------------------------------------------------------
    parameter CLK_PERIOD  = 10;           // 100 MHz
    parameter MAX_CYCLES  = 100000;       // Timeout
    parameter UART_ADDR   = 32'h10000000; // UART TX data register

    // -----------------------------------------------------------------------
    // Signals
    // -----------------------------------------------------------------------
    reg         clk;
    reg         rst;
    wire [31:0] debug_pc;

    // Cycle counter
    integer cycle_count;

    // Halt detection
    reg [31:0] prev_pc;
    reg [31:0] prev_prev_pc;
    integer    halt_counter;

    // Test result tracking
    integer test_pass;

    // -----------------------------------------------------------------------
    // Clock generation
    // -----------------------------------------------------------------------
    initial clk = 0;
    always #(CLK_PERIOD / 2) clk = ~clk;

    // -----------------------------------------------------------------------
    // DUT instantiation
    // -----------------------------------------------------------------------
    RV32I_SoC dut (
        .clk      (clk),
        .rst      (rst),
        .debug_pc (debug_pc)
    );

    // -----------------------------------------------------------------------
    // Firmware loading
    // -----------------------------------------------------------------------
    reg [1023:0] firmware_path;

    initial begin
        // Get firmware hex path from command line or use default
        if (!$value$plusargs("firmware=%s", firmware_path)) begin
            firmware_path = "../../../firmware/firmware.hex";
        end

        // Load firmware into instruction memory BRAM
        // Sparkle-generated memory array name: _gen_imem_19
        $readmemh(firmware_path, dut._gen_imem_19);

        $display("============================================================");
        $display(" RV32I SoC Testbench (Sparkle-generated)");
        $display(" Firmware: %0s", firmware_path);
        $display("============================================================");
    end

    // -----------------------------------------------------------------------
    // Reset sequence
    // -----------------------------------------------------------------------
    initial begin
        rst = 1;
        #(CLK_PERIOD * 5);   // Hold reset for 5 cycles
        @(posedge clk);
        rst = 0;
        $display("[%0t] Reset released", $time);
    end

    // -----------------------------------------------------------------------
    // UART write monitor (watches bus_addr and dmem_we)
    // -----------------------------------------------------------------------
    // Sparkle-generated signal names:
    //   bus_addr   = dut._gen_bus_addr_23
    //   dmem_we    = dut._gen_core_dmem_we_3
    //   dmem_wdata = dut._gen_core_dmem_wdata_2
    wire [31:0] bus_addr_mon   = dut._gen_bus_addr_23;
    wire        bus_we_mon     = dut._gen_core_dmem_we_3;
    wire [31:0] bus_wdata_mon  = dut._gen_core_dmem_wdata_2;

    always @(posedge clk) begin
        if (!rst && bus_we_mon && bus_addr_mon == UART_ADDR) begin
            $display("[UART @ cycle %0d] 0x%08h  (%0d)",
                     cycle_count, bus_wdata_mon, bus_wdata_mon);

            // Detect test markers
            case (bus_wdata_mon)
                32'hDEAD0001: $display(">>> Test suite START");
                32'hAAAA0001: $display(">>> Test 1: Fibonacci");
                32'hAAAA0002: $display(">>> Test 2: Array Sum");
                32'hAAAA0003: $display(">>> Test 3: Bubble Sort");
                32'hAAAA0004: $display(">>> Test 4: GCD");
                32'hAAAA0005: $display(">>> Test 5: CSR Read/Write");
                32'hAAAA0006: $display(">>> Test 6: ECALL Trap");
                32'hAAAA0007: $display(">>> Test 7: Timer Interrupt");
                32'hCAFE0000: begin
                    $display("============================================================");
                    $display("*** ALL TESTS PASSED ***");
                    $display("============================================================");
                    test_pass = 1;
                end
                32'hDEADDEAD: begin
                    $display("============================================================");
                    $display("*** SOME TESTS FAILED ***");
                    $display("============================================================");
                    test_pass = 0;
                end
            endcase
        end
    end

    // -----------------------------------------------------------------------
    // Main simulation loop
    // -----------------------------------------------------------------------
    initial begin
        // Optional VCD dump (enable with -DVCD)
        `ifdef VCD
        $dumpfile("tb_rv32.vcd");
        $dumpvars(0, tb_rv32);
        `endif

        cycle_count  = 0;
        halt_counter = 0;
        prev_pc      = 32'hFFFFFFFF;
        prev_prev_pc = 32'hFFFFFFFE;
        test_pass    = -1;  // -1 = not yet determined

        // Wait for reset release
        @(negedge rst);
        @(posedge clk);

        // Run simulation
        while (cycle_count < MAX_CYCLES) begin
            @(posedge clk);
            cycle_count = cycle_count + 1;

            // ---- PC trace (every 1000 cycles) ----
            if (cycle_count % 1000 == 0) begin
                $display("[cycle %0d] PC = 0x%08h", cycle_count, debug_pc);
            end

            // ---- Halt detection ----
            if (debug_pc == prev_pc) begin
                halt_counter = halt_counter + 1;
            end else begin
                halt_counter = 0;
            end

            prev_prev_pc = prev_pc;
            prev_pc      = debug_pc;

            if (halt_counter >= 10) begin
                $display("");
                $display("[cycle %0d] HALT detected: PC stuck at 0x%08h",
                         cycle_count, debug_pc);
                $display("============================================================");
                $display(" Simulation complete: %0d cycles", cycle_count);
                if (test_pass == 1)
                    $display(" Result: PASS");
                else if (test_pass == 0)
                    $display(" Result: FAIL");
                else
                    $display(" Result: UNKNOWN (no test marker seen)");
                $display("============================================================");
                $finish;
            end
        end

        // Timeout
        $display("");
        $display("[cycle %0d] TIMEOUT: simulation exceeded %0d cycles",
                 cycle_count, MAX_CYCLES);
        $display(" Last PC = 0x%08h", debug_pc);
        $display("============================================================");
        $finish;
    end

    // -----------------------------------------------------------------------
    // Verbose PC trace (enable with -DVERBOSE)
    // -----------------------------------------------------------------------
    `ifdef VERBOSE
    always @(posedge clk) begin
        if (!rst && debug_pc !== prev_pc) begin
            $display("[cycle %5d] PC = 0x%08h", cycle_count, debug_pc);
        end
    end
    `endif

    // -----------------------------------------------------------------------
    // Debug trace for first N cycles (enable with -DDEBUG_EARLY)
    // -----------------------------------------------------------------------
    `ifdef DEBUG_EARLY
    always @(posedge clk) begin
        if (!rst && cycle_count < 50) begin
            $display("[cycle %3d] PC=0x%08h inst=0x%08h alu_a=0x%08h alu_b=0x%08h alu_r=0x%08h wb_en=%b wb_rd=%0d wb_data=0x%08h stall=%b flush=%b",
                     cycle_count, debug_pc,
                     dut.core._gen_ifid_inst_17,
                     dut.core._gen_alu_a_152,
                     dut.core._gen_alu_b_153,
                     dut.core._gen_alu_result_176,
                     dut.core._gen_wr_en_fwd_7,
                     dut.core._gen_wr_addr_fwd_5,
                     dut.core._gen_wr_data_fwd_6,
                     dut.core._gen_stall_4,
                     dut.core._gen_flush_3);
        end
    end
    `endif

    // -----------------------------------------------------------------------
    // DMEM trace for bubble sort debug (enable with -DDEBUG_DMEM)
    // -----------------------------------------------------------------------
    `ifdef DEBUG_DMEM
    always @(posedge clk) begin
        #1;
        if (!rst && cycle_count >= 236 && cycle_count <= 260) begin
            $display("[cycle %3d] PC=0x%08h idex_pc=0x%08h memW=%b memR=%b alu_r=0x%08h rs2=0x%08h stall=%b flush=%b flushD=%b sqsh=%b wb_en=%b wb_rd=%0d wb_data=0x%08h",
                     cycle_count, debug_pc,
                     dut.core._gen_idex_pc_142,
                     dut.core._gen_idex_mem_write_110,
                     dut.core._gen_idex_mem_read_108,
                     dut.core._gen_alu_result_176,
                     dut.core._gen_ex_rs2_fwd_151,
                     dut.core._gen_stall_4,
                     dut.core._gen_flush_3,
                     dut.core._gen_flush_delay_8,
                     dut.core._gen_idex_squash_102,
                     dut.core._gen_wr_en_fwd_7,
                     dut.core._gen_wr_addr_fwd_5,
                     dut.core._gen_wr_data_fwd_6);
        end
    end
    `endif

endmodule
