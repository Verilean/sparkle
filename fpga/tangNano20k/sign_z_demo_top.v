// Board wrapper for the Sparkle k-on-chip secp256k1 signer, Tang Nano 20k.
//
// The Sparkle-generated top `signZDemoTop` (#writeVerilogDesign) chains the
// RFC-6979 nonce core + area-optimized signer, so the secret path stays on the
// die: d is baked (12345) and k is derived on-chip.  Ports:
//   ._gen_uartRx  ._gen_bitDiv[15:0]  .clk  .rst  .uartTx  .signDone
//
// CLOCK: a Gowin rPLL divides the 27 MHz crystal to 13.5 MHz on the global
// clock network.  This REPLACES an earlier fabric-FF ÷2 clock: a bare toggle
// flop gave 58 hold violations (2.44 ns skew), and buffering it through BUFG
// produced a DEAD clock (a fabric-FF-driven BUFG doesn't clock this part — an
// LED probe on that clk_div never toggled).  The rPLL output is a real global
// clock (an LED probe on it blinks correctly), so the core actually runs.
// fCLKOUT = 27 * (FBDIV_SEL+1)/(IDIV_SEL+1) = 27*1/2 = 13.5 MHz; VCO=864 MHz.
// The RFC-6979/SHA path is comfortable at 13.5 MHz; the ~1.3M-cycle sign
// takes ~0.1 s.  bit_div = 13.5 MHz / 115200 - 1 = 116.
//
// Protocol: host sends 32 bytes (the hash z); device replies 64 bytes r‖s.
// led_sign flashes on each completed signature (active-low).
module sign_z_demo_top(
    input  clk,            // 27 MHz crystal (pin 4)
    input  rst,            // S1 button, active-low (pin 88)
    input  uart_rx_line,   // FPGA RX  (from debugger UART TX, pin 70)
    output uart_tx,        // FPGA TX  (to   debugger UART RX, pin 69)
    output led_sign        // active-low user LED (pin 15) — flashes on sign-done
);
    // rPLL 27 MHz -> 13.5 MHz on the global clock spine.
    wire clk_div, pll_lock;
    rPLL #(
        .FCLKIN("27.0"), .DEVICE("GW2AR-18C"),
        .DYN_IDIV_SEL("false"), .IDIV_SEL(1),
        .DYN_FBDIV_SEL("false"), .FBDIV_SEL(0),
        .DYN_ODIV_SEL("false"), .ODIV_SEL(64),
        .PSDA_SEL("0000"), .DYN_DA_EN("false"), .DUTYDA_SEL("1000"),
        .CLKOUT_FT_DIR(1'b1), .CLKOUTP_FT_DIR(1'b1),
        .CLKOUT_DLY_STEP(0), .CLKOUTP_DLY_STEP(0),
        .CLKFB_SEL("internal"),
        .CLKOUT_BYPASS("false"), .CLKOUTP_BYPASS("false"), .CLKOUTD_BYPASS("false"),
        .DYN_SDIV_SEL(2), .CLKOUTD_SRC("CLKOUT"), .CLKOUTD3_SRC("CLKOUT")
    ) pll (
        .CLKOUT(clk_div), .LOCK(pll_lock),
        .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .CLKIN(clk), .CLKFB(1'b0), .RESET(1'b0), .RESET_P(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0),
        .PSDA(4'b0), .FDLY(4'b0), .DUTYDA(4'b0)
    );

    wire done;
    signZDemoTop u_core(
        .clk(clk_div),              // 13.5 MHz from the rPLL (global clock)
        .rst(~rst),                 // button low = reset; core wants active-high
        ._gen_uartRx(uart_rx_line),
        ._gen_bitDiv(16'd116),      // 13.5 MHz / 115200 - 1 = 116
        .uartTx(uart_tx),
        .signDone(done)
    );

    // Active-low LED: low = lit.  `done` is a 1-cycle pulse (brief flash).
    assign led_sign = ~done;
endmodule
