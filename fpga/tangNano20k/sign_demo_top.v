// Board wrapper for the Sparkle secp256k1 UART signing demo, Tang Nano 20k.
//
// The Sparkle-generated top `signDemoTop` (from #writeVerilogDesign, with its
// @[hardware_module] submodules — signCtrl + opCtrl + ladderEngine + regFile +
// wMulP + wMulN + wRx + wTx + signCoreSmall) has ports
//   ._gen_uartRx  ._gen_bitDiv[15:0]  .clk  .rst  .uartTx  .signDone
// Runs in defaultDomain at the 27 MHz crystal (no PLL).  bit_div = 233
// (27 MHz / 115200 baud - 1).  The private key d is baked into the bitstream.
//
// Protocol: host sends 64 bytes  k‖z (big-endian, k first); device replies
// 64 bytes r‖s.  led_sign flashes on each completed signature (active-low).
module sign_demo_top(
    input  clk,            // 27 MHz crystal (pin 4)
    input  rst,            // S1 button, active-low (pin 88)
    input  uart_rx_line,   // FPGA RX  (from debugger UART TX, pin 70)
    output uart_tx,        // FPGA TX  (to   debugger UART RX, pin 69)
    output led_sign        // active-low user LED (pin 15) — flashes on sign-done
);
    wire done;
    signDemoTop u_core(
        .clk(clk),
        .rst(~rst),                 // button low = reset; core wants active-high
        ._gen_uartRx(uart_rx_line),
        ._gen_bitDiv(16'd233),      // 27 MHz / 115200 - 1
        .uartTx(uart_tx),
        .signDone(done)
    );

    // Active-low LED: low = lit.  `done` is a 1-cycle pulse (brief flash).
    assign led_sign = ~done;
endmodule
