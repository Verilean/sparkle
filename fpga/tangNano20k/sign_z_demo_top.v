// Board wrapper for the Sparkle k-on-chip secp256k1 signer, Tang Nano 20k.
//
// The Sparkle-generated top `signZDemoTop` (#writeVerilogDesign) chains the
// RFC-6979 nonce core + area-optimized signer, so the secret path stays on the
// die: d is baked (12345) and k is derived on-chip.  Ports:
//   ._gen_uartRx  ._gen_bitDiv[15:0]  .clk  .rst  .uartTx  .signDone
//
// CLOCK: the RFC-6979/SHA-256 combinational path limits Fmax to ~19.4 MHz, so
// running the core straight off the 27 MHz crystal would violate setup.  We
// divide the crystal by 2 → 13.5 MHz (well under 19.4 MHz), which closes timing
// with margin and eases place-and-route.  The ~1.3M-cycle sign then takes
// ~0.1 s — imperceptible.  bit_div is recomputed for 13.5 MHz.
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
    // Divide-by-2 clock: 27 MHz → 13.5 MHz.  A toggle flop; nextpnr promotes
    // the high-fanout result onto the global clock network.
    reg clk_div = 1'b0;
    always @(posedge clk) clk_div <= ~clk_div;

    wire done;
    signZDemoTop u_core(
        .clk(clk_div),              // 13.5 MHz core clock
        .rst(~rst),                 // button low = reset; core wants active-high
        ._gen_uartRx(uart_rx_line),
        ._gen_bitDiv(16'd116),      // 13.5 MHz / 115200 - 1 = 116
        .uartTx(uart_tx),
        .signDone(done)
    );

    // Active-low LED: low = lit.  `done` is a 1-cycle pulse (brief flash).
    assign led_sign = ~done;
endmodule
