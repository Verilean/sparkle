// Board wrapper for the Sparkle FULL on-chip secp256k1 signer, Tang Nano 20k.
//
// The Sparkle-generated top `signMsgDemoTop` (#writeVerilogDesign) chains the
// Keccak-256 sponge + RFC-6979 nonce + area-optimized signer, so nothing
// secret ever leaves the die: d is baked (12345), k is derived on-chip, and
// z = keccak256(message) is hashed on-chip.  Ports:
//   ._gen_uartRx  ._gen_bitDiv[15:0]  .clk  .rst  .uartTx  .signDone
// CLOCK: the RFC-6979/SHA-256 path limits Fmax to ~19 MHz, so the core runs on
// a divide-by-2 of the crystal → 13.5 MHz (timing closes with margin; the
// ~4M-cycle sign then takes ~0.3 s).  bit_div is recomputed for 13.5 MHz.
//
// Protocol: host sends 136 bytes (the Keccak-padded message preimage); device
// replies 64 bytes r‖s.  led_sign flashes on each completed signature.
module sign_msg_demo_top(
    input  clk,            // 27 MHz crystal (pin 4)
    input  rst,            // S1 button, active-low (pin 88)
    input  uart_rx_line,   // FPGA RX  (from debugger UART TX, pin 70)
    output uart_tx,        // FPGA TX  (to   debugger UART RX, pin 69)
    output led_sign        // active-low user LED (pin 15) — flashes on sign-done
);
    reg clk_div = 1'b0;
    always @(posedge clk) clk_div <= ~clk_div;   // 27 MHz -> 13.5 MHz core clock

    wire done;
    signMsgDemoTop u_core(
        .clk(clk_div),
        .rst(~rst),                 // button low = reset; core wants active-high
        ._gen_uartRx(uart_rx_line),
        ._gen_bitDiv(16'd116),      // 13.5 MHz / 115200 - 1 = 116
        .uartTx(uart_tx),
        .signDone(done)
    );

    // Active-low LED: low = lit.  `done` is a 1-cycle pulse (brief flash).
    assign led_sign = ~done;
endmodule
