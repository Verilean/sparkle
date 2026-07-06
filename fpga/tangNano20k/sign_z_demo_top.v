// Board wrapper for the Sparkle k-on-chip (RFC-6979 nonce; z sent by host) secp256k1 signer, Tang Nano 20k.
//
// The Sparkle-generated top `signZDemoTop` (#writeVerilogDesign) chains the
// Keccak-256 sponge + RFC-6979 nonce + area-optimized signer, so nothing
// secret ever leaves the die: d is baked (12345), k is derived on-chip, and
// z = keccak256(message) is hashed on-chip.  Ports:
//   ._gen_uartRx  ._gen_bitDiv[15:0]  .clk  .rst  .uartTx  .signDone
// defaultDomain @ the 27 MHz crystal (no PLL).  bit_div = 233 (27MHz/115200-1).
//
// Protocol: host sends 32 bytes (the hash z)); device
// replies 64 bytes r‖s.  led_sign flashes on each completed signature.
module sign_z_demo_top(
    input  clk,            // 27 MHz crystal (pin 4)
    input  rst,            // S1 button, active-low (pin 88)
    input  uart_rx_line,   // FPGA RX  (from debugger UART TX, pin 70)
    output uart_tx,        // FPGA TX  (to   debugger UART RX, pin 69)
    output led_sign        // active-low user LED (pin 15) — flashes on sign-done
);
    wire done;
    signZDemoTop u_core(
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
