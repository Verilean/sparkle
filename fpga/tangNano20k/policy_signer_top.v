// Board wrapper for the Sparkle policy-enforcing Ethereum signer,
// targeting the Sipeed Tang Nano 20k (GW2AR-18).
//
// The Sparkle-generated top `gen_policyTx` (emitted by #writeVerilogDesign
// along with its 12 @[hardware_module] submodules — Keccak sponge +
// secp256k1 signer + UART) has ports
//   ._gen_uartRx  ._gen_bitDiv[15:0]  .clk  .rst  .out
// It runs in `defaultDomain` at the board's 27 MHz crystal, so no PLL is
// needed. We hardcode bit_div = 233 (27 MHz / 115200 baud - 1), invert the
// active-low reset button, and rename `out` -> `uart_tx` to match the .cst.
//
// The on-chip policy still bites without the LEDs: the host driver reads a
// 0xEE reject byte over UART. The two user LEDs are cosmetic and, on the
// Tang Nano 20k, ACTIVE-LOW, so we tie them off high (unlit).

module policy_signer_top(
    input  clk,             // 27 MHz crystal (pin 4)
    input  rst,             // S1 button, active-low (pin 88)
    input  uart_rx_line,    // FPGA RX  (from debugger UART TX, pin 70)
    output uart_tx,         // FPGA TX  (to   debugger UART RX, pin 69)
    output led_sign,        // active-low user LED (pin 15) — tied off
    output led_reject       // active-low user LED (pin 16) — tied off
);
    gen_policyTx u_core(
        .clk(clk),
        .rst(~rst),                 // button low = reset; core wants active-high
        ._gen_uartRx(uart_rx_line),
        ._gen_bitDiv(16'd233),      // 27 MHz / 115200 - 1
        .out(uart_tx)
    );

    // Active-low LEDs: high = off.
    assign led_sign   = 1'b1;
    assign led_reject = 1'b1;
endmodule
