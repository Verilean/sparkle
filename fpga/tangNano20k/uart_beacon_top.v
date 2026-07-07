// UART TX beacon for the Tang Nano 20k — tests whether the FPGA can transmit
// to the host over the on-board debugger UART (i.e. whether pin 69 is really
// the debugger's UART-RX).  Continuously transmits 0x55 ('U') at 115200 8N1
// using an rPLL 13.5 MHz clock, and blinks all LEDs so we know it's alive.
//
// Read the host port WITHOUT sending anything:
//   stream of 'U' (0x55) arrives  -> FPGA→host works; pin 69 is the debugger RX.
//   nothing arrives               -> pin 69 is NOT the path (wrong pin, or the
//                                    debugger doesn't forward FPGA TX).
module uart_beacon_top(
    input  clk,            // 27 MHz crystal (pin 4)
    input  rst,            // S1 (pin 88), unused
    output uart_tx,        // pin 69 (candidate: debugger UART-RX)
    output [5:0] led       // pins 15..20, heartbeat
);
    // rPLL 27 -> 13.5 MHz.
    wire clk_div, pll_lock;
    rPLL #(
        .FCLKIN("27.0"), .DEVICE("GW2AR-18C"),
        .DYN_IDIV_SEL("false"), .IDIV_SEL(1),
        .DYN_FBDIV_SEL("false"), .FBDIV_SEL(0),
        .DYN_ODIV_SEL("false"), .ODIV_SEL(64),
        .PSDA_SEL("0000"), .DYN_DA_EN("false"), .DUTYDA_SEL("1000"),
        .CLKOUT_FT_DIR(1'b1), .CLKOUTP_FT_DIR(1'b1),
        .CLKOUT_DLY_STEP(0), .CLKOUTP_DLY_STEP(0), .CLKFB_SEL("internal"),
        .CLKOUT_BYPASS("false"), .CLKOUTP_BYPASS("false"), .CLKOUTD_BYPASS("false"),
        .DYN_SDIV_SEL(2), .CLKOUTD_SRC("CLKOUT"), .CLKOUTD3_SRC("CLKOUT")
    ) pll (
        .CLKOUT(clk_div), .LOCK(pll_lock), .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .CLKIN(clk), .CLKFB(1'b0), .RESET(1'b0), .RESET_P(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0), .PSDA(4'b0), .FDLY(4'b0), .DUTYDA(4'b0)
    );

    // 115200 baud at 13.5 MHz -> 117 clk_div cycles/bit.
    localparam [7:0] DIV = 8'd116;   // 117-1
    reg [7:0] bcnt = 8'd0;
    wire tick = (bcnt == DIV);
    always @(posedge clk_div) bcnt <= tick ? 8'd0 : bcnt + 8'd1;

    // Frame for 0x55, LSB-first: start(0),1,0,1,0,1,0,1,0,stop(1) = 10'b1010101010.
    localparam [9:0] FRAME = 10'b1010101010;
    reg [3:0] bit_i = 4'd0;
    reg tx_r = 1'b1;                 // idle high
    always @(posedge clk_div) if (tick) begin
        tx_r  <= FRAME[bit_i];
        bit_i <= (bit_i == 4'd9) ? 4'd0 : bit_i + 4'd1;   // back-to-back frames
    end
    assign uart_tx = tx_r;

    // heartbeat: all LEDs blink ~1 s period (toggle every 6.75M clk_div cycles).
    reg [23:0] hb = 24'd0;
    reg hbled = 1'b1;
    always @(posedge clk_div) begin
        if (hb == 24'd6_749_999) begin hb <= 24'd0; hbled <= ~hbled; end
        else hb <= hb + 24'd1;
    end
    assign led = {6{hbled}};
endmodule
