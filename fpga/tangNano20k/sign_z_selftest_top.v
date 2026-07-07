// Self-signing hardware demo for the Tang Nano 20k.  Bakes z=123456789, runs
// the real signZSmallDemo core (rPLL 13.5 MHz), then continuously streams the
// 64-byte r‖s out pin 69 at 115200 (no gap; host slides a 64-byte window and
// verifies).  Needs only the working FPGA→host direction.
//   led[2:0] (15,16,17): heartbeat blink  -> design is RUNNING (clock alive).
//   led[5:3] (18,19,20): steady lit once the signature is ready (have=1).
module sign_z_selftest_top(
    input  clk, input rst,
    output uart_tx,          // pin 69
    output [5:0] led
);
    wire clk_div, lock;
    rPLL #(.FCLKIN("27.0"),.DEVICE("GW2AR-18C"),
        .DYN_IDIV_SEL("false"),.IDIV_SEL(1),.DYN_FBDIV_SEL("false"),.FBDIV_SEL(0),
        .DYN_ODIV_SEL("false"),.ODIV_SEL(64),.PSDA_SEL("0000"),.DYN_DA_EN("false"),
        .DUTYDA_SEL("1000"),.CLKOUT_FT_DIR(1'b1),.CLKOUTP_FT_DIR(1'b1),
        .CLKOUT_DLY_STEP(0),.CLKOUTP_DLY_STEP(0),.CLKFB_SEL("internal"),
        .CLKOUT_BYPASS("false"),.CLKOUTP_BYPASS("false"),.CLKOUTD_BYPASS("false"),
        .DYN_SDIV_SEL(2),.CLKOUTD_SRC("CLKOUT"),.CLKOUTD3_SRC("CLKOUT")
    ) pll (.CLKOUT(clk_div),.LOCK(lock),.CLKOUTP(),.CLKOUTD(),.CLKOUTD3(),
        .CLKIN(clk),.CLKFB(1'b0),.RESET(1'b0),.RESET_P(1'b0),
        .FBDSEL(6'b0),.IDSEL(6'b0),.ODSEL(6'b0),.PSDA(4'b0),.FDLY(4'b0),.DUTYDA(4'b0));

    // startup reset + one-shot start.
    reg [9:0] rc = 10'd0; reg crst = 1'b1;
    always @(posedge clk_div) begin
        if (rc != 10'd1023) rc <= rc + 10'd1;
        crst <= (rc < 10'd300);
    end
    reg started = 1'b0, start_p = 1'b0;
    always @(posedge clk_div) begin
        start_p <= 1'b0;
        if (!crst && !started) begin start_p <= 1'b1; started <= 1'b1; end
    end

    localparam [255:0] Z = 256'd123456789;
    wire [255:0] rOut, sOut; wire done;
    Sparkle_IP_Crypto_EcdsaSignMsgSmall_signZSmallDemo core(
        .clk(clk_div), .rst(crst), ._gen_start(start_p), ._gen_z(Z),
        .rOut(rOut), .sOut(sOut), .done(done));

    reg [511:0] rs = 512'd0; reg have = 1'b0;
    always @(posedge clk_div) if (done && !have) begin rs <= {rOut, sOut}; have <= 1'b1; end

    // --- UART TX: rotate a 512-bit copy of r‖s, always send the TOP byte
    // (fixed slice, no variable part-select).  Continuous loop; host slides a
    // 64-byte window to find the r-start alignment.
    localparam [8:0] DIV = 9'd116;   // 117-1
    reg [8:0] bcnt = 9'd0;
    wire tick = (bcnt == DIV);
    always @(posedge clk_div) bcnt <= tick ? 9'd0 : bcnt + 9'd1;

    reg [511:0] txsr = 512'd0;
    reg loaded = 1'b0;
    reg [3:0] bitidx = 4'd0;
    reg txl = 1'b1;
    wire [9:0] frame = {1'b1, txsr[511:504], 1'b0};  // stop, top byte (LSB-first), start
    always @(posedge clk_div) begin
        if (!loaded) begin
            if (have) begin txsr <= rs; loaded <= 1'b1; bitidx <= 4'd0; end
        end else if (tick) begin
            txl <= frame[bitidx];
            if (bitidx == 4'd9) begin
                bitidx <= 4'd0;
                txsr   <= {txsr[503:0], txsr[511:504]};  // rotate top byte to bottom
            end else bitidx <= bitidx + 4'd1;
        end
    end
    assign uart_tx = txl;

    // --- LEDs ---
    reg [23:0] hb = 24'd0; reg hbled = 1'b1;
    always @(posedge clk_div) begin
        if (hb == 24'd6_749_999) begin hb <= 24'd0; hbled <= ~hbled; end
        else hb <= hb + 24'd1;
    end
    assign led = {~have, ~have, ~have, hbled, hbled, hbled};  // [5:3]=have, [2:0]=heartbeat
endmodule
