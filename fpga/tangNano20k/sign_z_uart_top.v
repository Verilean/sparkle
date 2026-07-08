// Interactive UART secp256k1 signer for the Tang Nano 20k, built from three
// individually hardware-proven blocks: a hand-written UART RX (rxtest), the real
// signZSmallDemo core, and the rotate-register UART TX (self-test).  Host sends
// a 32-byte z (big-endian) on pin 70 (RX); the device signs with baked d=12345
// and on-chip RFC-6979 k, then streams the 64-byte r‖s out pin 69 (TX) in a
// continuous rotate loop until the next z arrives.  rPLL 13.5 MHz clock, 115200.
//   led[2:0]=heartbeat (running), led[5:3]=have (signature ready).
module sign_z_uart_top(
    input  clk, input rst,
    input  uart_rx_line,     // pin 70
    output uart_tx,          // pin 69
    output [5:0] led
);
    wire clk_div, lock;
    rPLL #(.FCLKIN("27.0"),.DEVICE("GW2AR-18C"),.DYN_IDIV_SEL("false"),.IDIV_SEL(1),
        .DYN_FBDIV_SEL("false"),.FBDIV_SEL(0),.DYN_ODIV_SEL("false"),.ODIV_SEL(64),
        .PSDA_SEL("0000"),.DYN_DA_EN("false"),.DUTYDA_SEL("1000"),.CLKOUT_FT_DIR(1'b1),
        .CLKOUTP_FT_DIR(1'b1),.CLKOUT_DLY_STEP(0),.CLKOUTP_DLY_STEP(0),.CLKFB_SEL("internal"),
        .CLKOUT_BYPASS("false"),.CLKOUTP_BYPASS("false"),.CLKOUTD_BYPASS("false"),
        .DYN_SDIV_SEL(2),.CLKOUTD_SRC("CLKOUT"),.CLKOUTD3_SRC("CLKOUT")
    ) pll (.CLKOUT(clk_div),.LOCK(lock),.CLKOUTP(),.CLKOUTD(),.CLKOUTD3(),.CLKIN(clk),
        .CLKFB(1'b0),.RESET(1'b0),.RESET_P(1'b0),.FBDSEL(6'b0),.IDSEL(6'b0),.ODSEL(6'b0),
        .PSDA(4'b0),.FDLY(4'b0),.DUTYDA(4'b0));
    localparam integer DIV = 117;

    reg [9:0] rc=10'd0; reg crst=1'b1;
    always @(posedge clk_div) begin if (rc!=10'd1023) rc<=rc+10'd1; crst<=(rc<10'd300); end

    // --- UART RX: collect 32 bytes (MSB-first) into z_reg, pulse start ---
    reg [1:0] rxsync=2'b11; always @(posedge clk_div) rxsync<={rxsync[0],uart_rx_line};
    wire rxpin=rxsync[1];
    reg rx_busy=1'b0; reg [9:0] rxdiv=10'd0; reg [3:0] rxbit=4'd0; reg [7:0] rxsh=8'd0;
    reg [255:0] zsr=256'd0; reg [5:0] bytecnt=6'd0;
    reg start_p=1'b0; reg [255:0] z_reg=256'd0;
    always @(posedge clk_div) begin
        start_p <= 1'b0;
        if (crst) begin rx_busy<=1'b0; bytecnt<=6'd0; end
        else if (!rx_busy) begin
            if (!rxpin) begin rx_busy<=1'b1; rxdiv<=DIV+DIV/2; rxbit<=4'd0; end
        end else if (rxdiv==10'd0) begin
            rxdiv<=DIV[9:0];
            if (rxbit==4'd8) begin
                rx_busy<=1'b0;
                zsr <= {zsr[247:0], rxsh};
                if (bytecnt==6'd31) begin
                    bytecnt<=6'd0; z_reg<={zsr[247:0], rxsh}; start_p<=1'b1;
                end else bytecnt<=bytecnt+6'd1;
            end else begin rxsh<={rxpin, rxsh[7:1]}; rxbit<=rxbit+4'd1; end
        end else rxdiv<=rxdiv-10'd1;
    end

    // --- signer core ---
    wire [255:0] rOut, sOut; wire done;
    Sparkle_IP_Crypto_EcdsaSignMsgSmall_signZSmallDemo core(
        .clk(clk_div), .rst(crst), ._gen_start(start_p), ._gen_z(z_reg),
        .rOut(rOut), .sOut(sOut), .done(done));

    // --- latch r‖s; a new sign (start_p) clears have ---
    reg [511:0] rs=512'd0; reg have=1'b0;
    always @(posedge clk_div) begin
        if (start_p) have<=1'b0;
        else if (done && !have) begin rs<={rOut,sOut}; have<=1'b1; end
    end

    // --- UART TX: rotate-stream r‖s while have; re-arm on new sign ---
    reg [8:0] bcnt=9'd0; wire tick=(bcnt==DIV[8:0]-9'd1);
    always @(posedge clk_div) bcnt<=tick?9'd0:bcnt+9'd1;
    reg [511:0] txsr=512'd0; reg loaded=1'b0; reg [3:0] bitidx=4'd0; reg txl=1'b1;
    wire [9:0] frame={1'b1, txsr[511:504], 1'b0};
    always @(posedge clk_div) begin
        if (start_p) loaded<=1'b0;
        if (!loaded) begin
            txl<=1'b1;
            if (have) begin txsr<=rs; loaded<=1'b1; bitidx<=4'd0; end
        end else if (tick) begin
            txl<=frame[bitidx];
            if (bitidx==4'd9) begin bitidx<=4'd0; txsr<={txsr[503:0], txsr[511:504]}; end
            else bitidx<=bitidx+4'd1;
        end
    end
    assign uart_tx=txl;

    reg [23:0] hb=24'd0; reg h=1'b1;
    always @(posedge clk_div) begin if(hb==24'd6749999)begin hb<=24'd0;h<=~h;end else hb<=hb+24'd1; end
    assign led={~have,~have,~have,h,h,h};
endmodule
