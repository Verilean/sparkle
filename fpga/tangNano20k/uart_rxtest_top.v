// RX test: TX continuously alternates 0x55 and the last byte received on RX.
//   read stream = 55 00 55 00 ...  -> port alive, TX works, no RX yet
//   send 0xAB, stream -> 55 AB 55 AB -> RX (pin 70) WORKS
//   stream stays 55 00 after sending -> RX broken ; nothing at all -> port dead
module uart_rxtest_top(input clk, input rst, input uart_rx_line, output uart_tx, output [5:0] led);
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
    // RX on pin 70
    reg [1:0] rxsync = 2'b11; always @(posedge clk_div) rxsync <= {rxsync[0], uart_rx_line};
    wire rxpin = rxsync[1];
    reg rx_busy=1'b0; reg [9:0] rxdiv=10'd0; reg [3:0] rxbit=4'd0; reg [7:0] rxsh=8'd0; reg [7:0] lastrx=8'h00;
    always @(posedge clk_div) begin
        if (!rx_busy) begin if (!rxpin) begin rx_busy<=1'b1; rxdiv<=DIV+DIV/2; rxbit<=4'd0; end end
        else if (rxdiv==10'd0) begin rxdiv<=DIV[9:0];
            if (rxbit==4'd8) begin rx_busy<=1'b0; lastrx<=rxsh; end
            else begin rxsh<={rxpin,rxsh[7:1]}; rxbit<=rxbit+4'd1; end
        end else rxdiv<=rxdiv-10'd1;
    end
    // TX: alternate 0x55, lastrx
    reg [8:0] bcnt=9'd0; wire tick=(bcnt==DIV[8:0]-9'd1); always @(posedge clk_div) bcnt<=tick?9'd0:bcnt+9'd1;
    reg which=1'b0; reg [3:0] bitidx=4'd0; reg txl=1'b1;
    wire [7:0] curbyte = which ? lastrx : 8'h55;
    wire [9:0] frame = {1'b1, curbyte, 1'b0};
    always @(posedge clk_div) if (tick) begin
        txl <= frame[bitidx];
        if (bitidx==4'd9) begin bitidx<=4'd0; which<=~which; end else bitidx<=bitidx+4'd1;
    end
    assign uart_tx = txl;
    reg [23:0] hb=24'd0; reg h=1'b1; always @(posedge clk_div) begin if(hb==24'd6749999)begin hb<=24'd0;h<=~h;end else hb<=hb+24'd1; end
    assign led = {6{h}};
endmodule
