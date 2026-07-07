// Proper registered UART echo (rPLL 13.5 MHz, 115200 8N1): receive a byte on
// pin 70, transmit it back on pin 69.  Tests the host->FPGA RX path (pin 70)
// with real UART logic.  LEDs blink so we know the core clock runs.
module uart_echo_top(
    input clk, input rst,
    input  uart_rx_line,     // pin 70 (FPGA RX)
    output uart_tx,          // pin 69 (FPGA TX)
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

    localparam integer DIV = 117;   // 13.5MHz/115200
    // --- RX ---
    reg [1:0] rxsync = 2'b11;
    always @(posedge clk_div) rxsync <= {rxsync[0], uart_rx_line};
    wire rxpin = rxsync[1];
    reg rx_busy=0; reg [8:0] rxdiv=0; reg [3:0] rxbit=0; reg [7:0] rxsh=0;
    reg [7:0] rx_byte=0; reg rx_valid=0;
    always @(posedge clk_div) begin
        rx_valid <= 0;
        if (!rx_busy) begin
            if (!rxpin) begin rx_busy<=1; rxdiv<=DIV+DIV/2; rxbit<=0; end // start seen; sample 1.5 bit later
        end else begin
            if (rxdiv==0) begin
                rxdiv<=DIV;
                if (rxbit==8) begin rx_busy<=0; rx_byte<=rxsh; rx_valid<=1; end
                else begin rxsh<={rxpin, rxsh[7:1]}; rxbit<=rxbit+1; end
            end else rxdiv<=rxdiv-1;
        end
    end
    // --- TX ---
    reg tx_busy=0; reg [8:0] txdiv=0; reg [3:0] txbit=0; reg [9:0] txsh=10'h3FF; reg txline=1;
    always @(posedge clk_div) begin
        if (!tx_busy) begin
            txline<=1;
            if (rx_valid) begin txsh<={1'b1,rx_byte,1'b0}; tx_busy<=1; txdiv<=DIV; txbit<=0; end
        end else begin
            txline<=txsh[0];
            if (txdiv==0) begin
                txdiv<=DIV; txsh<={1'b1,txsh[9:1]};
                if (txbit==9) tx_busy<=0; else txbit<=txbit+1;
            end else txdiv<=txdiv-1;
        end
    end
    assign uart_tx = txline;
    // heartbeat
    reg [23:0] hb=0; reg h=1;
    always @(posedge clk_div) begin if(hb==24'd6749999)begin hb<=0;h<=~h;end else hb<=hb+1; end
    assign led = {6{h}};
endmodule
