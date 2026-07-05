module blinky_top(input clk, output led);
    wire [24:0] cnt;
    blinkyTop u_blink(.clk(clk), .rst(1'b0), ._gen_en(1'b1), .out(cnt));
    assign led = cnt[24];   // ~1.6 Hz toggle
endmodule
