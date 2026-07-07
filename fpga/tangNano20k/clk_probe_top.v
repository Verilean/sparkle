// Dual-clock probe #2 for the Tang Nano 20k — validates a Gowin rPLL as the
// replacement for the (dead) BUFG-÷2 clock.  A fabric-FF→BUFG clock proved
// dead on this part; an rPLL output is a real global clock, so it should work.
//
//   led[2:0] (pins 15,16,17): counter on the RAW 27 MHz crystal.
//       toggle every 27,000,000 -> SLOW blink, 2.0 s period (reference).
//   led[5:3] (pins 18,19,20): counter on the rPLL CLKOUT (27→13.5 MHz).
//       toggle every 6,750,000 -> FAST blink, 1.0 s period (if rPLL=13.5 MHz).
//
//   BOTH groups blink -> rPLL works; use it for sign_z's core clock.
//   Only the SLOW group blinks (rPLL group dark) -> rPLL config wrong / no lock.
module clk_probe_top(
    input  clk,            // 27 MHz crystal (pin 4)
    input  rst,            // S1 (pin 88), unused
    output [5:0] led       // pins 15..20, active-low
);
    // --- group A: raw 27 MHz crystal (reference) -------------------------
    reg [24:0] cnt_a = 25'd0;
    reg a = 1'b1;
    always @(posedge clk) begin
        if (cnt_a == 25'd26_999_999) begin cnt_a <= 25'd0; a <= ~a; end
        else cnt_a <= cnt_a + 25'd1;
    end

    // --- group B: rPLL 27 MHz -> 13.5 MHz --------------------------------
    // fCLKOUT = 27 * (FBDIV_SEL+1)/(IDIV_SEL+1) = 27*1/2 = 13.5 MHz
    // fVCO    = 13.5 * ODIV_SEL(64) = 864 MHz  (in 400-1200 range)
    wire pll_clk, pll_lock;
    rPLL #(
        .FCLKIN("27.0"),
        .DEVICE("GW2AR-18C"),
        .DYN_IDIV_SEL("false"), .IDIV_SEL(1),
        .DYN_FBDIV_SEL("false"), .FBDIV_SEL(0),
        .DYN_ODIV_SEL("false"), .ODIV_SEL(64),
        .PSDA_SEL("0000"), .DYN_DA_EN("false"), .DUTYDA_SEL("1000"),
        .CLKOUT_FT_DIR(1'b1), .CLKOUTP_FT_DIR(1'b1),
        .CLKOUT_DLY_STEP(0), .CLKOUTP_DLY_STEP(0),
        .CLKFB_SEL("internal"),
        .CLKOUT_BYPASS("false"), .CLKOUTP_BYPASS("false"), .CLKOUTD_BYPASS("false"),
        .DYN_SDIV_SEL(2), .CLKOUTD_SRC("CLKOUT"), .CLKOUTD3_SRC("CLKOUT")
    ) pll (
        .CLKOUT(pll_clk), .LOCK(pll_lock),
        .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .CLKIN(clk), .CLKFB(1'b0),
        .RESET(1'b0), .RESET_P(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0),
        .PSDA(4'b0), .FDLY(4'b0), .DUTYDA(4'b0)
    );

    reg [23:0] cnt_b = 24'd0;
    reg b = 1'b1;
    always @(posedge pll_clk) begin
        if (cnt_b == 24'd6_749_999) begin cnt_b <= 24'd0; b <= ~b; end
        else cnt_b <= cnt_b + 24'd1;
    end

    assign led = {b, b, b, a, a, a};   // led[5:3]=B(rPLL), led[2:0]=A(raw clk)
endmodule
