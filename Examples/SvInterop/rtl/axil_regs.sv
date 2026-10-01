// AXI4-Lite register block, written the way such a block usually is in
// SystemVerilog.  It is here as a design that did NOT come from Sparkle:
// the examples load it with Verilator and test it with transactions.
//
//   0x00 .. 0x0C   four 32-bit read/write registers
//   0x10           read-only identification word
//   anything else  SLVERR
//
// A write address and write data are accepted independently and the write
// is performed once both have arrived.
//
// HONOR_WSTRB = 0 builds a deliberately wrong block that ignores the byte
// enables — the examples use it to show the scoreboard catching it.
module axil_regs #(
    parameter logic [31:0] ID = 32'h53504B4C,
    parameter bit          HONOR_WSTRB = 1'b1
) (
    input  logic        aclk,
    input  logic        aresetn,

    input  logic [7:0]  s_axil_awaddr,
    input  logic [2:0]  s_axil_awprot,
    input  logic        s_axil_awvalid,
    output logic        s_axil_awready,
    input  logic [31:0] s_axil_wdata,
    input  logic [3:0]  s_axil_wstrb,
    input  logic        s_axil_wvalid,
    output logic        s_axil_wready,
    output logic [1:0]  s_axil_bresp,
    output logic        s_axil_bvalid,
    input  logic        s_axil_bready,

    input  logic [7:0]  s_axil_araddr,
    input  logic [2:0]  s_axil_arprot,
    input  logic        s_axil_arvalid,
    output logic        s_axil_arready,
    output logic [31:0] s_axil_rdata,
    output logic [1:0]  s_axil_rresp,
    output logic        s_axil_rvalid,
    input  logic        s_axil_rready,

    output logic [31:0] reg0_o
);
    localparam logic [1:0] OKAY = 2'b00, SLVERR = 2'b10;

    logic [31:0] regs [4];
    logic [7:0]  aw_addr;
    logic        aw_held;
    logic [31:0] w_data;
    logic [3:0]  w_strb;
    logic        w_held;

    assign s_axil_awready = !aw_held;
    assign s_axil_wready  = !w_held;
    assign s_axil_arready = !s_axil_rvalid;
    assign reg0_o         = regs[0];

    wire do_write = aw_held && w_held && !s_axil_bvalid;
    wire [3:0] strb = HONOR_WSTRB ? w_strb : 4'hF;

    always_ff @(posedge aclk) begin
        if (!aresetn) begin
            aw_held       <= 1'b0;
            w_held        <= 1'b0;
            s_axil_bvalid <= 1'b0;
            s_axil_bresp  <= OKAY;
            s_axil_rvalid <= 1'b0;
            s_axil_rresp  <= OKAY;
            s_axil_rdata  <= '0;
            for (int i = 0; i < 4; i++) regs[i] <= '0;
        end else begin
            if (s_axil_awvalid && s_axil_awready) begin
                aw_addr <= s_axil_awaddr;
                aw_held <= 1'b1;
            end
            if (s_axil_wvalid && s_axil_wready) begin
                w_data <= s_axil_wdata;
                w_strb <= s_axil_wstrb;
                w_held <= 1'b1;
            end
            if (do_write) begin
                aw_held       <= 1'b0;
                w_held        <= 1'b0;
                s_axil_bvalid <= 1'b1;
                if (aw_addr[7:2] < 6'd4) begin
                    for (int b = 0; b < 4; b++)
                        if (strb[b]) regs[aw_addr[3:2]][8*b +: 8] <= w_data[8*b +: 8];
                    s_axil_bresp <= OKAY;
                end else begin
                    s_axil_bresp <= SLVERR;
                end
            end
            if (s_axil_bvalid && s_axil_bready) s_axil_bvalid <= 1'b0;

            if (s_axil_arvalid && s_axil_arready) begin
                s_axil_rvalid <= 1'b1;
                if (s_axil_araddr[7:2] < 6'd4) begin
                    s_axil_rdata <= regs[s_axil_araddr[3:2]];
                    s_axil_rresp <= OKAY;
                end else if (s_axil_araddr[7:2] == 6'd4) begin
                    s_axil_rdata <= ID;
                    s_axil_rresp <= OKAY;
                end else begin
                    s_axil_rdata <= '0;
                    s_axil_rresp <= SLVERR;
                end
            end else if (s_axil_rvalid && s_axil_rready) begin
                s_axil_rvalid <= 1'b0;
            end
        end
    end
endmodule
