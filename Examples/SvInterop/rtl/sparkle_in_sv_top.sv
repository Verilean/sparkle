// A Sparkle module inside a SystemVerilog design.
//
//   bytes in ─▶ axis_adapter 8→32 ─▶ axis_scale ─▶ axis_adapter 32→8 ─▶ bytes out
//               (verilog-axis)       (Sparkle)      (verilog-axis)
//
// `axis_scale` is the port-name wrapper Sparkle generates around a design
// written in its Lean DSL (Tests/SvInteropTest.lean: `axisScale`); the two
// adapters are third-party Verilog.  This file is ordinary SystemVerilog and
// instantiates all three the same way.
module sparkle_in_sv_top (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] s_axis_tdata,
    input  logic       s_axis_tvalid,
    output logic       s_axis_tready,
    input  logic       s_axis_tlast,
    output logic [7:0] m_axis_tdata,
    output logic       m_axis_tvalid,
    input  logic       m_axis_tready,
    output logic       m_axis_tlast
);
    logic [31:0] a_tdata, b_tdata;
    logic [3:0]  a_tkeep, b_tkeep;
    logic        a_tvalid, a_tready, a_tlast;
    logic        b_tvalid, b_tready, b_tlast;

    axis_adapter #(
        .S_DATA_WIDTH(8), .M_DATA_WIDTH(32), .S_KEEP_ENABLE(0), .M_KEEP_ENABLE(1),
        .ID_ENABLE(0), .DEST_ENABLE(0), .USER_ENABLE(0)
    ) widen (
        .clk(clk), .rst(rst),
        .s_axis_tdata(s_axis_tdata), .s_axis_tkeep(1'b1), .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready), .s_axis_tlast(s_axis_tlast),
        .s_axis_tid('0), .s_axis_tdest('0), .s_axis_tuser('0),
        .m_axis_tdata(a_tdata), .m_axis_tkeep(a_tkeep), .m_axis_tvalid(a_tvalid),
        .m_axis_tready(a_tready), .m_axis_tlast(a_tlast),
        .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser()
    );

    axis_scale core (
        .clk(clk), .rst(rst),
        .s_axis_tdata(a_tdata), .s_axis_tkeep(a_tkeep), .s_axis_tvalid(a_tvalid),
        .s_axis_tlast(a_tlast), .s_axis_tready(a_tready),
        .m_axis_tdata(b_tdata), .m_axis_tkeep(b_tkeep), .m_axis_tvalid(b_tvalid),
        .m_axis_tlast(b_tlast), .m_axis_tready(b_tready)
    );

    axis_adapter #(
        .S_DATA_WIDTH(32), .M_DATA_WIDTH(8), .S_KEEP_ENABLE(1), .M_KEEP_ENABLE(0),
        .ID_ENABLE(0), .DEST_ENABLE(0), .USER_ENABLE(0)
    ) narrow (
        .clk(clk), .rst(rst),
        .s_axis_tdata(b_tdata), .s_axis_tkeep(b_tkeep), .s_axis_tvalid(b_tvalid),
        .s_axis_tready(b_tready), .s_axis_tlast(b_tlast),
        .s_axis_tid('0), .s_axis_tdest('0), .s_axis_tuser('0),
        .m_axis_tdata(m_axis_tdata), .m_axis_tkeep(), .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready), .m_axis_tlast(m_axis_tlast),
        .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser()
    );
endmodule
