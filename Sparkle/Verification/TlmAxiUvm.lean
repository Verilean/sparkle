/-
  UVM environments for AXI4-Lite and AXI4-Stream interfaces, generated from
  the same definitions the Lean agents use.

  Given a design (its ports, as `Sv.Dut` read them) and the PREFIXES of its
  buses, this writes a complete SystemVerilog/UVM testbench in the shape of
  the UVM User's Guide, ch. 3:

    <prefix>_if            interface with the bus signals
    <prefix>_item          sequence item — the TRANSACTION
                             AXI4-Lite: write, addr, data, strb, resp
                             AXI4-Stream: tdata (bytes), tid, tdest, tuser
    <prefix>_seq           directed sequence: the items the Lean test used
    <prefix>_driver        get_next_item / drive_item / item_done
    <prefix>_monitor       pins → items, published on an analysis port
    <prefix>_responder     (stream out of the design) drives tready
    <prefix>_scoreboard    analysis subscriber: items against the list the
                           Lean run produced, in order
    <name>_env, <name>_test, <name>_top

  Signal names, widths and which optional signals exist are taken from the
  design's port list — nothing about the bus is typed in again.  The
  expected transactions are what the Lean monitor reported for the same
  sequence, so a UVM run and a Lean run of one test must agree transaction
  for transaction.

  Timing convention (as in `TlmUvm.lean`): drive at the falling clock edge,
  sample one time unit later.  No clocking blocks, no DPI.

  Checked with Verilator 5 and Accellera's uvm-core (`lake exe
  tlm-uvm-test`); no commercial simulator was available.
-/
import Sparkle.Verification.TlmAxi

namespace Sparkle.Verification.Tlm.Uvm

open Sparkle.Core.Sim

structure AxiBench where
  /-- prefix of the generated env / test / top -/
  name : String
  /-- how the design is built: top module, clock, reset, parameters -/
  config : Sv.Config
  /-- the design's ports, without clock and reset (`Sv.Dut.inputs/outputs`) -/
  inputs : List Sv.Port
  outputs : List Sv.Port
  /-- AXI4-Lite slave interfaces of the design: prefix, the accesses to
      issue, the transactions the monitor must report -/
  axil : List (String × List AxiLiteTxn × List AxiLiteTxn) := []
  /-- AXI4-Stream inputs of the design: prefix, frames to send -/
  axisIn : List (String × List AxiStreamFrame) := []
  /-- AXI4-Stream outputs of the design: prefix, frames expected -/
  axisOut : List (String × List AxiStreamFrame) := []
  /-- percentage of cycles in which a stream consumer is ready -/
  readyPercent : Nat := 100
  maxCycles : Nat := 20000

def AxiBench.ofDut (name : String) (config : Sv.Config) (dut : Sv.Dut) : AxiBench :=
  { name, config, inputs := dut.inputs.toList, outputs := dut.outputs.toList }

private def hexs (v : Nat) : String := String.ofList (Nat.toDigits 16 v)
private def lit (width v : Nat) : String := s!"{width}'h{hexs (v % 2 ^ width)}"
private def rng (w : Nat) : String := if w ≤ 1 then "" else s!"[{w - 1}:0] "

private def width? (b : AxiBench) (name : String) : Option Nat :=
  ((b.inputs ++ b.outputs).find? (·.name == name)).map (·.width)

/-- Signals of one bus: (suffix, width in the interface, present on the design). -/
private def busSignals (b : AxiBench) (pfx : String) (spec : List (String × Nat)) :
    List (String × Nat × Bool) :=
  spec.map fun (sfx, dflt) =>
    match width? b s!"{pfx}_{sfx}" with
    | some w => (sfx, w, true)
    | none => (sfx, dflt, false)

private def axilSpec (aw dw : Nat) : List (String × Nat) :=
  [ ("awaddr", aw), ("awprot", 3), ("awvalid", 1), ("awready", 1)
  , ("wdata", dw), ("wstrb", dw / 8), ("wvalid", 1), ("wready", 1)
  , ("bresp", 2), ("bvalid", 1), ("bready", 1)
  , ("araddr", aw), ("arprot", 3), ("arvalid", 1), ("arready", 1)
  , ("rdata", dw), ("rresp", 2), ("rvalid", 1), ("rready", 1) ]

private def axisSpec (dw : Nat) : List (String × Nat) :=
  [ ("tdata", dw), ("tkeep", dw / 8), ("tvalid", 1), ("tready", 1), ("tlast", 1)
  , ("tid", 8), ("tdest", 8), ("tuser", 1) ]

private def emitInterface (pfx : String) (sigs : List (String × Nat × Bool)) : List String :=
  -- handshake signals are scalars; everything else keeps its range even at
  -- one bit (the components index `tkeep[j]`, `tdata[8*j +: 8]`)
  let scalar (sfx : String) : Bool := sfx.endsWith "valid" || sfx.endsWith "ready" || sfx == "tlast"
  [ s!"interface {pfx}_if (input logic clk);" ]
  ++ sigs.map (fun (sfx, w, _) =>
      if scalar sfx then s!"  logic {sfx};" else s!"  logic [{w - 1}:0] {sfx};")
  ++ [ "endinterface", "" ]

private def vifGet (pfx : String) : List String :=
  [ s!"      if (!uvm_config_db #(virtual {pfx}_if)::get(this, \"\", \"{pfx}_vif\", vif))"
  , s!"        `uvm_fatal(\"NOVIF\", \"{pfx}_vif is not set\")" ]

/-- Item, sequence, driver, monitor and scoreboard of an AXI4-Lite master. -/
private def emitAxil (pfx : String) (aw dw : Nat) : List String :=
  let sw := dw / 8
  [ s!"  // ── AXI4-Lite `{pfx}` ─────────────────────────────────────────────"
  , s!"  class {pfx}_item extends uvm_sequence_item;"
  , "    rand bit write;"
  , s!"    rand bit [{aw - 1}:0] addr;"
  , s!"    rand bit [{dw - 1}:0] data;"
  , s!"    rand bit [{sw - 1}:0] strb;"
  , "    bit [1:0] resp;"
  , s!"    `uvm_object_utils({pfx}_item)"
  , s!"    function new(string name = \"{pfx}_item\"); super.new(name); endfunction"
  , "    function string convert2string();"
  , "      return write ? $sformatf(\"WRITE %0h := %0h strb %0h resp %0d\", addr, data, strb, resp)"
  , "                   : $sformatf(\"READ %0h = %0h resp %0d\", addr, data, resp);"
  , "    endfunction"
  , "  endclass"
  , ""
  , s!"  class {pfx}_seq extends uvm_sequence #({pfx}_item);"
  , s!"    `uvm_object_utils({pfx}_seq)"
  , s!"    {pfx}_item items[$];"
  , s!"    function new(string name = \"{pfx}_seq\"); super.new(name); endfunction"
  , "    function void add(bit write, longint unsigned addr, longint unsigned data, int unsigned strb);"
  , s!"      {pfx}_item it = {pfx}_item::type_id::create(\"it\");"
  , "      it.write = write; it.addr = addr; it.data = data; it.strb = strb;"
  , "      items.push_back(it);"
  , "    endfunction"
  , "    task body();"
  , "      foreach (items[k]) begin"
  , "        start_item(items[k]);"
  , "        finish_item(items[k]);"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , "  // one access at a time: address and data together, then the response"
  , s!"  class {pfx}_driver extends uvm_driver #({pfx}_item);"
  , s!"    `uvm_component_utils({pfx}_driver)"
  , s!"    virtual {pfx}_if vif;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);" ]
  ++ vifGet pfx ++
  [ "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , "      vif.awvalid = 1'b0; vif.wvalid = 1'b0; vif.arvalid = 1'b0;"
  , "      vif.bready = 1'b0; vif.rready = 1'b0;"
  , "      vif.awaddr = '0; vif.awprot = '0; vif.wdata = '0; vif.wstrb = '0;"
  , "      vif.araddr = '0; vif.arprot = '0;"
  , "      forever begin"
  , "        seq_item_port.get_next_item(req);"
  , "        drive_item(req);"
  , "        seq_item_port.item_done();"
  , "      end"
  , "    endtask"
  , s!"    task drive_item({pfx}_item it);"
  , "      bit aw_done = 1'b0;"
  , "      bit w_done = 1'b0;"
  , "      if (it.write) begin"
  , "        @(negedge vif.clk);"
  , "        vif.awaddr = it.addr; vif.awvalid = 1'b1;"
  , "        vif.wdata = it.data; vif.wstrb = it.strb; vif.wvalid = 1'b1;"
  , "        while (!(aw_done && w_done)) begin"
  , "          #1;"
  , "          if (vif.awvalid && vif.awready) aw_done = 1'b1;"
  , "          if (vif.wvalid && vif.wready) w_done = 1'b1;"
  , "          @(negedge vif.clk);"
  , "          if (aw_done) vif.awvalid = 1'b0;"
  , "          if (w_done) vif.wvalid = 1'b0;"
  , "        end"
  , "        vif.bready = 1'b1;"
  , "        forever begin #1; if (vif.bvalid) break; @(negedge vif.clk); end"
  , "        it.resp = vif.bresp;"
  , "        @(negedge vif.clk);"
  , "        vif.bready = 1'b0;"
  , "      end else begin"
  , "        @(negedge vif.clk);"
  , "        vif.araddr = it.addr; vif.arvalid = 1'b1;"
  , "        forever begin #1; if (vif.arready) break; @(negedge vif.clk); end"
  , "        @(negedge vif.clk);"
  , "        vif.arvalid = 1'b0; vif.rready = 1'b1;"
  , "        forever begin #1; if (vif.rvalid) break; @(negedge vif.clk); end"
  , "        it.data = vif.rdata; it.resp = vif.rresp;"
  , "        @(negedge vif.clk);"
  , "        vif.rready = 1'b0;"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , "  // five channels in, one item per completed access out"
  , s!"  class {pfx}_monitor extends uvm_monitor;"
  , s!"    `uvm_component_utils({pfx}_monitor)"
  , s!"    virtual {pfx}_if vif;"
  , s!"    uvm_analysis_port #({pfx}_item) ap;"
  , s!"    bit [{aw - 1}:0] awq[$];"
  , s!"    bit [{dw - 1}:0] wq[$];"
  , s!"    bit [{sw - 1}:0] sq[$];"
  , s!"    bit [{aw - 1}:0] arq[$];"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , "      ap = new(\"ap\", this);" ]
  ++ vifGet pfx ++
  [ "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , s!"      {pfx}_item it;"
  , "      forever begin"
  , "        @(negedge vif.clk); #1;"
  , "        if (vif.awvalid && vif.awready) awq.push_back(vif.awaddr);"
  , "        if (vif.wvalid && vif.wready) begin wq.push_back(vif.wdata); sq.push_back(vif.wstrb); end"
  , "        if (vif.arvalid && vif.arready) arq.push_back(vif.araddr);"
  , "        if (vif.bvalid && vif.bready) begin"
  , "          if (awq.size() == 0 || wq.size() == 0)"
  , s!"            `uvm_error(\"MON\", \"{pfx}: write response without a completed address and data transfer\")"
  , "          else begin"
  , s!"            it = {pfx}_item::type_id::create(\"it\");"
  , "            it.write = 1'b1; it.addr = awq.pop_front(); it.data = wq.pop_front();"
  , "            it.strb = sq.pop_front(); it.resp = vif.bresp;"
  , "            ap.write(it);"
  , "          end"
  , "        end"
  , "        if (vif.rvalid && vif.rready) begin"
  , "          if (arq.size() == 0)"
  , s!"            `uvm_error(\"MON\", \"{pfx}: read data without a read address\")"
  , "          else begin"
  , s!"            it = {pfx}_item::type_id::create(\"it\");"
  , "            it.write = 1'b0; it.addr = arq.pop_front(); it.data = vif.rdata;"
  , "            it.strb = '1; it.resp = vif.rresp;"
  , "            ap.write(it);"
  , "          end"
  , "        end"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , "  // in-order comparison against the transactions the Lean monitor reported"
  , s!"  class {pfx}_scoreboard extends uvm_scoreboard;"
  , s!"    `uvm_component_utils({pfx}_scoreboard)"
  , s!"    uvm_analysis_imp #({pfx}_item, {pfx}_scoreboard) imp;"
  , s!"    {pfx}_item expected[$];"
  , "    int unsigned matched = 0;"
  , "    int unsigned wrong = 0;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , "      imp = new(\"imp\", this);"
  , "    endfunction"
  , "    function void expect_item(bit write, longint unsigned addr, longint unsigned data, int unsigned strb, int unsigned resp);"
  , s!"      {pfx}_item it = {pfx}_item::type_id::create(\"e\");"
  , "      it.write = write; it.addr = addr; it.data = data; it.strb = strb; it.resp = resp;"
  , "      expected.push_back(it);"
  , "    endfunction"
  , s!"    function void write({pfx}_item t);"
  , s!"      {pfx}_item e;"
  , "      if (expected.size() == 0) begin"
  , "        wrong++;"
  , s!"        `uvm_error(\"SB\", $sformatf(\"{pfx}: unexpected transaction %s\", t.convert2string()))"
  , "      end else begin"
  , "        e = expected.pop_front();"
  , "        if (t.write !== e.write || t.addr !== e.addr || t.data !== e.data || t.strb !== e.strb || t.resp !== e.resp) begin"
  , "          wrong++;"
  , s!"          `uvm_error(\"SB\", $sformatf(\"{pfx}: transaction %0d is %s, expected %s\", matched + wrong - 1, t.convert2string(), e.convert2string()))"
  , "        end else matched++;"
  , "      end"
  , "    endfunction"
  , "    function void check_phase(uvm_phase phase);"
  , "      if (expected.size() != 0)"
  , s!"        `uvm_error(\"SB\", $sformatf(\"{pfx}: %0d expected transactions never arrived\", expected.size()))"
  , "      else if (wrong != 0)"
  , s!"        `uvm_info(\"SB\", $sformatf(\"SCOREBOARD FAIL {pfx}: %0d transactions wrong, %0d matched\", wrong, matched), UVM_NONE)"
  , "      else"
  , s!"        `uvm_info(\"SB\", $sformatf(\"SCOREBOARD PASS {pfx}: %0d transactions matched\", matched), UVM_NONE)"
  , "    endfunction"
  , "  endclass"
  , "" ]

/-- Item and monitor of an AXI4-Stream bus (both directions). -/
private def emitAxisCommon (pfx : String) (dw : Nat) : List String :=
  let n := dw / 8
  [ s!"  // ── AXI4-Stream `{pfx}` ───────────────────────────────────────────"
  , "  // one item = one frame"
  , s!"  class {pfx}_item extends uvm_sequence_item;"
  , "    byte unsigned tdata[$];"
  , "    int unsigned tid;"
  , "    int unsigned tdest;"
  , "    int unsigned tuser;"
  , s!"    `uvm_object_utils({pfx}_item)"
  , s!"    function new(string name = \"{pfx}_item\"); super.new(name); endfunction"
  , "    function string convert2string();"
  , "      string s = $sformatf(\"%0d bytes [\", tdata.size());"
  , "      foreach (tdata[k]) s = {s, $sformatf(\"%02h\", tdata[k])};"
  , "      return {s, $sformatf(\"] tid %0d tdest %0d tuser %0d\", tid, tdest, tuser)};"
  , "    endfunction"
  , s!"    function bit same({pfx}_item o);"
  , "      if (tdata.size() != o.tdata.size() || tid != o.tid || tdest != o.tdest || tuser != o.tuser) return 1'b0;"
  , "      foreach (tdata[k]) if (tdata[k] != o.tdata[k]) return 1'b0;"
  , "      return 1'b1;"
  , "    endfunction"
  , "  endclass"
  , ""
  , "  // transfers in, frames out"
  , s!"  class {pfx}_monitor extends uvm_monitor;"
  , s!"    `uvm_component_utils({pfx}_monitor)"
  , s!"    virtual {pfx}_if vif;"
  , s!"    uvm_analysis_port #({pfx}_item) ap;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , "      ap = new(\"ap\", this);" ]
  ++ vifGet pfx ++
  [ "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , s!"      {pfx}_item it;"
  , "      byte unsigned acc[$];"
  , "      forever begin"
  , "        @(negedge vif.clk); #1;"
  , "        if (vif.tvalid && vif.tready) begin"
  , s!"          for (int j = 0; j < {n}; j++)"
  , "            if (vif.tkeep[j]) acc.push_back(vif.tdata[8*j +: 8]);"
  , "          if (vif.tlast) begin"
  , s!"            it = {pfx}_item::type_id::create(\"it\");"
  , "            it.tdata = acc; it.tid = vif.tid; it.tdest = vif.tdest; it.tuser = vif.tuser;"
  , "            ap.write(it);"
  , "            acc.delete();"
  , "          end"
  , "        end"
  , "      end"
  , "    endtask"
  , "  endclass"
  , "" ]

private def emitAxisSource (pfx : String) (dw : Nat) : List String :=
  let n := dw / 8
  [ s!"  class {pfx}_seq extends uvm_sequence #({pfx}_item);"
  , s!"    `uvm_object_utils({pfx}_seq)"
  , s!"    {pfx}_item items[$];"
  , s!"    function new(string name = \"{pfx}_seq\"); super.new(name); endfunction"
  , "    task body();"
  , "      foreach (items[k]) begin"
  , "        start_item(items[k]);"
  , "        finish_item(items[k]);"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , "  // a frame as transfers: bytes low lane first, tkeep on a partial last one"
  , s!"  class {pfx}_driver extends uvm_driver #({pfx}_item);"
  , s!"    `uvm_component_utils({pfx}_driver)"
  , s!"    virtual {pfx}_if vif;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);" ]
  ++ vifGet pfx ++
  [ "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , "      vif.tvalid = 1'b0; vif.tdata = '0; vif.tkeep = '0; vif.tlast = 1'b0;"
  , "      vif.tid = '0; vif.tdest = '0; vif.tuser = '0;"
  , "      forever begin"
  , "        seq_item_port.get_next_item(req);"
  , "        drive_item(req);"
  , "        seq_item_port.item_done();"
  , "      end"
  , "    endtask"
  , s!"    task drive_item({pfx}_item it);"
  , "      int unsigned total = it.tdata.size();"
  , s!"      int unsigned beats = (total + {n} - 1) / {n};"
  , "      for (int unsigned b = 0; b < beats; b++) begin"
  , s!"        bit [{dw - 1}:0] d = '0;"
  , s!"        bit [{n - 1}:0] k = '0;"
  , s!"        for (int unsigned j = 0; j < {n} && b * {n} + j < total; j++) begin"
  , s!"          d[8*j +: 8] = it.tdata[b * {n} + j];"
  , "          k[j] = 1'b1;"
  , "        end"
  , "        @(negedge vif.clk);"
  , "        vif.tdata = d; vif.tkeep = k; vif.tlast = (b == beats - 1);"
  , "        vif.tid = it.tid; vif.tdest = it.tdest; vif.tuser = it.tuser; vif.tvalid = 1'b1;"
  , "        forever begin #1; if (vif.tready) break; @(negedge vif.clk); end"
  , "      end"
  , "      @(negedge vif.clk);"
  , "      vif.tvalid = 1'b0;"
  , "    endtask"
  , "  endclass"
  , "" ]

private def emitAxisSink (b : AxiBench) (pfx : String) : List String :=
  [ s!"  // the consumer side of `{pfx}`: tready in ready_percent % of cycles"
  , s!"  class {pfx}_responder extends uvm_component;"
  , s!"    `uvm_component_utils({pfx}_responder)"
  , s!"    virtual {pfx}_if vif;"
  , s!"    int unsigned ready_percent = {b.readyPercent};"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);" ]
  ++ vifGet pfx ++
  [ "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , "      vif.tready = 1'b0;"
  , "      forever begin"
  , "        @(negedge vif.clk);"
  , "        vif.tready = ($urandom_range(99) < ready_percent);"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , "  // in-order comparison against the frames the Lean run produced"
  , s!"  class {pfx}_scoreboard extends uvm_scoreboard;"
  , s!"    `uvm_component_utils({pfx}_scoreboard)"
  , s!"    uvm_analysis_imp #({pfx}_item, {pfx}_scoreboard) imp;"
  , s!"    {pfx}_item expected[$];"
  , "    int unsigned matched = 0;"
  , "    int unsigned wrong = 0;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , "      imp = new(\"imp\", this);"
  , "    endfunction"
  , s!"    function void write({pfx}_item t);"
  , s!"      {pfx}_item e;"
  , "      if (expected.size() == 0) begin"
  , "        wrong++;"
  , s!"        `uvm_error(\"SB\", $sformatf(\"{pfx}: unexpected frame %s\", t.convert2string()))"
  , "      end else begin"
  , "        e = expected.pop_front();"
  , "        if (!t.same(e)) begin"
  , "          wrong++;"
  , s!"          `uvm_error(\"SB\", $sformatf(\"{pfx}: frame %0d is %s, expected %s\", matched + wrong - 1, t.convert2string(), e.convert2string()))"
  , "        end else matched++;"
  , "      end"
  , "    endfunction"
  , "    function void check_phase(uvm_phase phase);"
  , "      if (expected.size() != 0)"
  , s!"        `uvm_error(\"SB\", $sformatf(\"{pfx}: %0d expected frames never arrived\", expected.size()))"
  , "      else if (wrong != 0)"
  , s!"        `uvm_info(\"SB\", $sformatf(\"SCOREBOARD FAIL {pfx}: %0d frames wrong, %0d matched\", wrong, matched), UVM_NONE)"
  , "      else"
  , s!"        `uvm_info(\"SB\", $sformatf(\"SCOREBOARD PASS {pfx}: %0d transactions matched\", matched), UVM_NONE)"
  , "    endfunction"
  , "  endclass"
  , "" ]

/-- SystemVerilog statements that build one frame item in `var`. -/
private def frameLines (indent pfx var : String) (f : AxiStreamFrame) : List String :=
  [ s!"{indent}{var} = {pfx}_item::type_id::create(\"{var}\");"
  , s!"{indent}{var}.tid = {f.tid}; {var}.tdest = {f.tdest}; {var}.tuser = {f.tuser};" ]
  ++ f.tdata.toList.map (fun byte => s!"{indent}{var}.tdata.push_back(8'h{hexs byte.toNat});")

/-- The whole testbench as one SystemVerilog file. -/
def emitAxi (b : AxiBench) : Except String String := do
  let need (pfx sfx : String) : Except String Nat :=
    match width? b s!"{pfx}_{sfx}" with
    | some w => pure w
    | none => throw s!"UVM {b.name}: design '{b.config.top}' has no signal '{pfx}_{sfx}'"
  -- bus shapes, from the design
  let mut axils : List (String × Nat × Nat × List (String × Nat × Bool)) := []
  for (pfx, _, _) in b.axil do
    let aw ← need pfx "awaddr"
    let dw ← need pfx "wdata"
    axils := axils ++ [(pfx, aw, dw, busSignals b pfx (axilSpec aw dw))]
  let mut streams : List (String × Nat × Bool × List (String × Nat × Bool)) := []   -- prefix, width, toDut
  for (pfx, _) in b.axisIn do
    let dw ← need pfx "tdata"
    streams := streams ++ [(pfx, dw, true, busSignals b pfx (axisSpec dw))]
  for (pfx, _) in b.axisOut do
    let dw ← need pfx "tdata"
    streams := streams ++ [(pfx, dw, false, busSignals b pfx (axisSpec dw))]
  let allPrefixes := axils.map (·.1) ++ streams.map (·.1)
  if allPrefixes.isEmpty then throw s!"UVM {b.name}: no bus was given"
  let mut l : List String :=
    [ s!"// AUTO-GENERATED by Sparkle HDL — UVM testbench `{b.name}` for `{b.config.top}`"
    , "// (Sparkle.Verification.Tlm.Uvm.emitAxi).  Bus shapes are read from the"
    , "// design; sequences and expected transactions come from the Lean test."
    , "`timescale 1ns/1ps"
    , "`include \"uvm_macros.svh\""
    , "" ]
  for (pfx, _, _, sigs) in axils do l := l ++ emitInterface pfx sigs
  for (pfx, _, _, sigs) in streams do l := l ++ emitInterface pfx sigs
  l := l ++ [ s!"package {b.name}_pkg;", "  import uvm_pkg::*;", "" ]
  for (pfx, aw, dw, _) in axils do l := l ++ emitAxil pfx aw dw
  for (pfx, dw, toDut, _) in streams do
    l := l ++ emitAxisCommon pfx dw
    l := l ++ (if toDut then emitAxisSource pfx dw else emitAxisSink b pfx)
  let drivers := axils.map (·.1) ++ (streams.filter (·.2.2.1)).map (·.1)
  let checked := axils.map (·.1) ++ (streams.filter (!·.2.2.1)).map (·.1)
  -- a stream out of the design gets a responder only if the design has tready
  let sinks := (streams.filter fun (_, _, toDut, sigs) =>
    !toDut && sigs.any fun (sfx, _, present) => sfx == "tready" && present).map (·.1)
  -- env
  l := l ++ [ s!"  class {b.name}_env extends uvm_env;", s!"    `uvm_component_utils({b.name}_env)" ]
  for p in allPrefixes do l := l ++ [ s!"    {p}_monitor {p}_mon;" ]
  for p in drivers do
    l := l ++ [ s!"    {p}_driver {p}_drv;", s!"    uvm_sequencer #({p}_item) {p}_sqr;" ]
  for p in sinks do l := l ++ [ s!"    {p}_responder {p}_rsp;" ]
  for p in checked do l := l ++ [ s!"    {p}_scoreboard {p}_sb;" ]
  l := l ++
    [ "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
    , "    function void build_phase(uvm_phase phase);"
    , "      super.build_phase(phase);" ]
  for p in allPrefixes do
    l := l ++ [ s!"      {p}_mon = {p}_monitor::type_id::create(\"{p}_mon\", this);" ]
  for p in drivers do
    l := l ++ [ s!"      {p}_drv = {p}_driver::type_id::create(\"{p}_drv\", this);"
              , s!"      {p}_sqr = uvm_sequencer #({p}_item)::type_id::create(\"{p}_sqr\", this);" ]
  for p in sinks do
    l := l ++ [ s!"      {p}_rsp = {p}_responder::type_id::create(\"{p}_rsp\", this);" ]
  for p in checked do
    l := l ++ [ s!"      {p}_sb = {p}_scoreboard::type_id::create(\"{p}_sb\", this);" ]
  l := l ++ [ "    endfunction", "    function void connect_phase(uvm_phase phase);" ]
  for p in drivers do
    l := l ++ [ s!"      {p}_drv.seq_item_port.connect({p}_sqr.seq_item_export);" ]
  for p in checked do
    l := l ++ [ s!"      {p}_mon.ap.connect({p}_sb.imp);" ]
  l := l ++ [ "    endfunction", "  endclass", "" ]
  -- test
  let clockVif := allPrefixes.headD "none"
  l := l ++
    [ s!"  class {b.name}_test extends uvm_test;"
    , s!"    `uvm_component_utils({b.name}_test)"
    , s!"    {b.name}_env env;"
    , s!"    virtual {clockVif}_if clk_vif;"
    , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
    , "    function void build_phase(uvm_phase phase);"
    , "      super.build_phase(phase);"
    , s!"      env = {b.name}_env::type_id::create(\"env\", this);"
    , s!"      if (!uvm_config_db #(virtual {clockVif}_if)::get(this, \"\", \"{clockVif}_vif\", clk_vif))"
    , s!"        `uvm_fatal(\"NOVIF\", \"{clockVif}_vif is not set\")"
    , "    endfunction"
    , "    task run_phase(uvm_phase phase);"
    , "      int unsigned cycles = 0;" ]
  for p in drivers do l := l ++ [ s!"      {p}_seq {p}_s;" ]
  for (p, _, _, _) in streams do l := l ++ [ s!"      {p}_item {p}_f;" ]
  l := l ++ [ "      phase.raise_objection(this);" ]
  for (pfx, sequence, expected) in b.axil do
    for t in expected do
      l := l ++ [ s!"      env.{pfx}_sb.expect_item({if t.write then 1 else 0}, 64'h{hexs t.addr}, 64'h{hexs t.data}, 'h{hexs t.strb}, {t.resp.toBits});" ]
    l := l ++ [ s!"      {pfx}_s = {pfx}_seq::type_id::create(\"{pfx}_s\");" ]
    for t in sequence do
      l := l ++ [ s!"      {pfx}_s.add({if t.write then 1 else 0}, 64'h{hexs t.addr}, 64'h{hexs t.data}, 'h{hexs t.strb});" ]
  for (pfx, fs) in b.axisOut do
    for f in fs do
      l := l ++ frameLines "      " pfx s!"{pfx}_f" f ++ [ s!"      env.{pfx}_sb.expected.push_back({pfx}_f);" ]
  for (pfx, fs) in b.axisIn do
    l := l ++ [ s!"      {pfx}_s = {pfx}_seq::type_id::create(\"{pfx}_s\");" ]
    for f in fs do
      l := l ++ frameLines "      " pfx s!"{pfx}_f" f ++ [ s!"      {pfx}_s.items.push_back({pfx}_f);" ]
  l := l ++ [ "      // out of reset before the first transaction", "      repeat (6) @(negedge clk_vif.clk);" ]
  if !drivers.isEmpty then
    l := l ++ [ "      fork" ]
    for p in drivers do l := l ++ [ s!"        {p}_s.start(env.{p}_sqr);" ]
    l := l ++ [ "      join" ]
  let pending := if checked.isEmpty then "0"
    else String.intercalate " + " (checked.map fun p => s!"env.{p}_sb.expected.size()")
  l := l ++
    [ "      // wait for every expected transaction, or give up"
    , s!"      while (({pending}) != 0 && cycles < {b.maxCycles}) begin"
    , "        @(negedge clk_vif.clk);"
    , "        cycles++;"
    , "      end"
    , s!"      if (cycles >= {b.maxCycles}) `uvm_error(\"TIMEOUT\", \"transactions did not arrive in time\")"
    , "      repeat (4) @(negedge clk_vif.clk);   // anything further is unexpected"
    , "      phase.drop_objection(this);"
    , "    endtask"
    , "  endclass"
    , ""
    , "endpackage"
    , "" ]
  -- top
  let rstActive := if b.config.resetActiveHigh then "1'b1" else "1'b0"
  let rstIdle := if b.config.resetActiveHigh then "1'b0" else "1'b1"
  l := l ++
    [ s!"module {b.name}_top;"
    , "  import uvm_pkg::*;"
    , s!"  import {b.name}_pkg::*;"
    , "  logic clk = 1'b0;"
    , s!"  logic rst = {rstActive};"
    , "  always #5 clk = ~clk;"
    , s!"  initial begin repeat (3) @(negedge clk); rst = {rstIdle}; end"
    , "" ]
  for p in allPrefixes do l := l ++ [ s!"  {p}_if {p}_bus (clk);" ]
  -- every port of the design: a bus signal, tied low, or left open
  let busOf (port : String) : Option (String × String) :=
    allPrefixes.findSome? fun p =>
      if port.startsWith (p ++ "_") then some (p, (port.drop (p.length + 1)).toString) else none
  let known (p sfx : String) : Bool :=
    (axils.any fun (q, _, _, sigs) => q == p && sigs.any (·.1 == sfx)) ||
    (streams.any fun (q, _, _, sigs) => q == p && sigs.any (·.1 == sfx))
  let conn (port : Sv.Port) : String :=
    match busOf port.name with
    | some (p, sfx) =>
      if known p sfx then s!".{port.name}({p}_bus.{sfx})"
      else if port.isInput then s!".{port.name}('0)" else s!".{port.name}()"
    | none => if port.isInput then s!".{port.name}('0)" else s!".{port.name}()"
  let conns := [ s!".{b.config.clock}(clk)" ]
    ++ (match b.config.reset with | some r => [ s!".{r}(rst)" ] | none => [])
    ++ (b.inputs ++ b.outputs).map conn
  let params := if b.config.params.isEmpty then ""
    else " #(" ++ String.intercalate ", " (b.config.params.map fun (n, v) => s!".{n}({v})") ++ ")"
  l := l ++ [ "", s!"  {b.config.top}{params} dut (" ++ String.intercalate ", " conns ++ ");", "" ]
  -- optional signals the design does not have
  for (p, _, _, sigs) in axils do
    for (sfx, _, present) in sigs do
      if !present && (sfx == "bresp" || sfx == "rresp") then
        l := l ++ [ s!"  assign {p}_bus.{sfx} = 2'b00;" ]
  for (p, _, toDut, sigs) in streams do
    for (sfx, _, present) in sigs do
      if !present then
        if sfx == "tready" then l := l ++ [ s!"  assign {p}_bus.tready = 1'b1;" ]
        else if !toDut && sfx == "tkeep" then l := l ++ [ s!"  assign {p}_bus.tkeep = '1;" ]
        else if !toDut && sfx == "tlast" then l := l ++ [ s!"  assign {p}_bus.tlast = 1'b1;" ]
        else if !toDut && (sfx == "tid" || sfx == "tdest" || sfx == "tuser") then
          l := l ++ [ s!"  assign {p}_bus.{sfx} = '0;" ]
  l := l ++ [ "", "  initial begin" ]
  for p in allPrefixes do
    l := l ++ [ s!"    uvm_config_db #(virtual {p}_if)::set(null, \"*\", \"{p}_vif\", {p}_bus);" ]
  l := l ++ [ s!"    run_test(\"{b.name}_test\");", "  end", "endmodule", "" ]
  return String.intercalate "\n" l

end Sparkle.Verification.Tlm.Uvm
