/-
  UVM testbench generation for ready/valid designs.

  `Sparkle.Verification.Tlm` runs a transaction-level test inside Lean.
  This module writes the SAME test — same streams, same transactions, same
  expected results — as a SystemVerilog/UVM testbench around the Verilog
  that Sparkle emits, for use in a conventional verification flow:

    interface per stream            <stream>_if   (valid, ready, data)
    sequence item / sequence        <stream>_item, <stream>_seq
    driver + sequencer + monitor    for each stream INTO the DUT
    responder + monitor + scoreboard for each stream OUT OF the DUT
    env, test, and a top module that instantiates the DUT

  The expected results are computed in Lean (by the untimed model) and
  written into the test, so the scoreboard needs no SystemVerilog model.

  Timing convention of the generated components (race-free without
  clocking blocks): the testbench changes DUT inputs at the falling clock
  edge and samples `valid`/`ready` one time unit later — after the
  combinational logic has settled, before the rising edge that clocks the
  DUT.  A handshake is `valid && ready` in that sample.

  Checked with Verilator 5 and Accellera's uvm-core (`lake exe
  tlm-uvm-test` with `SPARKLE_UVM_HOME` set); no commercial simulator was
  available to try.
-/

namespace Sparkle.Verification.Tlm.Uvm

/-- One ready/valid stream, in terms of the DUT's Verilog ports. -/
structure Stream where
  name : String
  /-- payload width in bits -/
  width : Nat
  /-- true: the testbench produces the stream (a DUT input stream) -/
  toDut : Bool
  /-- `toDut`: the DUT INPUT port carrying `valid`.
      otherwise: a SystemVerilog expression over the DUT's outputs. -/
  valid : String
  /-- `toDut`: the DUT INPUT port carrying the payload.
      otherwise: an expression over the DUT's outputs. -/
  data : String
  /-- `toDut`: an expression over the DUT's outputs.
      otherwise: the DUT INPUT port carrying `ready`. -/
  ready : String

structure Bench where
  /-- prefix of every generated name -/
  name : String
  /-- Verilog module name of the DUT -/
  dutModule : String
  /-- the DUT's output ports (name, width) -/
  dutOutputs : List (String × Nat)
  /-- DUT inputs that belong to no stream: tied to 0 -/
  tiedInputs : List (String × Nat) := []
  streams : List Stream
  /-- transactions to send, per stream INTO the DUT -/
  stimulus : List (String × List Nat)
  /-- transactions expected, in order, per stream OUT OF the DUT -/
  expected : List (String × List Nat)
  /-- percentage of cycles in which the testbench is ready (back-pressure) -/
  readyPercent : Nat := 100
  maxCycles : Nat := 10000

private def hex (v : Nat) : String := String.ofList (Nat.toDigits 16 v)

private def lit (width v : Nat) : String := s!"{width}'h{hex (v % 2 ^ width)}"

private def lookup (xs : List (String × List Nat)) (n : String) : List Nat :=
  ((xs.find? (·.1 == n)).map (·.2)).getD []

/-- Interface, item and monitor: the same for both directions. -/
private def emitCommon (s : Stream) : List String :=
  [ s!"  class {s.name}_item extends uvm_sequence_item;"
  , s!"    rand bit [{s.width - 1}:0] data;"
  , s!"    `uvm_object_utils({s.name}_item)"
  , s!"    function new(string name = \"{s.name}_item\"); super.new(name); endfunction"
  , "  endclass"
  , ""
  , s!"  // observes every handshake on `{s.name}`"
  , s!"  class {s.name}_monitor extends uvm_monitor;"
  , s!"    `uvm_component_utils({s.name}_monitor)"
  , s!"    virtual {s.name}_if vif;"
  , s!"    uvm_analysis_port #({s.name}_item) ap;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , "      ap = new(\"ap\", this);"
  , s!"      if (!uvm_config_db #(virtual {s.name}_if)::get(this, \"\", \"{s.name}_vif\", vif))"
  , s!"        `uvm_fatal(\"NOVIF\", \"{s.name}_vif is not set\")"
  , "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , s!"      {s.name}_item it;"
  , "      forever begin"
  , "        @(negedge vif.clk); #1;"
  , "        if (vif.valid && vif.ready) begin"
  , s!"          it = {s.name}_item::type_id::create(\"it\");"
  , "          it.data = vif.data;"
  , "          ap.write(it);"
  , "        end"
  , "      end"
  , "    endtask"
  , "  endclass"
  , "" ]

/-- Sequence + driver for a stream the testbench produces. -/
private def emitSource (s : Stream) : List String :=
  [ s!"  class {s.name}_seq extends uvm_sequence #({s.name}_item);"
  , s!"    `uvm_object_utils({s.name}_seq)"
  , s!"    bit [{s.width - 1}:0] items[$];"
  , s!"    function new(string name = \"{s.name}_seq\"); super.new(name); endfunction"
  , "    task body();"
  , "      foreach (items[k]) begin"
  , s!"        req = {s.name}_item::type_id::create(\"req\");"
  , "        start_item(req);"
  , "        req.data = items[k];"
  , "        finish_item(req);"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , s!"  // holds `valid` and the payload until the DUT is ready"
  , s!"  class {s.name}_driver extends uvm_driver #({s.name}_item);"
  , s!"    `uvm_component_utils({s.name}_driver)"
  , s!"    virtual {s.name}_if vif;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , s!"      if (!uvm_config_db #(virtual {s.name}_if)::get(this, \"\", \"{s.name}_vif\", vif))"
  , s!"        `uvm_fatal(\"NOVIF\", \"{s.name}_vif is not set\")"
  , "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , s!"      {s.name}_item cur;"
  , "      vif.valid = 1'b0;"
  , "      vif.data = '0;"
  , "      forever begin"
  , "        @(negedge vif.clk);"
  , "        if (cur == null) seq_item_port.try_next_item(cur);"
  , "        if (cur != null) begin vif.valid = 1'b1; vif.data = cur.data; end"
  , "        else vif.valid = 1'b0;"
  , "        #1;"
  , "        if (cur != null && vif.ready) begin"
  , "          seq_item_port.item_done();"
  , "          cur = null;"
  , "        end"
  , "      end"
  , "    endtask"
  , "  endclass"
  , "" ]

/-- Responder (drives `ready`) + scoreboard for a stream the DUT produces. -/
private def emitSink (b : Bench) (s : Stream) : List String :=
  [ s!"  // the consumer side of `{s.name}`: ready in ready_percent % of cycles"
  , s!"  class {s.name}_responder extends uvm_component;"
  , s!"    `uvm_component_utils({s.name}_responder)"
  , s!"    virtual {s.name}_if vif;"
  , s!"    int unsigned ready_percent = {b.readyPercent};"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , s!"      if (!uvm_config_db #(virtual {s.name}_if)::get(this, \"\", \"{s.name}_vif\", vif))"
  , s!"        `uvm_fatal(\"NOVIF\", \"{s.name}_vif is not set\")"
  , "    endfunction"
  , "    task run_phase(uvm_phase phase);"
  , "      vif.ready = 1'b0;"
  , "      forever begin"
  , "        @(negedge vif.clk);"
  , "        vif.ready = ($urandom_range(99) < ready_percent);"
  , "      end"
  , "    endtask"
  , "  endclass"
  , ""
  , s!"  // in-order comparison against the results computed in Lean"
  , s!"  class {s.name}_scoreboard extends uvm_scoreboard;"
  , s!"    `uvm_component_utils({s.name}_scoreboard)"
  , s!"    uvm_analysis_imp #({s.name}_item, {s.name}_scoreboard) imp;"
  , s!"    bit [{s.width - 1}:0] expected[$];"
  , "    int unsigned matched = 0;"
  , "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
  , "    function void build_phase(uvm_phase phase);"
  , "      super.build_phase(phase);"
  , "      imp = new(\"imp\", this);"
  , "    endfunction"
  , s!"    function void write({s.name}_item t);"
  , s!"      bit [{s.width - 1}:0] e;"
  , "      if (expected.size() == 0)"
  , s!"        `uvm_error(\"SB\", $sformatf(\"{s.name}: unexpected transaction %0h\", t.data))"
  , "      else begin"
  , "        e = expected.pop_front();"
  , "        if (t.data !== e)"
  , s!"          `uvm_error(\"SB\", $sformatf(\"{s.name}: transaction %0d is %0h, expected %0h\", matched, t.data, e))"
  , "        else matched++;"
  , "      end"
  , "    endfunction"
  , "    function void check_phase(uvm_phase phase);"
  , "      if (expected.size() != 0)"
  , s!"        `uvm_error(\"SB\", $sformatf(\"{s.name}: %0d expected transactions never arrived\", expected.size()))"
  , "      else"
  , s!"        `uvm_info(\"SB\", $sformatf(\"SCOREBOARD PASS {s.name}: %0d transactions matched\", matched), UVM_NONE)"
  , "    endfunction"
  , "  endclass"
  , "" ]

/-- The whole testbench as one SystemVerilog file. -/
def emit (b : Bench) : String := Id.run do
  let sources := b.streams.filter (·.toDut)
  let sinks := b.streams.filter (!·.toDut)
  let mut l : List String :=
    [ s!"// AUTO-GENERATED by Sparkle HDL — UVM testbench `{b.name}` for `{b.dutModule}`"
    , "// (Sparkle.Verification.Tlm.Uvm).  Stimulus and expected results come from"
    , "// the Lean transaction-level test."
    , "`timescale 1ns/1ps"
    , "`include \"uvm_macros.svh\""
    , "" ]
  for s in b.streams do
    l := l ++
      [ s!"interface {s.name}_if (input logic clk);"
      , "  logic valid;"
      , "  logic ready;"
      , s!"  logic [{s.width - 1}:0] data;"
      , "endinterface"
      , "" ]
  l := l ++ [ s!"package {b.name}_pkg;", "  import uvm_pkg::*;", "" ]
  for s in b.streams do l := l ++ emitCommon s
  for s in sources do l := l ++ emitSource s
  for s in sinks do l := l ++ emitSink b s
  -- env
  l := l ++ [ s!"  class {b.name}_env extends uvm_env;", s!"    `uvm_component_utils({b.name}_env)" ]
  for s in b.streams do l := l ++ [ s!"    {s.name}_monitor {s.name}_mon;" ]
  for s in sources do
    l := l ++ [ s!"    {s.name}_driver {s.name}_drv;"
              , s!"    uvm_sequencer #({s.name}_item) {s.name}_sqr;" ]
  for s in sinks do
    l := l ++ [ s!"    {s.name}_responder {s.name}_rsp;", s!"    {s.name}_scoreboard {s.name}_sb;" ]
  l := l ++
    [ "    function new(string name, uvm_component parent); super.new(name, parent); endfunction"
    , "    function void build_phase(uvm_phase phase);"
    , "      super.build_phase(phase);" ]
  for s in b.streams do
    l := l ++ [ s!"      {s.name}_mon = {s.name}_monitor::type_id::create(\"{s.name}_mon\", this);" ]
  for s in sources do
    l := l ++ [ s!"      {s.name}_drv = {s.name}_driver::type_id::create(\"{s.name}_drv\", this);"
              , s!"      {s.name}_sqr = uvm_sequencer #({s.name}_item)::type_id::create(\"{s.name}_sqr\", this);" ]
  for s in sinks do
    l := l ++ [ s!"      {s.name}_rsp = {s.name}_responder::type_id::create(\"{s.name}_rsp\", this);"
              , s!"      {s.name}_sb = {s.name}_scoreboard::type_id::create(\"{s.name}_sb\", this);" ]
  l := l ++ [ "    endfunction", "    function void connect_phase(uvm_phase phase);" ]
  for s in sources do
    l := l ++ [ s!"      {s.name}_drv.seq_item_port.connect({s.name}_sqr.seq_item_export);" ]
  for s in sinks do
    l := l ++ [ s!"      {s.name}_mon.ap.connect({s.name}_sb.imp);" ]
  l := l ++ [ "    endfunction", "  endclass", "" ]
  -- test
  let clockVif := (b.streams.head?.map (·.name)).getD "none"
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
  for s in sources do l := l ++ [ s!"      {s.name}_seq {s.name}_s;" ]
  l := l ++ [ "      phase.raise_objection(this);" ]
  for s in sinks do
    for v in lookup b.expected s.name do
      l := l ++ [ s!"      env.{s.name}_sb.expected.push_back({lit s.width v});" ]
  for s in sources do
    l := l ++ [ s!"      {s.name}_s = {s.name}_seq::type_id::create(\"{s.name}_s\");" ]
    for v in lookup b.stimulus s.name do
      l := l ++ [ s!"      {s.name}_s.items.push_back({lit s.width v});" ]
  l := l ++ [ "      // out of reset before the first transaction", "      repeat (4) @(negedge clk_vif.clk);" ]
  if !sources.isEmpty then
    l := l ++ [ "      fork" ]
    for s in sources do
      l := l ++ [ s!"        {s.name}_s.start(env.{s.name}_sqr);" ]
    l := l ++ [ "      join" ]
  let pending := if sinks.isEmpty then "0"
    else String.intercalate " + " (sinks.map fun s => s!"env.{s.name}_sb.expected.size()")
  l := l ++
    [ "      // wait for every expected result, or give up"
    , s!"      while (({pending}) != 0 && cycles < {b.maxCycles}) begin"
    , "        @(negedge clk_vif.clk);"
    , "        cycles++;"
    , "      end"
    , s!"      if (cycles >= {b.maxCycles}) `uvm_error(\"TIMEOUT\", \"results did not arrive in time\")"
    , "      repeat (4) @(negedge clk_vif.clk);   // anything further is unexpected"
    , "      phase.drop_objection(this);"
    , "    endtask"
    , "  endclass"
    , ""
    , "endpackage"
    , "" ]
  -- top
  l := l ++
    [ s!"module {b.name}_top;"
    , "  import uvm_pkg::*;"
    , s!"  import {b.name}_pkg::*;"
    , "  logic clk = 1'b0;"
    , "  logic rst = 1'b1;"
    , "  always #5 clk = ~clk;"
    , "  initial begin repeat (2) @(negedge clk); rst = 1'b0; end"
    , "" ]
  for s in b.streams do l := l ++ [ s!"  {s.name}_if {s.name}_bus (clk);" ]
  for (n, w) in b.dutOutputs do l := l ++ [ s!"  wire [{w - 1}:0] {n};" ]
  let conns :=
    [ ".clk(clk)", ".rst(rst)" ]
    ++ sources.flatMap (fun s => [ s!".{s.valid}({s.name}_bus.valid)", s!".{s.data}({s.name}_bus.data)" ])
    ++ sinks.map (fun s => s!".{s.ready}({s.name}_bus.ready)")
    ++ b.tiedInputs.map (fun (n, w) => s!".{n}({w}'d0)")
    ++ b.dutOutputs.map (fun (n, _) => s!".{n}({n})")
  l := l ++ [ "", s!"  {b.dutModule} dut (" ++ String.intercalate ", " conns ++ ");", "" ]
  for s in sources do l := l ++ [ s!"  assign {s.name}_bus.ready = {s.ready};" ]
  for s in sinks do
    l := l ++ [ s!"  assign {s.name}_bus.valid = {s.valid};", s!"  assign {s.name}_bus.data = {s.data};" ]
  l := l ++ [ "", "  initial begin" ]
  for s in b.streams do
    l := l ++ [ s!"    uvm_config_db #(virtual {s.name}_if)::set(null, \"*\", \"{s.name}_vif\", {s.name}_bus);" ]
  l := l ++ [ s!"    run_test(\"{b.name}_test\");", "  end", "endmodule", "" ]
  return String.intercalate "\n" l

end Sparkle.Verification.Tlm.Uvm
